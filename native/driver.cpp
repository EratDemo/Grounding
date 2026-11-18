// SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
// SPDX-License-Identifier: Apache-2.0
#include "driver.h"

#include <lean/lean.h>

#include <algorithm>
#include <cstddef>
#include <cstdio>
#include <exception>
#include <memory>
#include <mutex>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "backend_builder.h"
#include "diag.h"
#include "slang/ast/ASTContext.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang_frontend.h"

namespace grounding {

using namespace slang_frontend;

// Everything needed to evaluate expressions after the netlist has been
// emitted. The declaration order matters: members are destroyed in reverse
// order, so `netlist` (and the child contexts in `hqueue`) die before the
// compilation, which dies before the driver that owns the source manager.
struct SvState
{
	SynthesisSettings settings;
	slang::driver::Driver driver;
	std::unique_ptr<slang::ast::Compilation> compilation;
	std::vector<const slang::ast::InstanceSymbol *> tops;
	std::unique_ptr<HierarchyQueue> hqueue;
	std::unique_ptr<NetlistContext> netlist;
	std::mutex mutex;
};

namespace {

std::span<const slang::Diagnostic> diagnostics_span(const slang::Diagnostics &diags)
{
	return {diags.data(), diags.size()};
}

bool has_errors(std::span<const slang::Diagnostic> diags)
{
	return std::any_of(diags.begin(), diags.end(), [](const auto &diag) { return diag.isError(); });
}

std::string render_diagnostics(SvState &state, std::span<const slang::Diagnostic> diags)
{
	if (diags.empty()) {
		return {};
	}
	return slang::DiagnosticEngine::reportAll(state.driver.sourceManager, diags);
}

// Throw `fallback` (or the rendered diagnostics) if `diags` contains an error;
// otherwise print any warnings to stderr.
void check_diagnostics(
		SvState &state, std::span<const slang::Diagnostic> diags, const char *fallback)
{
	const std::string text = render_diagnostics(state, diags);
	if (has_errors(diags)) {
		throw std::runtime_error(text.empty() ? fallback : text);
	}
	std::fwrite(text.data(), 1, text.size(), stderr);
}

} // namespace

// Evaluate SystemVerilog expression `text` in the scope of the elaborated top
// module. The result references existing signals; no new signal or assignment
// is added to the netlist.
ir::Value eval_expression(SvState &state, const std::string &text)
{
	auto &compilation = *state.compilation;
	auto tree = slang::syntax::SyntaxTree::fromText(text, state.driver.sourceManager, "expression");
	if (!tree) {
		throw std::runtime_error("failed to parse expression");
	}

	check_diagnostics(state, diagnostics_span(tree->diagnostics()), "failed to parse expression");

	auto *expression_syntax = tree->root().as_if<slang::syntax::ExpressionSyntax>();
	if (expression_syntax == nullptr) {
		throw std::runtime_error("input is not a SystemVerilog expression");
	}

	slang::ast::Compilation::DiagnosticCapture capture(compilation);
	slang::ast::ASTContext context(state.netlist->realm, slang::ast::LookupLocation::max);
	const slang::ast::Expression &expr = slang::ast::Expression::bind(*expression_syntax, context);
	slang::Diagnostics bind_diags = capture.finish();

	check_diagnostics(state, diagnostics_span(bind_diags), "failed to bind expression");
	if (expr.bad()) {
		throw std::runtime_error("failed to bind expression");
	}

	const size_t before = state.netlist->issued_diagnostics.size();
	ir::Value value;
	try {
		value = state.netlist->eval(expr);
	} catch (const slang_frontend::InternalError &exc) {
		throw std::runtime_error(std::string("expression evaluation failed: ") + exc.what());
	}

	const auto &issued = state.netlist->issued_diagnostics;
	check_diagnostics(state, std::span(issued).subspan(std::min(before, issued.size())),
			"expression evaluation failed");
	return value;
}

// Elaborate with slang command-line `args` (files, -f/-F file lists, +incdir,
// --top, defines, ...) plus optional inline `source` text. On success the
// returned state keeps the compilation alive for expression evaluation.
ReadResult read_sv(const std::string &source, std::vector<std::string> args)
{
	auto state = std::make_unique<SvState>();
	auto &driver = state->driver;
	driver.addStandardArgs();

	state->settings.addOptions(driver.cmdLine);
	slang_frontend::diag::setup_messages(driver.diagEngine);

	if (!source.empty()) {
		auto buffer = driver.sourceManager.assignText("<inline>", std::string_view{source});
		driver.sourceLoader.addBuffer(buffer);
	}

	args.insert(args.begin(), "grounding");
	std::vector<const char *> c_args;
	c_args.reserve(args.size());
	for (auto &a : args) {
		c_args.push_back(a.c_str());
	}

	if (!driver.parseCommandLine(
				static_cast<int>(c_args.size()), const_cast<char **>(c_args.data()))) {
		throw std::runtime_error("failed to parse slang command line");
	}

	fixup_options(state->settings, driver);
	if (!driver.processOptions()) {
		throw std::runtime_error("failed to process slang options");
	}
	catch_forbidden_options(driver);

	if (!driver.parseAllSources()) {
		throw std::runtime_error("failed to parse SystemVerilog sources");
	}

	state->compilation = driver.createCompilation();
	driver.reportCompilation(*state->compilation, /*quiet=*/true);

	if (driver.diagEngine.getNumErrors()) {
		(void)driver.reportDiagnostics(/*quiet=*/false);
		throw std::runtime_error("SystemVerilog compilation failed");
	}

	if (state->settings.ast_compilation_only.value_or(false)) {
		throw std::runtime_error("--ast-compilation-only does not build a netlist");
	}

	for (auto *instance : state->compilation->getRoot().topInstances) {
		if (instance->getDefinition().definitionKind == slang::ast::DefinitionKind::Program) {
			continue;
		}
		state->tops.push_back(instance);
	}

	if (state->tops.size() != 1) {
		throw std::runtime_error(
				"expected exactly one top-level module, got " + std::to_string(state->tops.size()));
	}

	state->hqueue = std::make_unique<HierarchyQueue>();
	auto backend = std::make_unique<BackendGraphBuilder>();
	state->netlist = std::make_unique<NetlistContext>(
			std::move(backend), state->settings, *state->compilation, *state->tops.front());
	try {
		populate_netlist(*state->hqueue, *state->netlist);
	} catch (slang_frontend::InternalError &exc) {
		state->netlist->report_into(driver.diagEngine);
		(void)driver.reportDiagnostics(/*quiet=*/false);
		throw std::runtime_error(
				std::string("language frontend raised an internal error: ") + exc.what());
	} catch (...) {
		// Report what the frontend collected before the backend gave up.
		state->netlist->report_into(driver.diagEngine);
		(void)driver.reportDiagnostics(/*quiet=*/false);
		throw;
	}

	state->netlist->report_into(driver.diagEngine);
	if (driver.diagEngine.getNumErrors() || driver.diagEngine.getNumWarnings()) {
		(void)driver.reportDiagnostics(/*quiet=*/false);
	}
	if (driver.diagEngine.getNumErrors()) {
		throw std::runtime_error("netlist elaboration failed");
	}

	auto *netlist = static_cast<lean_object *>(state->netlist->backend->take_netlist());
	if (netlist == nullptr) {
		throw std::runtime_error("native elaboration produced no netlist");
	}
	return {netlist, state.release()};
}

} // namespace grounding

namespace {

std::string from_lean(lean_object *s)
{
	return std::string(lean_string_cstr(s), lean_string_size(s) - 1);
}

// `Except.error msg` / `Except.ok value`.
lean_object *mk_except(unsigned tag, lean_object *payload)
{
	lean_object *r = lean_alloc_ctor(tag, 1, 0);
	lean_ctor_set(r, 0, payload);
	return r;
}

lean_object *mk_error(std::string_view message)
{
	return mk_except(0, lean_mk_string_from_bytes(message.data(), message.size()));
}

lean_object *io_result(lean_object *value)
{
	return lean_io_result_mk_ok(value);
}

// Finalizer and traversal hook for the external `SvContext` object.
void sv_state_finalize(void *ptr)
{
	delete static_cast<grounding::SvState *>(ptr);
}

void sv_state_foreach(void *ptr, b_lean_obj_arg fn)
{
	auto *state = static_cast<grounding::SvState *>(ptr);
	if (state == nullptr || state->netlist == nullptr || state->netlist->backend == nullptr) {
		return;
	}
	// `fn` is borrowed; `lean_apply_1` consumes both the closure and the
	// argument, so take a reference to each per call.
	state->netlist->backend->for_each_lean_ref(const_cast<lean_object *>(fn), [](void *f,
																					  void *obj) {
		lean_inc(static_cast<lean_object *>(f));
		lean_inc(static_cast<lean_object *>(obj));
		lean_dec(lean_apply_1(static_cast<lean_object *>(f), static_cast<lean_object *>(obj)));
	});
}

lean_external_class *sv_state_class()
{
	static lean_external_class *cls =
			lean_register_external_class(sv_state_finalize, sv_state_foreach);
	return cls;
}

// `Elaborated { netlist, context }` (two object fields).
lean_object *mk_elaborated(lean_object *netlist, grounding::SvState *state)
{
	lean_object *context = lean_alloc_external(sv_state_class(), state);
	lean_object *result = lean_alloc_ctor(0, 2, 0);
	lean_ctor_set(result, 0, netlist);
	lean_ctor_set(result, 1, context);
	return result;
}

lean_object *run_read_sv(const std::string &source, std::vector<std::string> args)
{
	std::string error;
	grounding::ReadResult result;
	try {
		result = grounding::read_sv(source, std::move(args));
	} catch (const std::exception &e) {
		error = e.what();
	} catch (...) {
		error = "unknown native error";
	}

	if (result.state == nullptr || result.netlist == nullptr) {
		if (result.netlist != nullptr) {
			lean_dec(static_cast<lean_object *>(result.netlist));
		}
		delete result.state;
		if (error.empty()) {
			error = "native elaboration produced no netlist";
		}
		return io_result(mk_error(error));
	}
	return io_result(
			mk_except(1, mk_elaborated(static_cast<lean_object *>(result.netlist), result.state)));
}

} // namespace

// `readSv (source top : String)`.
extern "C" LEAN_EXPORT lean_object *grounding_read_sv(lean_object *source, lean_object *top)
{
	const std::string source_str = from_lean(source);
	const std::string top_str = from_lean(top);
	lean_dec(source);
	lean_dec(top);
	std::vector<std::string> args;
	if (!top_str.empty()) {
		args = {"--top", top_str};
	}
	return run_read_sv(source_str, std::move(args));
}

// `readSvArgs (args : Array String)`: slang command-line arguments.
extern "C" LEAN_EXPORT lean_object *grounding_read_sv_args(lean_object *args)
{
	std::vector<std::string> argv;
	const size_t n = lean_array_size(args);
	argv.reserve(n);
	for (size_t i = 0; i < n; i++) {
		argv.push_back(from_lean(lean_array_get_core(args, i)));
	}
	lean_dec(args);
	return run_read_sv("", std::move(argv));
}

// `evalExprBuilt (context : @& SvContext) (expr : String) :
//    IO (Except String BuiltValue)`.
// `context` is an `@&` (borrowed) argument; `expr` is owned.
extern "C" LEAN_EXPORT lean_object *grounding_sv_eval(lean_object *context, lean_object *expr)
{
	const std::string text = from_lean(expr);
	lean_dec(expr);

	if (!lean_is_external(context)) {
		return io_result(mk_error("invalid elaboration context"));
	}
	auto *state = static_cast<grounding::SvState *>(lean_get_external_data(context));

	try {
		std::lock_guard lock(state->mutex);
		ir::Value value = grounding::eval_expression(*state, text);
		void *realized = state->netlist->backend->realize_value(value);
		if (realized == nullptr) {
			throw std::runtime_error("cannot realize expression value");
		}
		return io_result(mk_except(1, static_cast<lean_object *>(realized)));
	} catch (const std::exception &e) {
		return io_result(mk_error(e.what()));
	} catch (...) {
		return io_result(mk_error("unknown native error"));
	}
}
