# SPDX-FileCopyrightText: Erat demo technologie, s.r.o.
# SPDX-License-Identifier: Apache-2.0
cmake_minimum_required(VERSION 3.28)

project(grounding_native CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

set(SV_ELAB_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/sv-elab")
set(SLANG_DIR "${SV_ELAB_DIR}/third_party/slang")

if(NOT LEAN_INCLUDE_DIR)
  message(FATAL_ERROR
    "LEAN_INCLUDE_DIR must point at the Lean sysroot include directory")
endif()

# Build slang as PIC object code to fold into our static library. Its options
# are set as normal variables (CMP0077), so they do not pollute the cache.
set(CMAKE_POLICY_DEFAULT_CMP0077 NEW)
set(BUILD_SHARED_LIBS OFF)
set(SLANG_INCLUDE_TOOLS OFF)
set(SLANG_INCLUDE_TESTS OFF)
set(SLANG_INCLUDE_DOCS OFF)
set(SLANG_INCLUDE_INSTALL OFF)
set(SLANG_INCLUDE_PYLIB OFF)
set(SLANG_USE_MIMALLOC OFF)
set(SLANG_USE_SYSTEM_FMT OFF)
set(SLANG_USE_SYSTEM_BOOST OFF)
set(SLANG_USE_SYSTEM_TOMLPLUSPLUS OFF)

add_subdirectory("${SLANG_DIR}" "${CMAKE_CURRENT_BINARY_DIR}/slang")

set(SV_ELAB_FRONTEND_SOURCES
  "${SV_ELAB_DIR}/src/addressing.cc"
  "${SV_ELAB_DIR}/src/async_pattern.cc"
  "${SV_ELAB_DIR}/src/builder.cc"
  "${SV_ELAB_DIR}/src/calculate.cc"
  "${SV_ELAB_DIR}/src/diag.cc"
  "${SV_ELAB_DIR}/src/initialization.cc"
  "${SV_ELAB_DIR}/src/lvalue.cc"
  "${SV_ELAB_DIR}/src/naming.cc"
  "${SV_ELAB_DIR}/src/procedural.cc"
  "${SV_ELAB_DIR}/src/slang_frontend.cc"
  "${SV_ELAB_DIR}/src/variables.cc"
)

# One static library with our sources and slang's objects
add_library(grounding_sv STATIC
  ${SV_ELAB_FRONTEND_SOURCES}
  "${CMAKE_CURRENT_SOURCE_DIR}/backend_builder.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/driver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/ir.cpp"
  $<TARGET_OBJECTS:slang_slang>
)

target_include_directories(grounding_sv PRIVATE
  "${CMAKE_CURRENT_SOURCE_DIR}"
  "${SV_ELAB_DIR}/src"
  "${SV_ELAB_DIR}/third_party/hashlib"
  "${LEAN_INCLUDE_DIR}"
)

target_compile_definitions(grounding_sv PRIVATE
  SLANG_MUX_LOWERING
  SLANG_NO_YOSYS
)

# Warnings for our own sources (not the vendored frontend).
set_source_files_properties(
  "${CMAKE_CURRENT_SOURCE_DIR}/backend_builder.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/driver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/ir.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/lean_builder.cpp"
  PROPERTIES COMPILE_OPTIONS "-Wall;-Wextra")

# Usage requirements (headers/definitions) of slang for our sources.
target_link_libraries(grounding_sv PRIVATE slang::slang)
