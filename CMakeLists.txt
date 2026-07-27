cmake_minimum_required(VERSION 3.20)
project(tctl_sat LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# ── Compiler warnings ───────────────────────────────────────────────────────
add_compile_options(-Wall -Wextra -Wpedantic -Werror)

# ── Find Z3 ─────────────────────────────────────────────────────────────────
# Try to find Z3 using find_package first, fallback to manual search
find_package(Z3 QUIET)
if(NOT Z3_FOUND)

    if(APPLE)
        # Homebrew default location (Apple Silicon)
        set(Z3_PREFIX "/opt/homebrew/opt/z3")

        if(EXISTS "${Z3_PREFIX}")
            set(Z3_INCLUDE_DIRS "${Z3_PREFIX}/include")
            set(Z3_LIBRARIES "${Z3_PREFIX}/lib/libz3.dylib")
            message(STATUS "Found Z3 (Homebrew macOS): ${Z3_PREFIX}")
        else()
            message(FATAL_ERROR "Z3 not found on macOS. Install with: brew install z3")
        endif()

    elseif(UNIX)
        # Linux: try system paths
        find_path(Z3_INCLUDE_DIRS z3.h
            PATHS /usr/include /usr/local/include
        )

        find_library(Z3_LIBRARIES z3
            PATHS /usr/lib /usr/local/lib /usr/lib/x86_64-linux-gnu
        )

        if(Z3_INCLUDE_DIRS AND Z3_LIBRARIES)
            message(STATUS "Found Z3 (Linux system)")
        else()
            message(FATAL_ERROR "Z3 not found on Linux. Install with your package manager (e.g., sudo apt install z3 libz3-dev)")
        endif()

    endif()

endif()

# ── HDBM (header-only DBM/federation layer) ─────────────────────────────────
# Zone algebra lives in HDBM/include/ptctlmc.  It is header-only, so every DBM
# primitive inlines into its call site -- at the dimensions this engine uses
# (one clock per timed subformula) that beats an out-of-line library call.
set(HDBM_DIR        "${CMAKE_SOURCE_DIR}/HDBM" CACHE PATH   "Path to the HDBM checkout")
set(HDBM_REPOSITORY "https://github.com/horaverify/HDBM.git"
                                                 CACHE STRING "HDBM git remote")
set(HDBM_TAG        "main"                       CACHE STRING "HDBM branch or tag")

# One header decides whether the checkout is usable; testing the directory alone
# would accept an interrupted clone.
set(HDBM_MARKER "${HDBM_DIR}/include/ptctlmc/dbm_ops.hpp")

if(NOT EXISTS "${HDBM_MARKER}")
    if(EXISTS "${HDBM_DIR}")
        message(FATAL_ERROR
            "${HDBM_DIR} exists but ${HDBM_MARKER} is missing: the checkout is "
            "incomplete. Delete the directory and re-run cmake to fetch it again, "
            "or point -DHDBM_DIR= at a good checkout.")
    endif()

    find_package(Git QUIET)
    if(NOT Git_FOUND)
        message(FATAL_ERROR
            "HDBM is missing and git was not found, so it cannot be fetched. "
            "Install git, or clone ${HDBM_REPOSITORY} to ${HDBM_DIR} by hand.")
    endif()

    message(STATUS "HDBM not found -- cloning ${HDBM_REPOSITORY} (${HDBM_TAG})")
    execute_process(
        COMMAND "${GIT_EXECUTABLE}" clone --depth 1 --branch "${HDBM_TAG}"
                "${HDBM_REPOSITORY}" "${HDBM_DIR}"
        RESULT_VARIABLE HDBM_CLONE_RESULT
        ERROR_VARIABLE  HDBM_CLONE_ERROR)
    if(NOT HDBM_CLONE_RESULT EQUAL 0)
        message(FATAL_ERROR "Failed to clone HDBM: ${HDBM_CLONE_ERROR}")
    endif()
    if(NOT EXISTS "${HDBM_MARKER}")
        message(FATAL_ERROR
            "Cloned ${HDBM_REPOSITORY} but ${HDBM_MARKER} is still missing; the "
            "remote layout may have changed.")
    endif()
    message(STATUS "HDBM cloned into ${HDBM_DIR}")
endif()

set(HDBM_INCLUDE_DIR "${HDBM_DIR}/include")
message(STATUS "HDBM includes: ${HDBM_INCLUDE_DIR}")

# ── Sources ──────────────────────────────────────────────────────────────────
set(SOURCES
    src/ast.cpp
    src/lexer.cpp
    src/parser.cpp
    src/normalization.cpp
    src/tableau.cpp
    src/satisfaction_set.cpp
    src/z3_solver.cpp
    src/timed_automaton.cpp
    src/zone.cpp
    src/zoneset.cpp
    src/zoneset_test.cpp
    src/cli.cpp
    src/utils.cpp
    src/test.cpp
    src/benchmark.cpp
    src/main.cpp
)
# src/timed_automaton.cpp holds the witness-automaton datatypes, serialisers and
# structural validation; the extractor itself lives with the engine, which is
# where the marking is.

# ── Executable ───────────────────────────────────────────────────────────────
add_executable(tctl_sat ${SOURCES})

# Enlarge the main-thread stack so the tableau's deep-but-finite DFS does not
# overflow the default 8 MB, without an artificial recursion-depth limit.
if(APPLE)
    target_link_options(tctl_sat PRIVATE -Wl,-stack_size,0x20000000)  # 512 MB
elseif(UNIX)
    target_link_options(tctl_sat PRIVATE -Wl,-z,stacksize=0x20000000)
endif()
target_include_directories(tctl_sat PRIVATE
    include
    ${HDBM_INCLUDE_DIR}
    ${Z3_INCLUDE_DIRS}
)
target_link_libraries(tctl_sat PRIVATE ${Z3_LIBRARIES})

##
### ── OpenMP (optional parallelism) ────────────────────────────────────────────
### Apple's clang doesn't bundle OpenMP, but Homebrew ships libomp separately.
### Point CMake's FindOpenMP at /opt/homebrew/opt/libomp before searching.
##if(APPLE AND EXISTS "/opt/homebrew/opt/libomp")
##    set(OpenMP_C_FLAGS   "-Xclang -fopenmp" CACHE STRING "" FORCE)
##    set(OpenMP_CXX_FLAGS "-Xclang -fopenmp" CACHE STRING "" FORCE)
##    set(OpenMP_C_LIB_NAMES   "omp" CACHE STRING "" FORCE)
##    set(OpenMP_CXX_LIB_NAMES "omp" CACHE STRING "" FORCE)
##    set(OpenMP_omp_LIBRARY
##        "/opt/homebrew/opt/libomp/lib/libomp.dylib" CACHE STRING "" FORCE)
##    # Also expose the libomp headers to the compiler search path.
##    target_include_directories(tctl_sat PRIVATE "/opt/homebrew/opt/libomp/include")
##endif()
##
##find_package(OpenMP QUIET)
##if(OpenMP_CXX_FOUND)
##    target_link_libraries(tctl_sat PRIVATE OpenMP::OpenMP_CXX)
##    target_compile_definitions(tctl_sat PRIVATE TCTL_USE_OPENMP)
##    message(STATUS "OpenMP found — parallel tableau exploration enabled")
##else()
##    message(STATUS "OpenMP not found — building single-threaded")
##endif()
# ── API documentation ────────────────────────────────────────────────────────
# `cmake --build build --target docs` renders docs/api/html/index.html.
find_package(Doxygen QUIET)
if(DOXYGEN_FOUND)
    add_custom_target(docs
        COMMAND ${DOXYGEN_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        COMMENT "Generating API documentation with Doxygen"
        VERBATIM)

    # The LaTeX backend additionally yields docs/api/latex/refman.pdf.
    add_custom_target(docs-pdf
        COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_SOURCE_DIR}/docs/api
        COMMAND ${CMAKE_MAKE_PROGRAM} -C ${CMAKE_CURRENT_SOURCE_DIR}/docs/api/latex
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        DEPENDS docs
        COMMENT "Rendering the API documentation to PDF"
        VERBATIM)
endif()
