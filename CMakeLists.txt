cmake_minimum_required(VERSION 3.20)
project(tctl_sat LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# ── Compiler warnings ───────────────────────────────────────────────────────
add_compile_options(-Wall -Wextra -Wpedantic -Werror)

# ── Detect platform ─────────────────────────────────────────────────────────
if(APPLE)
    set(UDBM_PLATFORM "darwin")
else()
    set(UDBM_PLATFORM "x86_64-linux")
endif()
message(STATUS "UDBM platform: ${UDBM_PLATFORM}")

# ── Find Z3 ─────────────────────────────────────────────────────────────────
# Try to find Z3 using find_package first, fallback to manual search
find_package(Z3 QUIET)

if(NOT Z3_FOUND)
    # Manual Z3 configuration (for Homebrew on macOS)
    set(Z3_PREFIX "/opt/homebrew/opt/z3")
    if(EXISTS "${Z3_PREFIX}")
        set(Z3_INCLUDE_DIRS "${Z3_PREFIX}/include")
        set(Z3_LIBRARIES "${Z3_PREFIX}/lib/libz3.dylib")
        message(STATUS "Found Z3 (manual): ${Z3_PREFIX}")
    else()
        message(FATAL_ERROR "Z3 not found. Please install via: brew install z3")
    endif()
endif()

# ── UDBM Configuration (REQUIRED) ────────────────────────────────────────────
# UDBM is mandatory for TCTL zone operations
set(UDBM_DIR "${CMAKE_SOURCE_DIR}/../UDBM" CACHE PATH "Path to UDBM installation")
set(UDBM_BUILD_DIR "${UDBM_DIR}/build-${UDBM_PLATFORM}-release")
set(UDBM_LIB_PATH "${UDBM_BUILD_DIR}/src/libUDBM.a")

# Check if UDBM is installed, if not install it
if(NOT EXISTS "${UDBM_DIR}" OR NOT EXISTS "${UDBM_LIB_PATH}")
    message(STATUS "UDBM not found or not compiled. Installing UDBM automatically...")
    
    # Clone UDBM if not present
    if(NOT EXISTS "${UDBM_DIR}")
        message(STATUS "Cloning UDBM repository...")
        execute_process(
            COMMAND git clone https://github.com/UPPAALModelChecker/UDBM "${UDBM_DIR}"
            RESULT_VARIABLE UDBM_CLONE_RESULT
        )
        if(NOT UDBM_CLONE_RESULT EQUAL 0)
            message(FATAL_ERROR "Failed to clone UDBM repository")
        endif()
        message(STATUS "UDBM cloned successfully")
    endif()
    
    # Run getlibs.sh
    message(STATUS "Running UDBM getlibs.sh for ${UDBM_PLATFORM}...")
    execute_process(
        COMMAND ./getlibs.sh ${UDBM_PLATFORM}
        WORKING_DIRECTORY "${UDBM_DIR}"
        RESULT_VARIABLE UDBM_GETLIBS_RESULT
    )
    if(NOT UDBM_GETLIBS_RESULT EQUAL 0)
        message(FATAL_ERROR "Failed to run UDBM getlibs.sh")
    endif()
    message(STATUS "UDBM dependencies fetched")
    
    # Compile UDBM
    message(STATUS "Compiling UDBM (${UDBM_PLATFORM}-libs-release)...")
    execute_process(
        COMMAND ./compile.sh ${UDBM_PLATFORM}-libs-release
        WORKING_DIRECTORY "${UDBM_DIR}"
        RESULT_VARIABLE UDBM_COMPILE_RESULT
    )
    if(NOT UDBM_COMPILE_RESULT EQUAL 0)
        message(FATAL_ERROR "Failed to compile UDBM")
    endif()
    message(STATUS "UDBM compiled successfully")
endif()

# Verify UDBM is now available
if(EXISTS "${UDBM_LIB_PATH}")
    set(UDBM_INCLUDE_DIRS "${UDBM_DIR}/include")
    set(UDBM_LOCAL_INCLUDE "${UDBM_DIR}/local/${UDBM_PLATFORM}/include")
    set(UDBM_LIBRARIES "${UDBM_LIB_PATH}")
    message(STATUS "Found UDBM: ${UDBM_DIR}")
    message(STATUS "UDBM includes: ${UDBM_INCLUDE_DIRS}")
    message(STATUS "UDBM local includes: ${UDBM_LOCAL_INCLUDE}")
    add_definitions(-DUSE_UDBM)
else()
    message(FATAL_ERROR "UDBM library not found at ${UDBM_LIB_PATH} after installation attempt")
endif()

# ── Sources ──────────────────────────────────────────────────────────────────
set(SOURCES
    src/ast.cpp
    src/lexer.cpp
    src/parser.cpp
    src/normalization.cpp
    src/tableau.cpp
    src/timed_automaton.cpp
    src/z3_solver.cpp
    src/zone.cpp
    src/cli.cpp
    src/utils.cpp
    src/test.cpp
    src/main.cpp
)

# ── Executable ───────────────────────────────────────────────────────────────
add_executable(tctl_sat ${SOURCES})
target_include_directories(tctl_sat PRIVATE 
    include
    ${Z3_INCLUDE_DIRS}
)
target_link_libraries(tctl_sat PRIVATE ${Z3_LIBRARIES})

# ── UDBM linking (always enabled for TCTL) ──────────────────────────────────
# Also need UUtils libraries (base, hash) that UDBM depends on
set(UUTILS_LIB_DIR "${UDBM_DIR}/local/${UDBM_PLATFORM}/lib")
set(UUTILS_LIBRARIES
    "${UUTILS_LIB_DIR}/libbase.a"
    "${UUTILS_LIB_DIR}/libhash.a"
)
target_include_directories(tctl_sat PRIVATE 
    ${UDBM_INCLUDE_DIRS}
    ${UDBM_LOCAL_INCLUDE}
)
target_link_libraries(tctl_sat PRIVATE ${UDBM_LIBRARIES} ${UUTILS_LIBRARIES})


#OPENMP IS NOT SUPPOETED YET
## ── OpenMP (optional parallelism) ────────────────────────────────────────────
## Apple's clang doesn't bundle OpenMP, but Homebrew ships libomp separately.
## Point CMake's FindOpenMP at /opt/homebrew/opt/libomp before searching.
#if(APPLE AND EXISTS "/opt/homebrew/opt/libomp")
#    set(OpenMP_C_FLAGS   "-Xclang -fopenmp" CACHE STRING "" FORCE)
#    set(OpenMP_CXX_FLAGS "-Xclang -fopenmp" CACHE STRING "" FORCE)
#    set(OpenMP_C_LIB_NAMES   "omp" CACHE STRING "" FORCE)
#    set(OpenMP_CXX_LIB_NAMES "omp" CACHE STRING "" FORCE)
#    set(OpenMP_omp_LIBRARY
#        "/opt/homebrew/opt/libomp/lib/libomp.dylib" CACHE STRING "" FORCE)
#    # Also expose the libomp headers to the compiler search path.
#    target_include_directories(tctl_sat PRIVATE "/opt/homebrew/opt/libomp/include")
#endif()
#
#find_package(OpenMP QUIET)
#if(OpenMP_CXX_FOUND)
#    target_link_libraries(tctl_sat PRIVATE OpenMP::OpenMP_CXX)
#    target_compile_definitions(tctl_sat PRIVATE TCTL_USE_OPENMP)
#    message(STATUS "OpenMP found — parallel tableau exploration enabled")
#else()
#    message(STATUS "OpenMP not found — building single-threaded")
#endif()
#