cmake_minimum_required(VERSION 3.4.3)

# To support both in- and out-of-source builds,
# we check for the presence of the add_llvm_loadable_module command.
# - if this command is not present, we are building out-of-source
set(CMAKE_CXX_COMPILER clang)

set(CMAKE_CXX_EXTENSIONS OFF)

if(NOT COMMAND add_llvm_loadable_module)
    message(STATUS "TEST")
    
    if (DEFINED ENV{LLVM_DIR})
        # We need to match the build environment for LLVM:
        # In particular, we need C++11 and the -fno-rtti flag
    if(CMAKE_BUILD_TYPE MATCHES "Debug")
        set(CMAKE_CXX_FLAGS "-std=c++17 -O0 -fno-rtti -fno-pie -g")
    else()
        set(CMAKE_CXX_FLAGS "-std=c++17 -O0 -fno-rtti -fno-pie -g")
    endif()

    find_package(LLVM REQUIRED CONFIG)

        set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
        list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
        include(AddLLVM)

        add_definitions(${LLVM_DEFINITIONS})
        include_directories(${LLVM_INCLUDE_DIRS})

    else()
        message(FATAL_ERROR "\
WARNING: The LLVM_DIR var was not set (required for an out-of-source build)!\n\
Please set this to environment variable to point to the LLVM build directory\
(e.g. on linux: export LLVM_DIR=/path/to/llvm/build/dir)")
    endif()
    else()
        set(IN_SOURCE_BUILD 1)
endif()

if(NOT DEFINED LLVM_VERSION_MAJOR)
  set(LLVM_VERSION_MAJOR 11)
endif()
if(NOT DEFINED LLVM_VERSION_MINOR)
  set(LLVM_VERSION_MINOR 0)
endif()
if(NOT DEFINED LLVM_VERSION_PATCH)
  set(LLVM_VERSION_PATCH 0)
endif()
if(NOT DEFINED LLVM_VERSION_SUFFIX)
  set(LLVM_VERSION_SUFFIX "")
endif()

if (NOT PACKAGE_VERSION)
  set(PACKAGE_VERSION
    "${LLVM_VERSION_MAJOR}.${LLVM_VERSION_MINOR}.${LLVM_VERSION_PATCH}${LLVM_VERSION_SUFFIX}")
endif()

add_subdirectory(Xmm)
#add_subdirectory(test)
