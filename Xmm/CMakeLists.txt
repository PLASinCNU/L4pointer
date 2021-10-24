add_library(Epsilon MODULE
    # List your source files here.
    #MPAll.cpp
    MPAvailable.cpp
    util.cpp
)

# Use C++11 to compile our pass (i.e., supply -std=c++11).
#include_directories(${PROJECT_SOURCE_DIR/})
#include_directories(${CMAKE_CURRENT_SOURCE_DIR})
target_compile_features(Epsilon PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.

