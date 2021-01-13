add_library(SkeletonPass MODULE
    # List your source files here.
    #MPAll.cpp
    ReMP.cpp
    MPAvailable.cpp
    SizeofTypes.cpp
    util.cpp
)

# Use C++11 to compile our pass (i.e., supply -std=c++11).
target_compile_features(SkeletonPass PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.

