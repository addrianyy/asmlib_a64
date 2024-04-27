cmake_minimum_required(VERSION 3.15)

add_library(asmlib_a64 "")
add_subdirectory(src)

target_include_directories(asmlib_a64 PUBLIC src)
target_compile_features(asmlib_a64 PUBLIC cxx_std_20)

if (TARGET baselib)
    target_link_libraries(asmlib_a64 PUBLIC baselib)
endif()