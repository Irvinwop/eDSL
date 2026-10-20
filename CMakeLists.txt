cmake_minimum_required(VERSION 3.25)
project(edsl VERSION 0.1.0 LANGUAGES C CXX)

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

check_c_compiler_flag("-std=gnu23" EDSL_HAS_GNU23)
check_cxx_compiler_flag("-std=gnu++26" EDSL_HAS_GNUCXX26)
if(NOT EDSL_HAS_GNU23 OR NOT EDSL_HAS_GNUCXX26)
    message(FATAL_ERROR
        "eDSL requires -std=gnu23 and -std=gnu++26. "
        "Select supporting C/C++ compilers (the bootstrap is checked with Clang 18).")
endif()

# Optional native-domain probes. The implementation/proofs build through Lake.
add_library(edsl_gnu23 INTERFACE)
add_library(edsl::gnu23 ALIAS edsl_gnu23)
target_compile_options(edsl_gnu23 INTERFACE "$<$<COMPILE_LANGUAGE:C>:-std=gnu23>")

add_library(edsl_gnucxx26 INTERFACE)
add_library(edsl::gnucxx26 ALIAS edsl_gnucxx26)
target_compile_options(edsl_gnucxx26 INTERFACE "$<$<COMPILE_LANGUAGE:CXX>:-std=gnu++26>")

# Compile-only dialect probes; semantic and runtime validation lives in Lake and scripts.
add_library(edsl_check_gnu23 OBJECT checks/gnu23.c)
target_link_libraries(edsl_check_gnu23 PRIVATE edsl::gnu23)
target_compile_options(edsl_check_gnu23 PRIVATE -Wall -Wextra -Werror)

add_library(edsl_check_gnucxx26 OBJECT checks/gnucxx26.cpp)
target_link_libraries(edsl_check_gnucxx26 PRIVATE edsl::gnucxx26)
target_compile_options(edsl_check_gnucxx26 PRIVATE -Wall -Wextra -Werror)
