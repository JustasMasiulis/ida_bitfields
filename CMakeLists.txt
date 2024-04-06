cmake_minimum_required(VERSION 3.14)

project(ida_bitfields)

include(FetchContent)

FetchContent_Declare(
  HexSuite
  GIT_REPOSITORY https://github.com/can1357/hexsuite
)

FetchContent_MakeAvailable(HexSuite)

add_library(bitfields SHARED ${CMAKE_CURRENT_SOURCE_DIR}/plugin.cpp)

target_compile_features(bitfields PRIVATE cxx_std_20)

if (DEFINED ENV{IDA_PATH})
    set(IDA_PATH $ENV{IDA_PATH})
elseif (DEFINED ENV{IDA_DIR})
    set(IDA_PATH $ENV{IDA_DIR})
else()
    message(FATAL_ERROR "IDA_PATH or IDA_DIR environment variable must be set")
endif()

target_include_directories(bitfields SYSTEM PRIVATE 
    ${hexsuite_SOURCE_DIR}
    ${IDA_PATH}/sdk/include
    ${IDA_PATH}/plugins/hexrays_sdk/include)

if (${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    set(IDA_SDK_LIB_OS "win_vc")
elseif (${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    set(IDA_SDK_LIB_OS "mac_clang")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    set(IDA_SDK_LIB_OS "linux_gcc")
else()
    message(FATAL_ERROR "unrecognized system: ${CMAKE_SYSTEM_NAME} (Windows/Darwin/Linux expected)")
endif()

if(${CMAKE_SYSTEM_PROCESSOR} MATCHES "arm") 
    set(IDA_SDK_LIB_ARCH "arm64")
else()
    set(IDA_SDK_LIB_ARCH "x64")
endif()

if("${CMAKE_SIZEOF_VOID_P}" STREQUAL "8")
    set(IDA_SDK_LIB_BITS "64")
    set_target_properties(bitfields PROPERTIES OUTPUT_NAME "bitfields64")
else()
    set(IDA_SDK_LIB_BITS "32")
endif()

target_link_libraries(bitfields PRIVATE "ida.lib")
target_link_directories(bitfields PRIVATE ${IDA_PATH}/sdk/lib/${IDA_SDK_LIB_ARCH}_${IDA_SDK_LIB_OS}_${IDA_SDK_LIB_BITS}_pro)
