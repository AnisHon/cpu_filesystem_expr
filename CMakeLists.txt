cmake_minimum_required(VERSION 3.31)
project(expr)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0")  # 添加 -O0 标志

add_executable(expr main.cpp)
