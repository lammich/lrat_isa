cmake_minimum_required(VERSION 3.0)

# set(CMAKE_VERBOSE_MAKEFILE ON)

project(lrat_cpp)

find_package(Boost COMPONENTS REQUIRED iostreams stacktrace_basic timer)

find_package(TBB REQUIRED)

set(CMAKE_CXX_FLAGS "-Wall -Wextra -Weffc++ -Wpedantic -Wzero-as-null-pointer-constant -std=c++17")

if (CMAKE_BUILD_TYPE STREQUAL "RelWithDebInfo")
  include_directories("~/opt/include")
  link_directories("~/opt/lib")
  link_libraries(profiler)
endif()


add_executable(test test.cpp Logging.cpp)

add_executable(lrat_cpp main.cpp Logging.cpp)
add_executable(lrat_cpp_par par_main.cpp Logging.cpp)
add_executable(lrat_cpp_ss simple_seq.cpp Logging.cpp)



target_link_libraries(lrat_cpp ${Boost_LIBRARIES} dl)
install(TARGETS lrat_cpp RUNTIME DESTINATION bin)

target_link_libraries(lrat_cpp_par ${Boost_LIBRARIES} dl tbb)
install(TARGETS lrat_cpp_par RUNTIME DESTINATION bin)

target_link_libraries(lrat_cpp_ss ${Boost_LIBRARIES} dl)
install(TARGETS lrat_cpp_ss RUNTIME DESTINATION bin)

target_link_libraries(test ${Boost_LIBRARIES} dl)
install(TARGETS test RUNTIME DESTINATION bin)
