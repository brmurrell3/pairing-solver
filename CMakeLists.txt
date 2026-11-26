cmake_minimum_required(VERSION 3.24)
project(pairing_solver VERSION 1.0.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set(CMAKE_BUILD_TYPE Release)
endif()

# Installed locally (Homebrew: tomlplusplus 3.4.0); nothing is fetched.
find_package(tomlplusplus 3.4 REQUIRED)

add_library(pairing
  src/money.cpp
  src/model.cpp
  src/margin.cpp
  src/spread.cpp
  src/simplex.cpp
  src/solver.cpp
  src/checker.cpp
  src/greedy.cpp
  src/dp.cpp
)
target_include_directories(pairing PUBLIC include)
target_link_libraries(pairing PRIVATE tomlplusplus::tomlplusplus)
target_compile_options(pairing PRIVATE -Wall -Wextra -Wpedantic)

enable_testing()

add_executable(pairing_tests
  tests/main.cpp
  tests/unit.cpp
  tests/fixtures.cpp
  tests/solver.cpp
  tests/exhaustive.cpp
)
target_link_libraries(pairing_tests PRIVATE pairing tomlplusplus::tomlplusplus)
target_compile_definitions(pairing_tests PRIVATE PAIRING_DATA_DIR="${CMAKE_SOURCE_DIR}/data")
target_compile_options(pairing_tests PRIVATE -Wall -Wextra -Wpedantic)

add_test(NAME unit COMMAND pairing_tests unit)
add_test(NAME cboe_manual
  COMMAND pairing_tests fixture ${CMAKE_SOURCE_DIR}/data/fixtures/cboe_manual.toml)
add_test(NAME cboe_manual_samples
  COMMAND pairing_tests fixture ${CMAKE_SOURCE_DIR}/data/fixtures/cboe_manual_samples.toml)
add_test(NAME solver COMMAND pairing_tests solver)
add_test(NAME exhaustive COMMAND pairing_tests exhaustive 1000)

# Phase 3 benchmarks: build/pairing_bench > docs/benchmarks.md regenerates every table.
add_executable(pairing_bench bench/bench.cpp)
target_include_directories(pairing_bench PRIVATE tests)
target_link_libraries(pairing_bench PRIVATE pairing)
target_compile_options(pairing_bench PRIVATE -Wall -Wextra -Wpedantic)

# HiGHS is a test-only oracle (spec §3.4): linked into this test binary, never into the library.
find_package(highs 1.16 CONFIG)
if(highs_FOUND)
  add_executable(pairing_highs_tests tests/highs.cpp)
  target_link_libraries(pairing_highs_tests PRIVATE pairing highs::highs)
  target_link_libraries(pairing_bench PRIVATE highs::highs)
  target_compile_definitions(pairing_bench PRIVATE PAIRING_BENCH_HIGHS)
  target_compile_options(pairing_highs_tests PRIVATE -Wall -Wextra -Wpedantic)
  # Phase 2 criteria (docs/plan.md): 1,000 portfolios of up to 40 series within 1% of HiGHS,
  # and five large ones of 50 to 200 series within 1% and 30 s each. HiGHS is slow on two of
  # the large ones (about 170 s), so that test takes about six minutes.
  add_test(NAME highs COMMAND pairing_highs_tests 1000 40)
  add_test(NAME highs_large COMMAND pairing_highs_tests large)
  set_tests_properties(highs_large PROPERTIES TIMEOUT 900)
else()
  message(STATUS "HiGHS not found: the differential test against it is skipped")
endif()
