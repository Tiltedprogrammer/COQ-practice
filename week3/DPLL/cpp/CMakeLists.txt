

add_library(DPLL STATIC CNF.cpp prop_parser.cpp DPLL.cpp)

add_executable(sat_solver main.cpp)
target_link_libraries(sat_solver DPLL)
