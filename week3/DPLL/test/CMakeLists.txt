# #TESTS


add_executable(test1 test.cpp ../cpp/CNF.cpp ../cpp/prop_parser.cpp ../cpp/DPLL.cpp)
target_link_libraries(test1 gtest)
target_link_libraries(test1 gtest_main)

add_test(NAME test1
         COMMAND test1)