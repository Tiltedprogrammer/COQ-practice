# #TESTS


add_executable(test1 test.cpp)
target_link_libraries(test1 gtest)
target_link_libraries(test1 gtest_main)
target_link_libraries(test1 DPLL)

add_test(NAME test1
         COMMAND test1)