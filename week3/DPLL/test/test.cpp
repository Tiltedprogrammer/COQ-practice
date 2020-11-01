#include "gtest/gtest.h"
#include "DPLL.h"
#include <prop_parser.h>
#include <CNFTransformer.h>
#include <filesystem>

namespace fs = std::filesystem;



struct TestDIMACS{
    public: 
        std::vector<std::string> cnf_paths;
        explicit TestDIMACS(std::string path_to_directory);
};

TestDIMACS::TestDIMACS(std::string path_to_directory){
    cnf_paths = std::vector<std::string>();
    for (const auto & entry : fs::directory_iterator(path_to_directory))
        cnf_paths.push_back(entry.path());
}


TEST(TestForTest, TestOne){
    ASSERT_EQ(1,1);
}

TEST(DPLL_TESTS,FALSE_IS_UNSAT){

    auto f = Proposition(std::string("~ 1 & 1"));
    auto f_cnf = CNFTransformer(f.get());
    auto solver = DPLL_solver();
    solver.add_clause(f_cnf.get_cnf());
    
    ASSERT_EQ(solver.solve(),UNSAT);
    


}


TEST(DPLL_TESTS,TRUE_IS_SAT){
    
    auto f = Proposition(std::string("~ 1 | 1"));
    auto f_cnf = CNFTransformer(f.get());
    auto solver = DPLL_solver();
    solver.add_clause(f_cnf.get_cnf());
    
    ASSERT_EQ(solver.solve(), SAT);
    auto model = solver.get_model();
    ASSERT_EQ(solver.satisfies(model),SAT);
    


}

TEST(DPLL_TESTS, DIMACS_SAT) {
    TestDIMACS td("/home/alexey.tyurin/MATH_LOGIC/Math-logic-practice/week3/DPLL/test/test_dataset/sat");
    
    for (const auto& path : td.cnf_paths) {
        if(!fs::is_directory(path)){
            std::cout << "\033[0;32m" << "[          ] " << "\u001b[35m" 
                << "Launching test for "<< path << std::endl;
            std::ifstream is(path);
            auto cnf = CNFTransformer(is);
            auto solver = DPLL_solver();

            solver.add_clause(cnf.get_cnf());
            ASSERT_EQ(solver.solve(), SAT);
            
            auto model = solver.get_model();
            ASSERT_EQ(solver.satisfies(model), SAT);
        }
    }
}


TEST(DPLL_TESTS, DIMACS_UNSAT) {
    TestDIMACS td("/home/alexey.tyurin/MATH_LOGIC/Math-logic-practice/week3/DPLL/test/test_dataset/unsat");
    
    for (const auto& path : td.cnf_paths) {
        if(!fs::is_directory(path)){
            std::cout << "\033[0;32m" << "[          ] " << "\u001b[35m" 
                << "Launching test for "<< path << std::endl;
            std::ifstream is(path);
            auto cnf = CNFTransformer(is);
            auto solver = DPLL_solver();

            solver.add_clause(cnf.get_cnf());
            ASSERT_EQ(solver.solve(), UNSAT);
            
        }
    }
}

int main(int argc, char** argv) {
    
    testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();

}
