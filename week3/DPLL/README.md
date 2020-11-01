# Yet another DPLL in C++

## Propositional formulas could be parsed using `int` for atoms (except `0`) and `~` `&` `|` standing for `\neg`, `\wedge`, and `\vee` respectively.
```CPP
//Retunrn unique_ptr to abstact class formula
auto f = Proposition(std::string("~ 1 & 1"));

//pretty prints the formula
std::cout << *f.get() << std::endl;
```

## Formulas could be transformed to CNF using Tseitin transformation

```CPP
//transforms the formula to CNF via Tseitin
    //or loads DIMACS through @istream
auto f_cnf = CNFTransformer(f.get());
//or
std::ifstream is("path/to/DIMACS");
auto f_cnf = CNFTransformer(is);
```

##  

```CPP
//DPLL solver
auto solver = DPLL_solver();
    
//add signle clause such as @std::set<int> or many clauses at once
    // @std::set<std::set<int>>
solver.add_clause(f_cnf.get_cnf());
//or
solver.add_clause(std::set<int>({1,-1}))

assert(solver.solve() == UNSAT);
```

## Project structure

    .
    ├── cpp                         # cpp sourses
    |   ├── CNF.cpp                 # Tseitin's transformation
    |   ├── DPLL.cpp                # DPLL solver
    |   ├── main.cpp                # main example + clique
    |   └── prop_parser.cpp         # prop formula parser               
    ├── build                       # convenient directory to place build files
    ├── CppCmb                      # CPP parser combinator library submodule 
    ├── DIMACS                      # DIMACS example
    |    
    ├── include                     # include headers
    │   ├── ...
    |   └── formula.h               # Prop formula representation 
    ├── test                        # test dir 
    |   ├── test_dataset            # DIMACS data for test.cpp
    |   ├── ...
    |   ├── crop.py                 # crops last 4 lines in DIMACS
    |   ├── test.cpp                # test sources
    |   └── test.py                 # python SAT for DIMACS
    |                               # test folder
    ├── CMakeLists.txt              # main CMake
    ├── CMakeLists.txt.in           # CMake for google-tests         `
    └── README.md                   # this README

## Build instructions
```bash
mkdir build && cd build && cmake .. && make
./cpp/sat_solver
```