from pysat.formula import CNF
from pysat.solvers import MapleCM

if __name__ == "__main__":
    
    f1 = CNF(from_file='/home/alexey.tyurin/MATH_LOGIC/Math-logic-practice/week3/DPLL/test/test_dataset/sat/uf50-0584.cnf-cropped')  # reading from file
    # print(len(f1.clauses))
    solver = MapleCM()
    solver.append_formula(f1.clauses)
    print(solver.solve())
