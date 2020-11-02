#include <prop_parser.h>
#include <CNFTransformer.h>
#include <DPLL.h>
#include <cassert>
#include <map>
#include <vector>
#include <algorithm>

enum MINER_RESULT {BOOM, SAFE};

std::ostream& operator<<(std::ostream& out, const MINER_RESULT value) {
    const char* s = 0;
#define PROCESS_VAL(p) case(p): s = #p; break;
    switch(value){
        PROCESS_VAL(BOOM);     
        PROCESS_VAL(SAFE);     
    }
#undef PROCESS_VAL

    return out << s;
}

typedef std::vector<std::vector<char>> Field;

class MineSweeper
{
private:
    DPLL_solver solver = DPLL_solver();
    int width;
    int height;

    std::vector<std::vector<int>> comb(int K,std::vector<int>& neighbours);
    void area_is_safe(int i, int j, int n, int w, int h);

public:
    MineSweeper(Field& field);

    MineSweeper(const MineSweeper& ms) {
        solver = ms.solver;
        width = ms.width;
        height = ms.height;
    }
    MineSweeper operator=(const MineSweeper& ms) {
        solver = ms.solver;
        width = ms.width;
        height = ms.height;
    }

    MINER_RESULT query(int i, int j);

    ~MineSweeper() = default;
};

MineSweeper::MineSweeper(Field& field) {

    assert(!field.empty());
    assert(!field[0].empty());

    height = (int)field.size();
    width = (int)field[0].size();
    for(auto e : field) { 
        assert(e.size() == width);
    }
    //every cell on the edge is safe, i.e. \neg p_{i,j};
    for(int i = 0; i < width + 2; i++) {
        solver.add_clause(std::set<int>({-(i+1)}));//first row
        solver.add_clause(std::set<int>({-((width + 2) * (height + 1) + i + 1)}));//last row
    }

    for(int i = 0; i < height + 2; i++) {
        solver.add_clause(std::set<int>({-(i * (width + 2) + 1)}));//first col
        solver.add_clause(std::set<int>({-(i * (width + 2) + width + 2)}));//last col
    }

    for (int i = 0; i < height; i++) {
        for (int j = 0; j < width; j++) {

            auto cell = field[i][j];
            
            if (cell == 'b') {
                solver.add_clause(std::set<int>({((i+1) * (width + 2)) + (j + 1) + 1}));

            } 
            else if ((cell - '0') <= 8 && (cell - '0') >= 0) {
                //the cell itself is safe
                solver.add_clause(std::set<int>({-((i+1) * (width + 2) + (j + 1) + 1)}));
                area_is_safe(i+1, j+1,cell-'0',width + 2, height + 2);
            } 
        }
    }


}


std::vector<std::vector<int>>  MineSweeper::comb(int K,std::vector<int>& neighbours) {
    std::string bitmask(K, 1); // K leading 1's
    bitmask.resize(8, 0); // N-K trailing 0's
    
    auto result = std::vector<std::vector<int>>();
    // print integers and permute bitmask
    do {
        auto res_local = std::vector<int>();
        for (int i = 0; i < 8; ++i) // [0..N-1] integers
        {
            if (bitmask[i]) res_local.push_back(neighbours[i]);
            else res_local.push_back(-neighbours[i]);
            
        }
        result.push_back(res_local);
    } while (std::prev_permutation(bitmask.begin(), bitmask.end()));

    return result;

}

//constraints for neighbours of {i,j} cell
void MineSweeper::area_is_safe(int i, int j, int n, int w, int h) {

    std::string clause;
    std::vector<int> neigbours;

    neigbours.push_back((i+1) * w + j + 1);
    neigbours.push_back((i-1) * w + j + 1);
    neigbours.push_back((i * w) + j + 1 + 1);
    neigbours.push_back((i * w) + j - 1 + 1);

    neigbours.push_back((i+1) * w + j + 1 + 1);
    neigbours.push_back((i-1) * w + j + 1 + 1);
    neigbours.push_back((i+1) * w + j - 1 + 1);
    neigbours.push_back((i-1) * w + j - 1 + 1);

    auto combs = comb(n,neigbours);
    
    for(auto& c : combs) {
        std::string clausee = "(";
        for(auto i : c) {
            if (i < 0) {
                clausee += "~";
                clausee += std::to_string(std::abs(i));
            } else clausee += std::to_string(i);
            clausee += " & ";
        }
        clausee.pop_back();
        clausee.pop_back();
        clausee += ")";
        clause += clausee;
        clause += " | ";
    }
    clause.pop_back();
    clause.pop_back();

    solver.add_clause(clause);

}


MINER_RESULT MineSweeper::query(int i, int j) {
    
    assert(i >= 0 && i <= height);
    assert(j >= 0 && j <= width);

    solver.add_clause(std::set<int>({(i + 1) * (width + 2) + j + 2}));

    auto verdict = solver.solve();
    solver.remove_clause(std::set<int>({(i + 1) * (width + 2) + j + 2}));
    // std::cout << solver << std::endl;

    switch (verdict)
    {
    case UNSAT:
        return SAFE;
        break;
    case SAT:
        return BOOM;
        break;
    default:
        break;
    }


}


int main(int argc, char const *argv[]) {   
    auto field = std::vector<std::vector<char>>();
    field.push_back(std::vector<char>({'0','1','?','1','0','0','0','1','?'}));
    field.push_back(std::vector<char>({'0','1','?','1','0','0','0','1','1'}));
    field.push_back(std::vector<char>({'0','1','1','1','0','0','0','0','0'}));
    field.push_back(std::vector<char>({'0','0','0','0','0','0','0','0','0'}));
    field.push_back(std::vector<char>({'1','1','1','1','1','0','0','1','1'}));
    field.push_back(std::vector<char>({'?','?','?','?','1','0','0','1','?'}));
    field.push_back(std::vector<char>({'?','?','?','?','3','1','0','1','?'}));
    field.push_back(std::vector<char>({'?','?','?','?','?','2','1','1','?'}));
    field.push_back(std::vector<char>({'?','?','?','?','?','?','?','?','?'}));

    auto solver = MineSweeper(field);

    //All safe
    std::cout << solver.query(0,0) << std::endl;
    std::cout << solver.query(0,2) << std::endl;
    std::cout << solver.query(5,1) << std::endl;
    std::cout << solver.query(5,2) << std::endl;
    std::cout << solver.query(6,3) << std::endl;
    std::cout << solver.query(6,8) << std::endl;
    std::cout << solver.query(7,8) << std::endl;
    
    return 0;
}
