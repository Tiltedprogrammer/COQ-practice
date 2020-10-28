#include <prop_parser.h>
#include <CNFTransformer.h>



int main(int argc, char const *argv[])
{
    
    auto f = Proposition(std::string("~ ((1 & 2) | ~ 3)"));

    std::cout << *f.get() << std::endl;
    
    return 0;
}
