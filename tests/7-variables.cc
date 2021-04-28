/******************************************************************************
                     Compiler Construction - Project 1
                        Test for Variable Qualifieres
*******************************************************************************/

#include <iostream>

using std;


int main()
{
    // should parse according to DOMjudge test 68
    const constinit int uninitialized;
    // should be valid 
    int & & & & & multipleRefOperators;
    return 0;
}