/**
 * verify.cpp
 * @author kisslune 
 */

#include "Z3Mgr.h"

using namespace z3;
using namespace SVF;


/* A simple example

int main() {
    int* p;
    int q;
    int* r;
    int x;

    p = malloc();
    q = 5;
    *p = q;
    x = *p;
    assert(x==5);
}
*/
void Z3Tests::test0()
{
    //  int* p;
    expr p = getZ3Expr("p");
    //  int q;
    expr q = getZ3Expr("q");
    //  int* r;
    expr r = getZ3Expr("r");
    //  int x;
    expr x = getZ3Expr("x");
    //  p = malloc();
    addToSolver(p == getMemObjAddress("malloc"));
    //  q = 5;
    addToSolver(q == 5);
    //  *p = q;
    storeValue(p, q);
    //  x = *p;
    addToSolver(x == loadValue(p));

    // print the expression values
    printExprValues();

    addToSolver(x == getZ3Expr(10));
    // print the result of satisfiability check
    std::cout << solver.check() << std::endl;
}


/*
// Simple integers

    int main() {
        int a;
        int b;
        a = 0;
        b = a + 1;
        assert(b > 0);
    }
*/
void Z3Tests::test1()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    
    // a = 0;
    addToSolver(a == 0);
    // b = a + 1;
    addToSolver(b == a + 1);
    
    // assert(b > 0);
    addToSolver(b > 0);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
  // One-level pointers

    int main() {
        int* p;
        int q;
        int b;
        p = malloc;
        *p = 0;
        q = *p;
        *p = 3;
        b = *p + 1;
        assert(b > 3);
    }
*/
void Z3Tests::test2()
{
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr b = getZ3Expr("b");

    // p = malloc;
    addToSolver(p == getMemObjAddress("malloc"));
    
    // *p = 0;
    // FIX: Convert 0 to z3 expression
    storeValue(p, ctx.int_val(0));
    
    // q = *p;
    addToSolver(q == loadValue(p));
    
    // *p = 3;
    // FIX: Convert 3 to z3 expression
    storeValue(p, ctx.int_val(3));
    
    // b = *p + 1;
    addToSolver(b == loadValue(p) + 1);
    
    // assert(b > 3);
    addToSolver(b > 3);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
    // Mutiple-level pointers

    int main() {
        int** p;
        int* q;
        int* r;
        int x;

        p = malloc1(..);
        q = malloc2(..);
        *p = q;
        *q = 10;
        r = *p;
        x = *r;
        assert(x==10);
    }
*/
void Z3Tests::test3()
{
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr x = getZ3Expr("x");

    // p = malloc1(..);
    addToSolver(p == getMemObjAddress("malloc1"));
    // q = malloc2(..);
    addToSolver(q == getMemObjAddress("malloc2"));
    
    // *p = q;
    storeValue(p, q);
    
    // *q = 10;
    // FIX: Convert 10 to z3 expression
    storeValue(q, ctx.int_val(10));
    
    // r = *p;
    addToSolver(r == loadValue(p));
    
    // x = *r;
    addToSolver(x == loadValue(r));
    
    // assert(x==10);
    addToSolver(x == 10);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
   // Array and pointers

    int main() {
        int* p;
        int* x;
        int* y;
        int a;
        int b;
        p = malloc;
        x = &p[0];
        y = &p[1]
        *x = 10;
        *y = 11;
        a = *x;
        b = *y;
        assert((a + b)>20);
    }
*/
void Z3Tests::test4()
{
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");

    // p = malloc;
    addToSolver(p == getMemObjAddress("malloc"));
    
    // x = &p[0];
    addToSolver(x == getGepObjAddress(p, 0));
    
    // y = &p[1];
    addToSolver(y == getGepObjAddress(p, 1));
    
    // *x = 10;
    // FIX: Convert 10 to z3 expression
    storeValue(x, ctx.int_val(10));
    
    // *y = 11;
    // FIX: Convert 11 to z3 expression
    storeValue(y, ctx.int_val(11));
    
    // a = *x;
    addToSolver(a == loadValue(x));
    
    // b = *y;
    addToSolver(b == loadValue(y));
    
    // assert((a + b)>20);
    addToSolver((a + b) > 20);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
    // Branches

int main(int argv) {
    int a;
    int b;
    int b1;
    a = argv + 1;
    b = 5;
    if(a > 10)
        b = a;
    b1 = b;
    assert(b1 >= 5);
}
*/
void Z3Tests::test5()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");   // Represents initial b
    expr b1 = getZ3Expr("b1"); // Represents final b
    expr argv = getZ3Expr("argv");

    // a = argv + 1;
    addToSolver(a == argv + 1);
    
    // b = 5; (initial)
    addToSolver(b == 5);
    
    // if(a > 10) b = a;
    // Model using ite: final_val = ite(cond, true_branch_val, false_branch_val)
    expr b_final = ite(a > 10, a, b);
    
    // b1 = b; (which is b_final)
    addToSolver(b1 == b_final);
    
    // assert(b1 >= 5);
    addToSolver(b1 >= 5);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
// Compare and pointers
int main() {
   int *a = malloc1;
   int *b = malloc2;
   *a = 5;
   *b = 10;
   int *p;
   if (*a < *b) {
       p = a;
   } else {
       p = b;
   }
   assert(*p == 5);
}
*/
void Z3Tests::test6()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr p = getZ3Expr("p");

    // int *a = malloc1;
    addToSolver(a == getMemObjAddress("malloc1"));
    // int *b = malloc2;
    addToSolver(b == getMemObjAddress("malloc2"));
    
    // *a = 5;
    // FIX: Convert 5 to z3 expression
    storeValue(a, ctx.int_val(5));
    // *b = 10;
    // FIX: Convert 10 to z3 expression
    storeValue(b, ctx.int_val(10));
    
    // Condition: *a < *b
    expr cond = loadValue(a) < loadValue(b);
    
    // if (...) p = a else p = b
    addToSolver(p == ite(cond, a, b));
    
    // assert(*p == 5);
    addToSolver(loadValue(p) == 5);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
 int main() {
    int a = 1, b = 2, c = 3;
    int d;
  if (a > 0) {
    d = b + c;
  }
  else {
    d = b - c;
  }
  assert(d == 5);
 }
 */
void Z3Tests::test7()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr c = getZ3Expr("c");
    expr d = getZ3Expr("d");

    // int a = 1, b = 2, c = 3;
    addToSolver(a == 1);
    addToSolver(b == 2);
    addToSolver(c == 3);
    
    // if (a > 0) d = b + c else d = b - c
    addToSolver(d == ite(a > 0, b + c, b - c));
    
    // assert(d == 5);
    addToSolver(d == 5);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
 int main() {
    int arr[2] = {0, 1};
    int a = 10;
    int *p;
    if (a > 5) {
        p = &arr[0];
    }
    else {
        p = &arr[1];
    }
    assert(*p == 0);
 }
 */
void Z3Tests::test8()
{
    // Model 'arr' as a memory object
    expr arr = getMemObjAddress("arr");
    expr a = getZ3Expr("a");
    expr p = getZ3Expr("p");

    // int arr[2] = {0, 1};
    // FIX: Convert values to z3 expression
    storeValue(getGepObjAddress(arr, 0), ctx.int_val(0));
    storeValue(getGepObjAddress(arr, 1), ctx.int_val(1));
    
    // int a = 10;
    addToSolver(a == 10);
    
    // if (a > 5) p = &arr[0] else p = &arr[1]
    expr addr0 = getGepObjAddress(arr, 0);
    expr addr1 = getGepObjAddress(arr, 1);
    addToSolver(p == ite(a > 5, addr0, addr1));
    
    // assert(*p == 0);
    addToSolver(loadValue(p) == 0);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
    // Struct and pointers

    struct A{ int f0; int* f1;};
    int main() {
       struct A* p;
       int* x;
       int* q;
       int** r;
       int* y;
       int z;

       p = malloc1;
       x = malloc2;
       *x = 5;
       q = &(p->f0);
       *q = 10;
       r = &(p->f1);
       *r = x;
       y = *r;
       z = *q + *y;
       assert(z == 15);
    }
*/
void Z3Tests::test9()
{
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr y = getZ3Expr("y");
    expr z = getZ3Expr("z");

    // p = malloc1; x = malloc2;
    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(x == getMemObjAddress("malloc2"));
    
    // *x = 5;
    // FIX: Convert 5 to z3 expression
    storeValue(x, ctx.int_val(5));
    
    // q = &(p->f0);  (Offset 0)
    addToSolver(q == getGepObjAddress(p, 0));
    
    // *q = 10;
    // FIX: Convert 10 to z3 expression
    storeValue(q, ctx.int_val(10));
    
    // r = &(p->f1); (Offset 1, assuming fields are int sized slots in this abstract model)
    addToSolver(r == getGepObjAddress(p, 1));
    
    // *r = x;
    storeValue(r, x);
    
    // y = *r;
    addToSolver(y == loadValue(r));
    
    // z = *q + *y;
    // Note: y is a pointer (x), so *y means loadValue(y)
    addToSolver(z == loadValue(q) + loadValue(y));
    
    // assert(z == 15);
    addToSolver(z == 15);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
int foo(int z) {
    k = z;
    return k;
}
int main() {
  int x;
  int y;
  y = foo(2);
  x = foo(3);
  assert(x == 3 && y == 2);
}
*/
void Z3Tests::test10()
{
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    
    // Function foo(z) essentially returns z. 
    // We model the return values directly.
    
    // y = foo(2); -> returns 2
    addToSolver(y == 2);
    
    // x = foo(3); -> returns 3
    addToSolver(x == 3);
    
    // assert(x == 3 && y == 2);
    addToSolver(x == 3 && y == 2);

    printExprValues();
    std::cout << solver.check() << std::endl;
}


int main()
{
    Z3Tests tests;
    tests.test0();
    tests.resetSolver();
    tests.test1();
    tests.resetSolver();
    tests.test2();
    tests.resetSolver();
    tests.test3();
    tests.resetSolver();
    tests.test4();
    tests.resetSolver();
    tests.test5();
    tests.resetSolver();
    tests.test6();
    tests.resetSolver();
    tests.test7();
    tests.resetSolver();
    tests.test8();
    tests.resetSolver();
    tests.test9();
    tests.resetSolver();
    tests.test10();

    return 0;
}
