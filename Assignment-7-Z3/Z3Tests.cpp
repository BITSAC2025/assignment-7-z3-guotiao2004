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
    storeValue(p, ctx.int_val(0));
    
    // q = *p;
    addToSolver(q == loadValue(p));
    
    // *p = 3;
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
    addToSolver(x == p);
    
    // y = &p[1];
    addToSolver(y == p + 1);
    
    // *x = 10;
    storeValue(x, ctx.int_val(10));
    
    // *y = 11;
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
    expr argv = getZ3Expr("argv");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr b1 = getZ3Expr("b1");

    // a = argv + 1;
    addToSolver(a == argv + 1);
    
    // b = 5; (initial value logic)
    // if(a > 10) b = a; else b = 5;
    addToSolver(b == ite(a > 10, a, ctx.int_val(5)));
    
    // b1 = b;
    addToSolver(b1 == b);
    
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
    storeValue(a, ctx.int_val(5));
    // *b = 10;
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
    // Step 1: Capture the array variable
    expr arr = getZ3Expr("arr");
    expr a = getZ3Expr("a");
    expr p = getZ3Expr("p");

    // Step 2: Calculate GEP addresses BEFORE converting arr to a constant address
    // This works because arr is still a named variable "arr" in the map here.
    expr addr0 = getGepObjAddress(arr, 0);
    expr addr1 = getGepObjAddress(arr, 1);
    
    // Step 3: Constrain 'arr' to be the physical address.
    // getMemObjAddress("arr") assigns the address constant to the name "arr".
    // We bind our 'arr' variable to this address so that addr0 (which is 'arr') becomes a valid address.
    addToSolver(arr == getMemObjAddress("arr"));

    // Now we can safely store
    storeValue(addr0, ctx.int_val(0));
    storeValue(addr1, ctx.int_val(1));
    
    // int a = 10;
    addToSolver(a == 10);
    
    // if (a > 5) p = &arr[0] else p = &arr[1]
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

    // We must handle 'malloc1' carefully to avoid address collision with 'malloc2'
    // when accessing field f1 (offset 1).
    // Use the same pattern as test8:
    
    // 1. Get the object variable
    expr m1 = getZ3Expr("malloc1");
    
    // 2. Get safe GEP addresses (which will be far away from malloc2 ID)
    expr f0 = getGepObjAddress(m1, 0);
    expr f1 = getGepObjAddress(m1, 1);
    
    // 3. Constrain m1 to its address
    addToSolver(m1 == getMemObjAddress("malloc1"));

    // p = malloc1
    addToSolver(p == m1);
    
    // x = malloc2
    addToSolver(x == getMemObjAddress("malloc2"));
    
    // *x = 5;
    storeValue(x, ctx.int_val(5));
    
    // q = &(p->f0) -> q = f0
    addToSolver(q == f0);
    
    // *q = 10;
    storeValue(q, ctx.int_val(10));
    
    // r = &(p->f1) -> r = f1
    addToSolver(r == f1);
    
    // *r = x;
    storeValue(r, x);
    
    // y = *r;
    addToSolver(y == loadValue(r));
    
    // z = *q + *y;
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
    
    // Function calls modeled by return values
    addToSolver(y == 2);
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
