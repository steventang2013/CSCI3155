# Lab 1

Edward Zhu; Partner - Steven Tang

### 1. Scala Basics: Bindings and Scope
**a.** The use of x at line 4 in bound at line 3, pi = 3.14159, because it is within the scope of the circumference function. The use of x at line 7 in bound at line 1, pi = 3.14, because it is outside the method of circumference and is in the scope of line 1.

**b.** The use of x at line 3 in bound at line 2, because the value will always match the integer in the f(x: Int). The use of x at line 6 in bound at line 5, because it's value will always match the case statement, but not at line 2 because if x is zero, it will hit the case for 0. The use of x at line 10 is bound to line 5, because it is in the same scope as x in line 6, thus bounded to the same line 5. The use of x at line 13 in bound to line 1 because it is in the same scope and doesn't reliant on the f(x: Int) function.

### 2. Scala Basics: Typing
Yes, the body of g is well-typed because it will return a tuple of ((Int, Int), Int), as b is a tuple of form (Int, Int) and the returned value would also be a tuple with b as one of its variables.

	if (x == 0) : ((Int, Int), Int) because
		b : (Int, Int) because
			x : Int
			3 : Int
		1 : Int
	else : ((Int, Int), Int) because
		b : (Int, Int) because
			x : Int
			3 : Int
		a + 2 : Int because
			a : Int
			2 : Int

### Scala exercices

To run the auto-grader:

	sbt "project lab1-grader" run