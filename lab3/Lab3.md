# Lab 2

*Steven Tang, John Zavidniak*

### 1. Dynamic vs Static Scoping
	
	
**a.**	


	const b = 5;
	def foo()
	{
   		var a = b + 5;
   		return a;
	}
 
	def bar()
	{
   		var b = 2;
   		return foo();
	}
 

   	foo(); // returns 10
   	bar(); 
	
Returns (10, 10) in lexical scoping, but (10, 7) in dynamic scoping.
In lexical scoping, if a variable name's scope is a certain function, then its scope is the
text of the function definition: within that text, the variable name exists, and is bound to 
the variable's value, but outside that text, the variable name does not exist.
By contrast, in dynamic scoping (or dynamic scope), if a variable name's scope is a certain 
function, then its scope is the time-period during which the function is executing


### 2. Write UP


**c.** Yes, the evaluation order is deterministic because the grammar generates a unique parse tree.


### 3. Evaluation Order

e1 is evaluated first, followed by e2. The judgment form computes toNumber(e1) before toNumber(e2).
We can change the rules by writing the evaluation of e2 before writing the evaluation of e1.

### 4. 

**a.**

if (obj != 0 && obj == 5){
	do Something;
}
This short circuits because if the first expression (obj != 0) evaluates to be false, the second
expression (obj == 5) wouldn't even be looked at because the entire if expression would already
be false.

**b.**
Yes, DoAndFalse short circuits because if the first expression is false, then the entire expression
returns false.