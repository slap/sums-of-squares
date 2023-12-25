# Uncomment and set the path to rationalSOS.mpl file
#currentdir("C:/Users/User/rationalSOS");

#######################################################################
# Load "Rational SOS" procedures
#######################################################################
read("rationalSOS.mpl");
with(rationalSOS);

# Display tables of any size
interface(rtablesize=infinity);

#######################################################################
# Example 2.1 in [1]
#######################################################################

# We define a polynomial f as the sum of two squares.
p1 := x^2 + 3*x*y - 5*x*z+ 2z^2;
p2 := 3x^2 - 2*x*z +y*z+5*y^2;
f := expand(p1^2 + p2^2);

# Compute the matrix Q associated to the problem
Q, QVars, v := polyToMatrix(f);

# Dimension and rank of Q
nops(indets(Q));
randomRank(Q);

# Computes numerically a SDP solution using SEDUMI
xSol := numericSolver(Q);

# Solution matrix and eigenvalues
Qsol := evalMat(Q, QVars, xSol):
eig(Qsol);

# Four positive eigenvalues and two approximate zeros

#######################################################################


#######################################################################
# Example 3.2 in [1]
#######################################################################

sSym := solve({f=0, diff(f, x)=0, diff(f,y)=0, diff(f,z)=0});

## sSym[1] plain equation
v0 := eval(Vector(v), sSym);
v01 := eval(v0, {x = 1}):

# We verify that it satisfies the condition vt.Q.v = 0, which must always
# be satisfied for real solutions
simplify(LinearAlgebra[Transpose](v01).Q.v01);

# We reduce the dimension
Q1 := reduceByLinearEquation(Q, v01):
nops(indets(Q1));
randomRank(Q1);
# We reduced the dimension to 5 but we need to reduce to 4, 
# because the numerical solution had 2 null eigenvalues

v01t := vectorTrace(v01);

# We took the trace, so the equation vt.Q.v=0 may not be satisfied
simplify(LinearAlgebra[Transpose](v01t).Q.v01t);

Q1 := reduceByLinearEquation(Q, v01t):
nops(indets(Q1));
randomRank(Q1);

# The problem was completely solved, no need to call the numerical solver.

L, DD, Lt, fNew, a, p := matrixToPoly(Q1, v):
fNew;

