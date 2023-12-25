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
# Example 3.3 in [1]
#######################################################################

# Constructin of f. We begin with generic polynomials in Q(alpha),
# alpha a root of Z^4-3.
mp := t^4-3; 
p1 := d1*t^3+c1*t^2+b1*t+a1; 
p2 := d2*t^3+c2*t^2+b2*t+a2; 
p3 := d3*t^3+c3*t^2+b3*t+a3; 

# We rename some variables and impose some relations between the coefficients 
# to decrease the dimension of the problem
b1 := x; d2 := z; c3 := y;
b2 := 3*x; c2 := x+c1; c1 := d1-x; b3 := 2*x; d1 := 2*z; d3 := d1+x;
fGeneric := p1^2+p2^2+p3^2; 
fGeneric := expand(fGeneric);

# We solve the coefficients a1 and a2 so that the polynomial is in Q,
f2 := NormalForm(fGeneric, [mp], plex(a1, a2, a3, x,y,z, t)); 
f3 := collect(f2, t); 
lz := CoefficientList(f3, t); 
ss := solve({lz[2], lz[3],lz[4]}, {a1, a2, a3});

# We plug in the solutions found for a1 and a2
ssDen := denom(rhs(ss[1])); 
p1s := simplify(subs(ss, p1)*ssDen); 
p2s := simplify(subs(ss, p2)*ssDen); 
p3s := simplify(subs(ss, p3)*ssDen);

p1ss := subs({t = RootOf(x^4-3)}, p1s); 
p2ss := subs({t = RootOf(x^4-3)}, p2s); 
p3ss := subs({t = RootOf(x^4-3)}, p3s); 

# Starting polynomial, it is a polynomial in Q[x,y,z]
f := simplify(p1ss^2+p2ss^2+p3ss^2);

# Compute the matrix Q associated to the problem
Q, QVars, v := polyToMatrix(f);

# Dimension and rank of Q
nops(indets(Q));
randomRank(Q);

# Computes numerically a SDP solution using SEDUMI
xVars, xSol := numericSolver(Q):

# Solution matrix and eigenvalues
Qsol := evalMat(Q, xVars, xSol):
eig(Qsol);

# Ten positive eigenvalues and five approximate zeros

##########################################################################

# Matrix associated to the original decomposition
MNEW := decompositionToMatrix([p1ss, p2ss, p3ss], v);

############################################
##  STEP BY STEP
############################################

# Real solutions
sSym := solve({f=0, diff(f, x)=0, diff(f,y)=0, diff(f,z)=0});

############################################

## sSym[1] plain equation
v1 := eval(Vector(v), sSym[1]);
v11 := eval(v1, {y = 1}):

# We verify that it satisfies the condition vt.Q.v = 0, which must always
# be satisfied for real solutions
simplify(LinearAlgebra[Transpose](v11).Q.v11);

# We reduce the dimension
Q1 := reduceByLinearEquation(Q, v11):
nops(indets(Q1));
randomRank(Q1); # 14

############################################

## sSym[2] plain equation
v2 := eval(Vector(v), sSym[2]);
v21 := eval(v2, {z = 1}):

# We verify that it satisfies the condition vt.Q.v = 0, which must always
# be satisfied for real solutions
simplify(LinearAlgebra[Transpose](v21).Q.v21);

# We reduce the dimension
Q2 := reduceByLinearEquation(Q1, v21):
nops(indets(Q2));
randomRank(Q2); # 13

############################################

## sSym[3] trace equation
v3 := eval(Vector(v), sSym[3]);
v31 := eval(v3, {x=1}):
v31t := vectorTrace(v31);

Q3 := reduceByLinearEquation(Q2, v31t):
nops(indets(Q3));
randomRank(Q3); # 12

############################################

# Equations from zeros in the diagonal
Q4 := zeroRows(Q3):
nops(indets(Q4));
randomRank(Q4); # 10

############################################

MMT, tVars, vSol := numericSolverSubmatrix(Q4, 10):
vSolR := roundVec(vSol, 15);
QSol := evalMat(Q4, tVars, vSolR):
evalf(LinearAlgebra[Eigenvalues](QSol));
# 5 exact null eigenvalues and 4 approximate null eigenvalues

############################################

# sSym[3] plain equations - reduction to rank 9
Q5 := reduceByLinearEquation(Q4, v31):
nops(indets(Q5));
randomRank(Q5); # 9

############################################

# We force the entries of Q5 to be rational expressions
Q5Prim := primitiveMatrix(Q5):
L := getExtension(Q5Prim);
Q6 := nonRatCoef(Q5Prim, 15, L):

nops(indets(Q6));
randomRank(Q6); # 6

MMT, tVars, vSol := numericSolverSubmatrix(Q6, 6);  
vSolR := roundVec(vSol, 1):
Q6Sol := evalMat(Q6, tVars, vSolR):
eigval := LinearAlgebra[Eigenvalues](Q6Sol):
evalf(eigval);
# 9 exact null eigenvalues

# Verification
L, DD, Lt, fSol, a, p := matrixToPoly(Q6Sol,v):
fSol;
simplify(f-fSol);



