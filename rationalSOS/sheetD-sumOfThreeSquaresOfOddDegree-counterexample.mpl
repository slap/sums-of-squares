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
# Theorem 5.1
#######################################################################

# We define a polynomial z as the sum of three squares in an algebraic
# extension of degree 3 with generic coefficients.

mp := t^3-2; 
p1 := c1*t^2+b1*t+a1; 
p2 := c2*t^2+b2*t+a2; 
p3 := c3*t^2+b3*t+a3; 

# We impose some relations between the coefficients to decrease
# the dimension of the problem and rename the remaining variables
b2 := 3*b1;  c2 := b1+7*c1;  a3 := 3*c2-b2; 
b1 := x; b3 := y; c1 := z; c3 := w;

fGeneric := p1^2+p2^2+p3^2; 
fGeneric := expand(fGeneric);


# We solve the coefficients a1 and a2 so that the polynomial is in Q,
f2 := NormalForm(fGeneric, [mp], plex(a1, a2, x, y, z, w, t)); 
f3 := collect(f2, t); 
lf := CoefficientList(f3, t); 
ss := solve({lf[2], lf[3]}, {a1, a2});

# We plug in the solutions found for a1 and a2 and compute the resulting polynomial
ssDen := denom(rhs(ss[1])); 
p1s := simplify(subs(ss, p1)*ssDen); 
p2s := simplify(subs(ss, p2)*ssDen); 
p3s := simplify(subs(ss, p3)*ssDen);

p1ss := subs({t = RootOf(x^3-2)}, p1s); 
p2ss := subs({t = RootOf(x^3-2)}, p2s); 
p3ss := subs({t = RootOf(x^3-2)}, p3s); 

f := simplify(p1ss^2+p2ss^2+p3ss^2);

# We verify that the polynomial is absolutely irreducible
evala(AIrreduc(f));

# Matrix Q associated to the problem (parametrization of the space L)
Q, QVars, v := polyToMatrix(f):

# Matrix associated to the original decomposition
MNEW := decompositionToMatrix([p1ss, p2ss, p3ss], v):


#-----------------------------------

# We start from Q and go step by step.
nops(indets(Q));
randomRank(Q);

# Real solutions - In this problem, the system obtained by equating f and the partial derivatives 
# to 0 is too complicated for Maple solver. Using the starting polynomials we get a system that
# is easier to solve.
#sSym := solve({f=0, diff(f, x)=0, diff(f,y)=0, diff(f,z)=0, diff(f,w)=0, p1ss = 0, p2ss = 0, p3ss = 0});
sSym := solve({p1ss = 0, p2ss = 0, p3ss = 0});


## sSym[3] plain equations - reduction to 71 variables and rank 16
v3 := eval(Vector(v), sSym[3]);
v31 := eval(v3, {y=1, w=1}):
simplify(LinearAlgebra[Transpose](v31).Q.v31);
Q1 := reduceByLinearEquation(Q, v31):
nops(indets(Q1));
randomRank(Q1);

v32 := eval(v3, {y=1, w=0}):
simplify(LinearAlgebra[Transpose](v32).Q1.v32);
Q2 := reduceByLinearEquation(Q1, v32):
nops(indets(Q2));
randomRank(Q2);

v33 := eval(v3, {y=0, w=1}):
simplify(LinearAlgebra[Transpose](v33).Q2.v33);
Q3 := reduceByLinearEquation(Q2, v33):
nops(indets(Q3));
randomRank(Q3);

v34 := eval(v3, {y=-1, w=1}):
simplify(LinearAlgebra[Transpose](v34).Q3.v34);
Q4 := reduceByLinearEquation(Q3, v34):
nops(indets(Q4));
randomRank(Q4);

## Determinant equations - reduction to 29 variables and rank 12

Q5 := zeroRows(Q4):
nops(indets(Q5));
randomRank(Q5);

Q6 := zeroRows(Q5):
nops(indets(Q6));
randomRank(Q6);

Q7 := zeroDetSRows(Q6, 2):
nops(indets(Q7));
randomRank(Q7);

## sSym[1] plain equations - reduction to 8 variables and rank 9

v1 := eval(Vector(v), sSym[1]):
v11 := eval(v1, {x=1, w=1}):
evalf(allvalues(v11));
simplify(LinearAlgebra[Transpose](v11).Q.v11);
Q8 := reduceByLinearEquation(Q7, v11):
nops(indets(Q8));
randomRank(Q8);

v12 := eval(v1, {x=1, w=2}):
evalf(allvalues(v12));
simplify(LinearAlgebra[Transpose](v12).Q.v12);
Q9 := reduceByLinearEquation(Q8, v12):
nops(indets(Q9));
randomRank(Q9);

v13 := eval(v1, {x=1, w=3}):
evalf(allvalues(v13));
simplify(LinearAlgebra[Transpose](v13).Q.v13);
Q10 := reduceByLinearEquation(Q9, v13):
nops(indets(Q10));
randomRank(Q10);

## sSym[2] plain equations - reduction to 6 variables and rank 8

v2 := eval(Vector(v), sSym[2]);
v21 := eval(v2, {y=-3, z=1});
evalf(allvalues(v21));
simplify(LinearAlgebra[Transpose](v21).Q.v21);
Q11 := reduceByLinearEquation(Q10, v21):
nops(indets(Q11));
randomRank(Q11);

# CHECK IF MNEW IS SOLUTION - passed
eqs := Equate(Q11, MNEW):
solve(eqs);

## Determinant equations - reduction to 3 variables and rank 7

Q12 := zeroRows(Q11):
nops(indets(Q12));
randomRank(Q12);

# CHECK IF MNEW IS SOLUTION - passed
eqs := Equate(Q12, MNEW):
solve(eqs);

## sSym[4] plain equations
v4 := eval(Vector(v), sSym[4]);
v41 := eval(v4, {x=1});
evalf(allvalues(v41));
simplify(LinearAlgebra[Transpose](v41).Q.v41);
Q13 := reduceByLinearEquation(Q12, v41):
Q13 := simplify(Q13);
nops(indets(Q13));
randomRank(Q13);

## THE ONLY SOLUTION IS THE NON-RATIONAL SOLUTION!=!=!=!=!=!=!=!=!=!==!=!=!=!=!=!

MNEW;
simplify(MNEW-Q13);
