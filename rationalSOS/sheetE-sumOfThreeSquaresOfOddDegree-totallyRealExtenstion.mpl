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
# Construction of Theorem 5.1 using a totally real extension of Q
#######################################################################

# In this worksheet we do the same construction as in Theorem 5.1
# for a sum of three squares in an algebraic extension of degree 3,
# but instead of using Q(cubic root of 2), we use a totally real 
# extension. By Hillar results, this polynomial must be decomposable
# as the sum of squares with rational coefficients.

# We define a polynomial z as the sum of three squares in an algebraic
# extension of degree 3 with generic coefficients.

mp := t^3-7*t^2+2*t+10; 
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

p1ss := subs({t = RootOf(x^3-7*x^2+2*x+10)}, p1s); 
p2ss := subs({t = RootOf(x^3-7*x^2+2*x+10)}, p2s); 
p3ss := subs({t = RootOf(x^3-7*x^2+2*x+10)}, p3s); 

f := simplify(p1ss^2+p2ss^2+p3ss^2);

# Real solutions - In this problem, the system obtained by equating f and the partial derivatives 
# to 0 is too complicated for Maple solver. 
# If we call exactSOS(f), it will not finish. 
#
# We need to compute some solutions manually. 
#Using the starting polynomials we get a system that # is easier to solve.
sSym := solve({p1ss = 0, p2ss = 0, p3ss = 0});

# Maple founds 4 branches of solutions.
# We use the first branch:
# {w = w, x = x, y = RootOf(8*_Z^2+(104*w-21*x)*_Z+328*w^2-84*w*x+25*x^2), z = -(1/4)*x}

# We need to compute real points in these branch. We give different values to x and w:
# (we use procedure evalSolution from rationalSOS package to evaluate the solution)
s1 := evalSolution(sSym[1], {x = 1, w = -1});
s2 := evalSolution(sSym[1], {x = 1, w = -2});
s3 := evalSolution(sSym[1], {x = 1, w = -3});

# We verify that these solutions contain real points:
evalf(allvalues(s1));
evalf(allvalues(s2));
evalf(allvalues(s3));

# We now call procedure exactSOS using only these 3 points as solutions.
out := exactSOS(f, zeros = {s1, s2, s3});

# The problem is solved. We verify the solution
p := 0:
for i from 1 to 6 do p := p + out[1][i]*out[2][i]^2 end:
simplify(f-p);

