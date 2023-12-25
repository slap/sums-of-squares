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
# Example 4.4 in [1]
#######################################################################

# Constructin of f. We begin with generic polynomials in Q(alpha),
# alpha a root of Z^3-2.

mp := t^3-2; 
p1 := c1*t^2+b1*t+a1; 
p2 := c2*t^2+b2*t+a2; 
b1 := x; b2 := y; c1 := z;

c2 := b1;
fGeneric := p1^2+p2^2; 
fGeneric := expand(fGeneric);

# We solve the coefficients a1 and a2 so that the polynomial is in Q,
f2 := NormalForm(fGeneric, [mp], plex(a1, a2, b1, b2, c1, t)); 
f3 := collect(f2, t); 
lf := CoefficientList(f3, t); 
ss := solve({lf[2], lf[3]}, {a1, a2});

# We plug in the solutions found for a1 and a2
ssDen := denom(rhs(ss[1])); 
p1s := simplify(subs(ss, p1)*ssDen); 
p2s := simplify(subs(ss, p2)*ssDen); 

p1ss := subs({t = RootOf(Z^3-2)}, p1s); 
p2ss := subs({t = RootOf(Z^3-2)}, p2s); 

# Verification
f := simplify(p1ss^2+p2ss^2);

# Conjugates of the original polynomial decomposition
pa1, pa2, pa3 := allvalues(p1ss);
pb1, pb2, pb3 := allvalues(p2ss);

# f^3 = (P1 + IP2)*(P1 - IP2)
P1 := pa1*pa2*pa3 - pb1*pb2*pa3 - pa1*pb2*pb3 - pb1*pa2*pb3;
P2 := -pb1*pb2*pb3 + pa1*pb2*pa3 + pa1*pa2*pb3 + pb1*pa2*pa3;
P1 :=  simplify(P1);
P2 :=  simplify(P2);
simplify(P1^2+P2^2 - f^3);

# f = p1^2 + p2^2
p1 := simplify(P1 / f);
p2 := simplify(P2 / f);

