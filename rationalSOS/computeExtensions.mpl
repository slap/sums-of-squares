computeExtensions := module()
description "Tools for exact sum of squares decomposition";
option package;
export computeExtensionDeg5;


# Given values of the coefficientes, computes four polynomials with coefficients in an algebraic
# extension of degree 5 such that their is a rational polynomials.

computeExtensionDeg5 := proc(s)
  local p1, p2, p3, p4, p1s, p2s, p3s, p4s, p1ss, p2ss, p3ss, p4ss;
  local mp, fGeneric, f2, f3, lf, sSym1, sSym, ss, ssDen;
  # We define a polynomial z as the sum of three squares in an algebraic
  # extension of degree 3 with generic coefficients.

  mp := t^5-2; 
  p1 := e1*t^4+d1*t^3+c1*t^2+b1*t+a1; 
  p2 := e2*t^4+d2*t^3+c2*t^2+b2*t+a2; 
  p3 := e3*t^4+d3*t^3+c3*t^2+b3*t+a3; 
  p4 := e4*t^4+d4*t^3+c4*t^2+b4*t+a4;

  # We impose some relations between the coefficients to decrease
  # the dimension of the problem and rename the remaining variables
  p1 := eval(p1, s);
  p2 := eval(p2, s);
  p3 := eval(p3, s);
  p4 := eval(p4, s);

  #f2 := NormalForm(fGeneric, [mp], plex(a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, t)); 

  fGeneric := p1^2+p2^2+p3^2+p4^2:
  fGeneric := expand(fGeneric):


  # We solve the coefficients a1 and a2 so that the polynomial is in Q,
  f2 := NormalForm(fGeneric, [mp], plex(a1, a2, a3, a4, x, y, z, w, t)):
  f3 := collect(f2, t):
  lf := CoefficientList(f3, t): 
  print("lf: ", lf);
  ss := solve({lf[2], lf[3], lf[4], lf[5]}, {a1, a2, a3, a4});

  print("ss: ", ss);

  # We plug in the solutions found for a1 and a2 and compute the resulting polynomial
  ssDen := lcm(denom(rhs(ss[1])), denom(rhs(ss[2])), denom(rhs(ss[3])), denom(rhs(ss[4]))); 
  print("ssDen: ", ssDen);

  p1s := simplify(subs(ss, p1)*ssDen): 
  p2s := simplify(subs(ss, p2)*ssDen): 
  p3s := simplify(subs(ss, p3)*ssDen):
  p4s := simplify(subs(ss, p4)*ssDen):

  p1ss := subs({t = RootOf(Z^5-2)}, p1s): 
  p2ss := subs({t = RootOf(Z^5-2)}, p2s): 
  p3ss := subs({t = RootOf(Z^5-2)}, p3s): 
  p4ss := subs({t = RootOf(Z^5-2)}, p4s): 

  print("p1ss: ", p1ss);

  fh := simplify(p1ss^2+p2ss^2+p3ss^2+p4ss^2);
  
#  p1ssa := eval(p1ss, {z = 1});
#  p2ssa := eval(p2ss, {z = 1});
#  p3ssa := eval(p3ss, {z = 1});
#  sSym := solve({p1ssa = 0, p2ssa = 0, p3ssa = 0});
  sSym := [];

  f := simplify(p1ss^2+p2ss^2+p3ss^2+p4ss^2);

  [f, fh, {p1ss, p2ss, p3ss, p4ss}, [sSym]];
end proc:


end module; # computeExtensions
