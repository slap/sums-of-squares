### Rational SOS library v0.1
### A Maple library for computing rational sum of squares decompositions.
### Author: Santiago Laplagne
### Contact: slaplagn@dm.uba.ar

### Requirements: 
### - Maple (tested on 2015 Windows version)
### - Matlab (tested on 2016 Windows version)
### - SEDUMI package installed on Matlab
###   (download from http://sedumi.ie.lehigh.edu/?page_id=58)

### Some of the procedures in this library, as well as connection 
### with SEDUMI, are based on 
### SOSTOOLS - A sum of squares optimization toolbox for Matlab
### by Antonis Papachristodoulou, James Anderson, Giorgio Valmorbida,
### Stephen Prajna, Peter Seiler, Pablo A. Parrilo
### https://www.cds.caltech.edu/sostools/

### Support
### Maple functions output can be different dependending on the format
### of the input, for example if the input polynomial is expanded or 
### not, and this can produce errors, the code has not been tested 
### extensively.
### If you find any such error, or any other problem, 
### please contact the author providing a concrete example where the
### error is obtained.

### Since Maple connection with Matlab is system dependent, the author
### cannot provide support on this matter. Please contact Maple or
### Matlab support for this.

#######################################################################
# CONNECTION WITH MATLAB
#######################################################################
with(Matlab):

# We postpone opening the connection until we need it
#print("Opening connection with Matlab");
#openlink();

#######################################################################
# Maple packages
#######################################################################

with(LinearAlgebra):
with(Groebner):
with(PolynomialTools):
with(ListTools):
with(Optimization):
with(Student:-NumericalAnalysis):


rationalSOS := module()
description "Tools for exact sum of squares decomposition";
option package;
export numericSolverSubmatrixMaxRank;
export solveSubmatrixGeneral, homogenize, isHomogeneous;
export exactSOS, numericSolver, numericSolverSubmatrix, numericSolverSubmatrixRoundBefore, reduceByLinearEquation;
export getDiag, randomRank, evalMat, roundVec, roundMat, roundMatFloat, smallToZero, smallToZeroMatrix, zeroRows, zeroDetSRows, zeroDetSys;
export matrixToPoly, polyToMatrix, polyToMatrixVars, decompositionToMatrix, vectorTrace, getVars, rround, roundAbs, rrounde;
export primitiveMatrix, nonRatCoef, getExtension, evalSolution, getCoeffs, dimSimplex;
export cancelDenominator, reduceByLinearEquationLinear, linIndepRows, listSubsets;
export sedumiCallObjective, sedumiCallMaxSpectralNorm, sedumiCallMaxSpectralNormSDP;
export solveSubset, roundToIntMatrix, roundMatToZero, solveToZero;
export minorsDet;
local sublist, addElt, getEquationsTrace, getEquationsTraceRandom, getEquationsPlain, getEquationsPlainRandom; 
local hasExtension, hasRationalSolution, getIndet, solveEquations;
local hasRealRoot;
local emptyRow, productDenominator;
local facialReduction, randomSolutions, randomTraceSolutions, checkMinEig, quotFactor;
local commonDenominator;



#########################################################################
# exactSOS
# main procedure of the package
#
# Given a polynomial f, it computes an exact SOS decomposition of f.
# It assumes f is an homogeneous polynomial.
#
#########################################################################

# OPTIONS
# 
# - zeros
# list of solutions of f = 0 given by exact points or by parametrizations 
# of the solutions. 
# If the solutions are given by parametrizations (for example, the 
# output of solve procedure), it looks for real solutions by assigning 
# random values to the unknowns. 
#
# If no list of solutions is given, it will compute them by solving 
# f = 0 and all the partial derivative = 0.
# 
# See Worksheet E for an example of usage
#
# - traceEquations = "yes" / "no"
# If traceEquations is set to "yes", it will use the trace of the real solutions
# to derive equations to reduce the dimension of the search space.
# All rational solutions must verify these equations, so no rational solution
# will be lost. Real solutions may be lost, so this option should be set to "no"
# if you want to determine if there exists a real SOS.
#
# - forceRational = "yes" / "no"
# If forceEquations is set to "yes", it will remove non-rational terms in the entries 
# of the parametrization matrix. This simplifies the problem but may loose solutions
# (even rational solutions maybe lost).
# It should only be set to "yes" if the problem cannot be solved using option "no"
#
# - digits = integer
# Number of digits to be kept when rounding the numerical solution from SEDUMI.
#
# - incremental = "yes" / "no"
# Defines whether the systems of equations obtained from the real solutions
# should be solved after adding each new equation or it should first compute
# all the equations and then solve the problem. 
# Option "no" is preferred, "yes" can be tried if "no" does not succeed.
#
# - printLevel = integer
# Set higher printLevel for printinig more output and intermediate results.


exactSOS := proc(f, {`useMatlab`:="yes", `zeros` := {}, `realPolynomials` := {}, `facial`::string := "yes", `plainEquations`::string := "yes", `traceEquations`::string := "yes", `forceRational`::string := "no" , `computePolynomialDecomposition`::string := "yes", `digits`::integer := 10, `incremental` := "no", `printLevel`::integer := 0, `objFunction`:="eig"} )
  local eqs, sSym, cfs, cf, vars, cfv, cfvt, mSize, MM, i, j, ex, rr, sol, MMS, MMSE, rRank, MMT, tVars;
  local yRound, eigens, symEigens, cfPlain;
  local QQ, mVars, MSol, TSol, ySol, fs, fSimp;
  local cFail; 
  local originalRank, originalDimension;
  local MMSERound, approxSolution, solved;

  if (printLevel >= 1) then print("exactSOS begins...") end if;

  fSimp := expand(simplify(f));
  if(not(isHomogeneous(fSimp))) then
    fSimp := homogenize(fSimp, _H);
    print("The input polynomial is not homogeneous. I am homogenizing it to ", fSimp);
  end if:

  if(degree(fSimp) mod 2 = 1) then
    error("The input polynomial has odd degree. A SOS decomposition cannot exist.");
  end if:
  
  # vars are the variables of f
  # cfv is the vector of monomials that can appear in 
  cfs, cf, vars := getVars(fSimp);
  cfv := Vector(cf);
  
  if (printLevel >= 5) then print("polyToMatrix begins") end if;
  MMS, mVars, cfPlain := polyToMatrix(fSimp);
  if (printLevel >= 5) then print("polyToMatrix finished") end if;
  
  # Any values we set to the unknowns in MMS will provide a solution to 
  # to v^t MM v = f
  
  # PROBLEM: The problem is now to determine rational values to those 
  # unknowns so that the matrix is positive semidefinite.

  # Plain equations
  # Plain equations
  if(facial = "yes") then
  
    originalRank := randomRank(MMS);
    originalDimension := nops(indets(MMS));
    if (printLevel >= 5) then print("randomRank finished") end if;
  
    # If no real solution of f = 0 is given, we compute them.
    if(nops(zeros) = 0) then
      if (printLevel >= 1) then print("Computing real zeros of f...") end if;  
      if(nops(realPolynomials) = 0) then 
        QQ := [];
        for i from 1 to nops(vars) do
          QQ := [op(QQ), diff(fSimp, vars[i])];
        end do:
      else 
        QQ := realPolynomials;
        #print("real p", QQ);
      end if;
      eqs := Equate(QQ, Vector(nops(QQ)));
      sSym := [solve(eqs)];
      sSym := expand(sSym);
      #print("Solutions to f = 0 found by solve procedure:", sSym);
      if(nops(sSym) > 0) then 
        #if (printLevel >= 1) then print("Zeros found:", sSym) end if;
        if (printLevel >= 1) then print("Zeros found.") end if;
      else 
        if (printLevel >= 1) then print("No real zeros were found. No facial reduction will be performed.") end if;
      end if;
    else 
      sSym := expand(zeros);
    end if:
    MMSE := facialReduction(MMS, sSym, cfv, incremental_f = incremental, eqPlain = plainEquations, eqTrace = traceEquations, forceRational_f = `forceRational`,  printLevel_f = (printLevel - 1));
  else
    MMSE := MMS;
  end;

  if (printLevel >= 5) then print("After plain equations") end if;
  
  rRank := randomRank(MMSE);

  # Remove
  rRank := randomRank(evalf(MMSE));

  if(facial = "yes") then
    print("-----");
    print("Facial reduction results:");
    print("Original matrix - Rank: ", originalRank, " - Number of indeterminates: ", originalDimension);
    print("Matrix after facial reduction - Rank: ", rRank, " - Number of indeterminates: ", nops(indets(MMSE)));
    #print("Matrix MMSE = ", evalf(simplify(MMSE)));
  else 
    MMSE := zeroRows(MMSE);
  end if;
  
  print("Number of indeterminates: ", nops(indets(MMSE)));
  
  if(nops(indets(MMSE)) > 0) then
    

    #######################################################################
    # After reducing the dimension of the problem, 
    # we use SEDUMI to find a solution to Problem 1
    #######################################################################

    if(useMatlab = "yes") then
    
      print("Opening connection with Matlab");
      openlink();

      print("Calling numerical solver SEDUMI to find the values of the remaining indeterminates...");

      if(getExtension(MMSE)<>0) then
        print(getExtension(MMSE));
        print("Matrix contains algebraic numbers. They will be rounded to call the numerical solver SEDUMI. You can also try forceRational = \"yes\" for computing an exact rational solution.");

        MMT, tVars, ySol := numericSolverSubmatrixRoundBefore(MMSE, rRank, objFunction);

        yRound := roundVec(ySol, digits);
        yRound := smallToZero(ySol, digits);
        
        MSol := evalMat(MMSE, tVars, yRound);
        approxSolution := 1:
      else 
        MMT, tVars, ySol := numericSolverSubmatrix(MMSE, rRank, objFunction);
        yRound := roundVec(ySol, digits);
        yRound := smallToZero(ySol, digits);

        # Use this instead to convert all small numbers to zero.
        #yRound := smallToZero(ySol, digits);

        MSol := evalMat(MMSE, tVars, yRound);
        approxSolution := 0:
      end if;
      
      if(computePolynomialDecomposition = "yes") then
        if(simplify((expand(LinearAlgebra[Transpose](cfv) . MSol . cfv) - fSimp)) != 0) then
          print("The approximation of the numerical solution is not correct. Try increasing the number of digits in the approximation.");
        else 
          if(approxSolution = 0) then 
            TSol := evalMat(MMT, tVars, yRound);
            solved := LinearAlgebra[IsDefinite](TSol);
          else 
            solved := false;
          end if;

          if(solved) then
            print("Reduced problem solved. Exact positive definite matrix found for the reduced problem.");
          else 
            print("An exact positive definite solution could not be found for the reduced problem.")
          end if;
        end if;
      else 
        solved := false;
      end if;
    else
      solved := false;
      print("Problem not solved. Please try enabling numerical optimization via Matlab call to SEDUMI.");
      MSol := MMSE;
      ySol := {}:
    end if;
  else
    print("An exact solution was found without calling the numerical solver. The solution matrix is unique under the specified conditions."); 
    solved := true;
    MSol := MMSE;
    ySol := {}:
  end if;
  MSol := simplify(MSol);

  if(computePolynomialDecomposition = "yes") then
    fs := matrixToPoly(MSol, cfv);
  end if;
    
  if(solved) then 
    if(computePolynomialDecomposition = "yes") then 
      # We check if solution is positive semidefinite
      cFail := 0:
      
      for i from 1 to nops(fs[5]) do
        if(evalf(fs[5][i]) < 0) then
          cFail := 1;
        end if;
      end;

      if(cFail = 1) then
        print("The solution is not positive semidefinite. A SOS decomposition may not exist under the specified conditions.");
      else 
        print("Extension succedeed. An exact SOS decomposition has been found for the input polynomial.");
      end if;
    end if;
  end if;
  
  if(computePolynomialDecomposition = "yes") then 
    [fs[5], fs[6], MSol, MMSE, cfv]:
  else 
    [0, 0, MSol, MMSE, cfv]:
  end if
end proc:

#######################################################################
# Code for generating subsets of desired number of elements
# Procedures from
# https://www.maplesoft.com/applications/view.aspx?sid=4244&view=html
#######################################################################

sublist := proc(list, ini)
  local i:
  [ seq(list[i],i=ini..nops(list)) ]:
end proc:

addElt := proc(elt, list)
  local templist, i:
  templist:=[]:
  for i from 1 to nops(list) do
    templist:=[ op(templist), [elt, op(list[i])] ]:
  end do:
  templist:
end proc:

listSubsets := proc(L, i)
  local n, j, fl, temp: # fl-final list
  n := nops(L):

  if i=1 then # base case
    fl:=[]:
    for j from 1 to n do
      fl:=[op(fl),[L[j]]]:
    end do:

  else 
    fl:=[]:
    for j from 1 to n-i+1 do 
      temp:=listSubsets(sublist(L,j+1),i-1):
      temp:=addElt(L[j],temp):
      fl:=[op(fl),op(temp)]:
    end do:

  end if:

  fl:
end proc:

#######################################################################
# Diagonal of a matrix as vector
#######################################################################

getDiag := proc(A)
  local nRow, nCol, v, i;
  nRow, nCol := LinearAlgebra[Dimension](A);
  v := Vector(nRow);
  for i from 1 to nRow do
    v[i] := A(i,i);
  end do:
  v:
end proc:

#######################################################################
# Random rank
# Given a matrix with unknows in the entries, it gives random values
# to the unknowns and compute the rank of the resulting matrix
#######################################################################

randomRank := proc(A)
  local randomA;
  randomA := eval(A, Equate([op(indets(A))], LinearAlgebra[RandomVector](nops(indets(A))))):
  
  LinearAlgebra[Rank](randomA);
end proc:

#######################################################################
# Builds the matrix from SEDUMI output
# AVars is the list of variables of A and y is the output from SEDUM
# which indicates the values to assign to each unknow of A respecting
# the order of variables given in A
# TODO: replace this by evaluation (check the correct signs!)
#######################################################################

evalMat := proc(A, AVars, y)
  local ANew:
  ANew := eval(A,Equate([op(AVars)], y[1..nops([op(AVars)])])):
  ANew:
end proc:



#######################################################################
# Sedumi call - Spectral norm (max eigenvalue)
#######################################################################

# Calls SEDUMI to minimize the largest eigenvalue of A.
# In this way, it will output a positive definite A if it exists

# minimize s 
# subject to 
# [ s I - A     0      ]
# [ 0           sI + A ] >= 0

sedumiCallMaxSpectralNorm := proc(A, AVars)

  local x, y, nRows, nCols, matlab_At, matlab_bt, matlab_ct, zeroTerm, i;
  local At_sub, A_sub;
  nRows, nCols := LinearAlgebra[Dimension](A);


  print("Opening connection with Matlab");
  openlink();
  
  matlab_At := Matrix((2*nRows) * (2*nRows), nops(AVars) + 1):
  
  for i from 1 to nops(AVars) do
  #  This is for minimum largest eigenvalue
  #  matlab_At[1..(nRows*nRows), i] := (-1)*convert(coeff(A, AVars[i]), Vector);
  #  We try this for maximum smaller eigenvalue?
    A_sub := coeff(A, AVars[i]);
    At_sub := Matrix((2*nRows), (2*nRows)):
    At_sub[1..nRows, 1..nRows] := -A_sub;
    At_sub[(nRows+1)..(2*nRows), (nRows+1)..(2*nRows)] := A_sub;
    matlab_At[1..(2*nRows*2*nRows), i] := -convert(At_sub, Vector);
  end do:
  At_sub := IdentityMatrix(2*nRows);
  matlab_At[1..(2*nRows*2*nRows), nops(AVars)+1] := -convert(At_sub, Vector):


  matlab_bt := Vector(1..(nops(AVars)+1), 0):
  matlab_bt[nops(AVars)+1]:=-1:

  zeroTerm := eval(A, Equate([op(AVars)], Vector(nops(AVars)))):
  At_sub := Matrix((2*nRows), (2*nRows)):
  At_sub[1..nRows, 1..nRows] := -zeroTerm;
  At_sub[(nRows+1)..(2*nRows), (nRows+1)..(2*nRows)] := zeroTerm;

  matlab_ct := convert(At_sub, Vector):
  
  print("At", Dimension(matlab_At));
  print("bt", Dimension(matlab_bt));
  print("ct", Dimension(matlab_ct));

  # We compute a real solution.
  # We will check if we can round it to get a rational solution
  setvar("At", matlab_At);
  setvar("bt", matlab_bt);
  setvar("ct", matlab_ct);
  setvar("nRows", 2*nRows);

  # SEDUMI parameters
  evalM("pars.eps=0;");
  evalM("p = length(bt);");
  evalM("K.s = nRows;");
  
  print("SEDUMI SPECTRAL");
  
  # SEDUMI call
  evalM("[x, y, info] = sedumi(At,bt,ct,K,pars);"):
  [x, y, info];
  x := getvar("x"):
  y := getvar("y"):
  x, y;
end proc:

#######################################################################
# Sedumi call - Spectral norm (max eigenvalue) restricted to SDP
#######################################################################

# Calls SEDUMI to minimize the largest eigenvalue of A.
# In this way, it will output a positive definite A if it exists

# minimize s 
# subject to 
# [ s I - A     0      ]
# [ 0           A      ] >= 0

sedumiCallMaxSpectralNormSDP := proc(A, AVars)
  local x, y, nRows, nCols, matlab_At, matlab_bt, matlab_ct, zeroTerm, i;
  local At_sub, A_sub;
  nRows, nCols := LinearAlgebra[Dimension](A);


  print("Opening connection with Matlab");
  openlink();
  
  matlab_At := Matrix((2*nRows) * (2*nRows), nops(AVars) + 1):
  
  for i from 1 to nops(AVars) do
  #  This is for minimum largest eigenvalue
  #  matlab_At[1..(nRows*nRows), i] := (-1)*convert(coeff(A, AVars[i]), Vector);
  #  We try this for maximum smaller eigenvalue?
    A_sub := coeff(A, AVars[i]);
    At_sub := Matrix((2*nRows), (2*nRows)):
    At_sub[1..nRows, 1..nRows] := -A_sub;
    At_sub[(nRows+1)..(2*nRows), (nRows+1)..(2*nRows)] := A_sub;
    matlab_At[1..(2*nRows*2*nRows), i] := -convert(At_sub, Vector);
  end do:
  # Identity matrix only on the first block
  At_sub := Matrix((2*nRows), (2*nRows)):
  At_sub[1..nRows, 1..nRows] := IdentityMatrix(nRows);
  matlab_At[1..(2*nRows*2*nRows), nops(AVars)+1] := -convert(At_sub, Vector):

  matlab_bt := Vector(1..(nops(AVars)+1), 0):
  matlab_bt[nops(AVars)+1]:=-1:

  zeroTerm := eval(A, Equate([op(AVars)], Vector(nops(AVars)))):
  At_sub := Matrix((2*nRows), (2*nRows)):
  At_sub[1..nRows, 1..nRows] := -zeroTerm;
  At_sub[(nRows+1)..(2*nRows), (nRows+1)..(2*nRows)] := zeroTerm;

  matlab_ct := convert(At_sub, Vector):
  
  print("At", Dimension(matlab_At));
  print("bt", Dimension(matlab_bt));
  print("ct", Dimension(matlab_ct));

  # We compute a real solution.
  # We will check if we can round it to get a rational solution
  setvar("At", matlab_At);
  setvar("bt", matlab_bt);
  setvar("ct", matlab_ct);
  setvar("nRows", 2*nRows);

  # SEDUMI parameters
  evalM("pars.eps=0;");
  evalM("p = length(bt);");
  evalM("K.s = nRows;");
  
  # SEDUMI call
  print("SEDUMI SPECTRAL");
  evalM("[x, y, info] = sedumi(At,bt,ct,K,pars);"):
  [x, y, info];
  x := getvar("x"):
  y := getvar("y"):
  x, y;
end proc:


###############################################################################
# Sedumi call - Allows different objective functions restricted to PSD matrices
###############################################################################

# FROM SEDUMI MANUAL:
# IV. SDP Problems
# Consider the “standard” dual SDP problem

# minimize c^T y
# subject to: F_0 + y_1 F_1 + ... + y_p F_p >= 0 (PSD)

# where vector y = [y 1 y 2 … y p ]^T, and F_i are symmetric matrices. 
# In order to use SeDuMi to solve the SDP problem, we define

# b_t = -c ;
# c_t = vec(F_0);
# A_t(:, i) = -vec(F_i) for i = 1, 2, ..., p

# This can be used to obtain many different points in the spectrahedron 
# of f
sedumiCallObjective := proc(A, AVars, objFunction)
  local x, y, nRows, nCols, matlab_At, matlab_bt, matlab_ct, zeroTerm, i;
  local tt;  
  
  print("Opening connection with Matlab");
  openlink();

  nRows, nCols := LinearAlgebra[Dimension](A);
  
  if (objFunction = "eig") then
    matlab_At := Matrix(nRows * nRows, nops(AVars) + 1):
    for i from 1 to nops(AVars) do
      matlab_At[1..(nRows*nRows), i] := -convert(coeff(A, AVars[i]), Vector);
    end do:
    
    # A_(s+1) = -Id, the coefficient is lambda.
    matlab_At[1..(nRows*nRows), nops(AVars)+1] := convert(LinearAlgebra[IdentityMatrix](nRows), Vector):

    # We maximize the value of the last parameter: lambda
    matlab_bt := Vector(1..(nops(AVars)+1), 0):
    matlab_bt[nops(AVars)+1]:=1:

    zeroTerm := eval(A, Equate([op(AVars)], Vector(nops(AVars)))):
    matlab_ct := convert(zeroTerm, Vector):
  end if;

  if (objFunction = "minX") then
    matlab_At := Matrix(nRows * nRows, nops(AVars)):
    for i from 1 to nops(AVars) do
      matlab_At[1..(nRows*nRows), i] := -convert(coeff(A, AVars[i]), Vector);
    end do:

    # We minimize the first coordinate
    matlab_bt := Vector(nops(AVars)):
    matlab_bt[1] := -1;

    zeroTerm := eval(A, Equate([op(AVars)], Vector(nops(AVars)))):
    matlab_ct := convert(zeroTerm, Vector):
  end if;

  if (objFunction = "maxX") then
    matlab_At := Matrix(nRows * nRows, nops(AVars)):
    for i from 1 to nops(AVars) do
      matlab_At[1..(nRows*nRows), i] := -convert(coeff(A, AVars[i]), Vector);
    end do:

    # We minimize the first coordinate
    matlab_bt := Vector(nops(AVars)):
    matlab_bt[1] := 1;

    zeroTerm := eval(A, Equate([op(AVars)], Vector(nops(AVars)))):
    matlab_ct := convert(zeroTerm, Vector):
  end if;
  
  if (objFunction = "random") then
    # Sedumi format, one matrix Ai, i >= 1, in each row
    matlab_At := Matrix(nRows * nRows, nops(AVars)):
    for i from 1 to nops(AVars) do
      matlab_At[1..(nRows*nRows), i] := -convert(coeff(A, AVars[i]), Vector);
    end do:

    # The linear functional to minimize is the trace of A as a function
    # of the unknowns yi
    
    matlab_bt := LinearAlgebra[RandomVector](nops(AVars)):
  
    # The matrix A0 is given as ct to SEDUMI
    zeroTerm := eval(A, Equate([op(AVars)], Vector(nops(AVars)))):
    matlab_ct := convert(zeroTerm, Vector):
  end if;
  
  if (objFunction = "atomic") then
    # Sedumi format, one matrix Ai, i >= 1, in each row
    matlab_At := Matrix(nRows * nRows, nops(AVars)):
    for i from 1 to nops(AVars) do
      matlab_At[1..(nRows*nRows), i] := -convert(coeff(A, AVars[i]), Vector);
    end do:

    # The linear functional to minimize is the trace of A as a function
    # of the unknowns yi
    tt := expand(LinearAlgebra[Trace](A));  # Trace
    matlab_bt := Vector(1..(nops(AVars)), 0):
    for i from 1 to nops(AVars) do
      matlab_bt[i] := -coeff(tt, AVars[i]);
    end do;
    
    # The matrix A0 is given as ct to SEDUMI
    zeroTerm := eval(A, Equate([op(AVars)], Vector(nops(AVars)))):
    matlab_ct := convert(zeroTerm, Vector):
  end if;

  # We compute a real solution.
  # We will check if we can round it to get a rational solution
  setvar("At", matlab_At);
  setvar("bt", matlab_bt);
  setvar("ct", matlab_ct);
  setvar("nRows", nRows);

  # SEDUMI parameters
  evalM("pars.eps=0;");
  evalM("p = length(bt);");
  evalM("K.s = nRows;");
  
  # Remove this optional parameters
  evalM("pars.maxiter=100;");
  evalM("pars.bigeps=.000001;");
  evalM("pars.alg=1;");
  evalM("pars.stepdif=0;");
  
  evalM("echo off;"):
  
  # SEDUMI call
  evalM("[output, x, y, info] = evalc('sedumi(At,bt,ct,K,pars);')"):
  x := getvar("x"):
  y := getvar("y"):
  x, y;
end proc:

#######################################################################
# We use SEDUMI to solve the problem restricted to a submatrix of
# the original matrix
#######################################################################

solveSubset := proc(A, sub0, objFunction)
  local MMT, tVars, x, y, randomMMT;

  MMT := LinearAlgebra[SubMatrix](A, sub0, sub0):
  tVars := indets(MMT);
  
  print("tVars = ", tVars);
  
  randomMMT := eval(MMT, Equate([op(tVars)], LinearAlgebra[RandomVector](nops(tVars)))):
  if (LinearAlgebra[Determinant](randomMMT) <> 0) then
    print("SEDUMI CALL - Objective function = ", objFunction);
  else 
    print("SEDUMI CALL - zero determinant - Objective function = ", objFunction);
  end if;
  
#  Dimension of the Simplex
#  lV := [];
#  for i from 1 to nops(tVars) do
#    x, y := sedumiCallObjective(MMT, tVars, "random");
#    #print("y: ", y);
#    lV := [op(lV), y[1..(Dimension(y)-1)]];
#  end do;
#  ds := dimSimplex(lV);
#  print("ds: ", ds);
#  print("Number of variables: ", nops(tVars));
  
  if (objFunction = "atomic") then
    # Minimum atomic norm
    print("SEDUMI CALL - atomic");
    x, y := sedumiCallObjective(MMT, tVars, "atomic");
  end if;
  if (objFunction = "spectralSDP") then
    # Maximum spectral norm restricted to SDP matrices
    print("SEDUMI CALL - spectral");
    x, y := sedumiCallMaxSpectralNormSDP(MMT, tVars);
  end if;
  if (objFunction = "spectral") then
    # Maximum spectral norm
    print("SEDUMI CALL - spectral");
    x, y := sedumiCallMaxSpectralNorm(MMT, tVars);
  end if;
  if (objFunction = "random") then
    # Minimize a random linear form
    print("SEDUMI CALL - random");
    x, y := sedumiCallObjective(MMT, tVars, "random");
  end if;
  if (objFunction = "minX") then
    # Minimum atomic norm
    print("SEDUMI CALL - min X");
    x, y := sedumiCallObjective(MMT, tVars, "minX");
  end if;
  if (objFunction = "maxX") then
    # Minimum atomic norm
    print("SEDUMI CALL - max X");
    x, y := sedumiCallObjective(MMT, tVars, "maxX");
  end if;
  if (objFunction = "eig") then
    print("SEDUMI CALL - eig");
    # Maximum of the smallest eigenvalue
    x, y := sedumiCallObjective(MMT, tVars, "eig");
  end if;
  if(not(type(y,'Vector'))) then
    #print("Not a vector: ", y);
    y := convert([y], Vector);
  end if;
  MMT, tVars, y:
end proc:

#########################################################################
# Coefficients of a polynomial with respect to a given list of monomials
#########################################################################

getCoeffs := proc(p, terms)
  local cf, cftV, vars, cfs, i, ind, out;
  vars := indets(terms);
  cfs := [coeffs(p, vars, 'cft')];
  cftV := [cft];
  out := Vector(nops(terms));
  for i from 1 to nops(cftV) do
    ind := ListTools[Search](cftV[i], terms);
    if(ind > 0) then 
      out[ind] := cfs[i];
    end if:
  end do:
  out;
end proc:

#########################################################################
# Rounding functions
#########################################################################
# Rounds to the closest rational faction keeping d representative 
# digits
rround := (x,d)-> convert(x, rational, d):

# Convert to rational after converting to floating point
rrounde := (x,d)-> convert(evalf(x), rational, d):

roundAbs := (x,d) -> parse(sprintf("%.*f",d,evalf(x))):

# Convert all small numbers (smaller than 10^(-d) in absolute value) 
# in v to 0, 
smallToZero := proc(v, d)
  local i, nRows, vR;
  nRows := LinearAlgebra[Dimension](v);
  vR := Vector(nRows);
  for i from 1 to nRows do
    if(abs(v[i])<10^(d*(-1))) then 
      vR[i] := 0;
    else 
      vR[i] := rround(v[i], d);
    end if;
  end do:
  vR;
end proc:

smallToZeroMatrix := proc(M, d)
  local i,j, nRows, nCols, MR;
  nRows, nCols := LinearAlgebra[Dimension](M);
  MR := Matrix(nRows, nCols);
  for i from 1 to nRows do
    for j from 1 to nCols do
      if(abs(M[i,j])<10^(d*(-1))) then 
        MR[i,j] := 0;
      else 
        MR[i,j] := roundAbs(M[i,j], d);
      end if;
    end do:
  end do:
  MR;
end proc:

roundVec := proc(v, d)
  local i, nRows, vR;
  nRows := LinearAlgebra[Dimension](v);
  vR := Vector(nRows);
  for i from 1 to nRows do
    vR[i] := rround(v[i], d);
  end do:
  vR;
end proc:

roundMat := proc(A,d)
  local i, j, nRows, nCols;
  nRows, nCols := LinearAlgebra[Dimension](A);
  for i from 1 to nRows do
    for j from 1 to nRows do
      A[i, j] := rround(A[i, j], d);
    end do:
  end do:
  A;
end proc:

roundMatFloat := proc(A,d)
  local i, j, nRows, nCols;
  nRows, nCols := LinearAlgebra[Dimension](A);
  for i from 1 to nRows do
    for j from 1 to nRows do
      A[i, j] := roundAbs(A[i, j], d);
    end do:
  end do:
  A;
end proc:

# Convert all entries of the matrix that at distance smaller than 10^(-d) from an integer, to that integer
roundToIntMatrix := proc(M, d)
  local i,j, nRows, nCols, MR;
  nRows, nCols := LinearAlgebra[Dimension](M);
  MR := Matrix(nRows, nCols);
  for i from 1 to nRows do
    for j from 1 to nCols do
      if((abs(frac(M[i,j]))<10^(d*(-1))) or (abs(1-frac(M[i,j]))<10^(d*(-1)))) then 
        MR[i,j] := round(M[i,j]);
      else 
        MR[i,j] := roundAbs(M[i,j], d);
      end if;
    end do:
  end do:
  MR;
end proc:

# Convert all entries of the matrix that at distance smaller than 10^(-d) from 0, to 0
roundMatToZero := proc(A, d)
  local i, j, nRows, nCols;
  nRows, nCols := LinearAlgebra[Dimension](A);
  for i from 1 to nRows do
    for j from 1 to nRows do
		if(abs(A[i, j])<10^(d*(-1))) then 
		  A[i, j] := 0;
		else 
		  A[i, j] := rround(A[i, j], d);
		end if;
    end do:
  end do:
  A;
end proc:

#########################################################################
# Equation obtained by computing the trace of a real solution 
#########################################################################
getEquationsTrace := proc(solSym, cfv, MMS, vars, L)
  local cfve, eqMinT, allEq, i, cofT, mSize, out, vecTrace, solCheck;
  mSize := LinearAlgebra[Dimension](cfv);
  cfve := eval(cfv, solSym):
  
  vecTrace := vectorTrace(cfve);

  eqMinT := MMS.vecTrace:

  allEq := []:
  for i from 1 to mSize do
    cofT := coeffs(expand(eqMinT[i]), vars);
    allEq := [op(allEq), cofT];
  end do:
  out := Equate(allEq,Vector(nops(allEq))):
  out;
end proc:


#########################################################################
# Equation obtained by evaluating the solution at random values and 
# computing the trace of the resulting vector
#########################################################################

getEquationsTraceRandom := proc(solSym, cfv, MMS, vars, boundRank)
  local cfve, eqMinT, allEq, i, j, cofT, mSize, out;
  local nVectors, randomSol, checkSol;

  mSize := LinearAlgebra[Dimension](cfv);
  nVectors := mSize;

  randomSol := randomTraceSolutions(solSym, cfv, vars, nVectors, boundRank):

  if(nops(randomSol) > 0) then
    for j from 1 to nops(randomSol) do
      eqMinT := MMS.randomSol[j]:

      allEq := []:
      for i from 1 to mSize do
        cofT := coeffs(expand(eqMinT[i]), vars);
        allEq := [op(allEq), cofT];
      end do:
    end do:
    out := Equate(allEq,Vector(nops(allEq))):
  else
    out := [];
  end if;  
  out;
end proc:

#########################################################################
# Equations obtained from symbolic solutions
#########################################################################

getEquationsPlain := proc(solSym, cfv, MMS, vars)
  local cfve, eqMinT, allEq, i, cofT, mSize, out, solCheck;
  mSize := LinearAlgebra[Dimension](cfv);

  cfve := eval(cfv, solSym):
  eqMinT := MMS.cfve:

  allEq := []:
  for i from 1 to mSize do
    cofT := coeffs(expand(numer(simplify(expand(eqMinT[i])))), vars);
    allEq := [op(allEq), cofT];
  end do:
  out := Equate(allEq,Vector(nops(allEq))):
  out;
end proc:

#########################################################################
# Equations obtained from symbolic solutions evaluating the unknowns
# at random values
# If ratSol is set to yes, it will force to be zero to all coefficients 
# of non-rational values in the entries in the matrix. This can 
# discard valid solutions, and should only be used if we are looking 
# for simple solutions to the problem.
#########################################################################

getEquationsPlainRandom := proc(solSym, cfv, MMS, vars, { ratSol::string := "no" })
  local cfve, eqMinT, allEq, allEqRat, eqRat, i, j, cofT, mSize, out;
  local nVectors, randomSol, solCheck, aAlg, aPrim;
  mSize := LinearAlgebra[Dimension](cfv);

  # FIX THIS!!
  # This sets the maximum of vectors to try to reduce the dimension of the 
  # search space. It should be changed to some verification that no more
  # reduction can be obtained.
  #nVectors := mSize * 10;
  nVectors := mSize;

  randomSol := randomSolutions(solSym, cfv, vars, nVectors):

  if(nops(randomSol) > 0) then

    allEq := []:
    for j from 1 to nops(randomSol) do
      eqMinT := MMS.randomSol[j]:
      if(nops(indets(eqMinT)) > 0) then
        for i from 1 to mSize do
          cofT := coeffs(expand(eqMinT[i]), vars);
          allEq := [op(allEq), cofT];
        end do:
      end if;
    end do:

    if(ratSol = "yes") then
      allEqRat := [];
      for j from 1 to nops(allEq) do
        if(getExtension(allEq[j])<>0) then
          aAlg := evala(Algfield(allEq[j]));
          aPrim := evala(Primfield(aAlg[3]));
          eqRat := coeffs(expand(eval(numer(allEq[j]), aPrim[2])), [lhs(op(aPrim[1]))]):
          allEqRat := [op(allEqRat), eqRat];
        else
          allEqRat := [op(allEqRat), allEq[j]];
        end if;
      end do:
      out := Equate(allEqRat,Vector(nops(allEqRat))):
    else 
      if(nops(allEq) > 0) then
        out := Equate(allEq,Vector(nops(allEq))):
      else 
        out := [];
      end if;
    end if:
  else 
    # No real solutions in this branch
    out := [];
  end if;
  out;
end proc:


#########################################################################
# Simplifies the matrix by forcing  to be zero to all coefficients 
# of non-rational values in the entries in the matrix. This can 
# discard valid solutions, and should only be used if we are looking 
# for simple solutions to the problem.
#########################################################################

nonRatCoef := proc(MMSE, mSize, az)
  local out, allCoefEq, i, j, cofT, eqsCoef, matC2, vecC2, sol123C, solT2, ex;
  allCoefEq := [];
  for i from 1 to mSize do 
    for j from i to mSize do 
      #print("argument: ", expand(numer(MMSE[i,j])), [az]);
      cofT := coeffs(expand(numer(MMSE[i,j])), [az]);
      for ex from 2 to nops([cofT]) do
        allCoefEq := [op(allCoefEq), cofT[ex]];
      end do:
    end do:
  end do:
  eqsCoef := Equate(allCoefEq,Vector(nops(allCoefEq))):
  matC2, vecC2 := LinearAlgebra[GenerateMatrix](eqsCoef,indets(MMSE)):
  LinearAlgebra[Rank](matC2);
  sol123C := LinearAlgebra[LinearSolve](matC2, vecC2):
  solT2 := Equate([op(indets(MMSE))], sol123C):
  out := eval(MMSE, solT2):
  out := simplify(out):
  out;
end proc:

#########################################################################
# Checks if the element given is in an algebraic extension of Q
#########################################################################

hasExtension := proc(elem)
  local out, a, i;
  out := 0;
  a := evala(Algfield(elem));
  for i from 1 to nops(a) do
    if (nops(a[i]) = 1) then
      if (a[i] <> true) then
        out := 1;
      end if;
    end if;
  end do:
  out;
end proc:

#########################################################################
# We check if the equation has rational solutions.
#########################################################################
hasRationalSolution := proc(elem)
  local out, a, i;
  out := 0;
  a := evala(Algfield(elem));
  if (a[4]=false) then
    out := 1;
  else 
    out := 0;
  end if;
  out;
end proc:


#########################################################################
# Extracts the extension of Q in which the given element lives
#########################################################################
getExtension := proc(elem)
  local out, a, i, debugExtension;
  debugExtension := false;
  
  out := 0;
  a := evala(Algfield(elem));
  if(debugExtension) then 
    print("getExtension - Algfield(elem):", a);
  end if;
  if(a[4]=true) then
    if (nops(a[3]) = 1) then
      out := a[3][1];
    end if;
    if(nops(a[3]) > 1) then
      out := lhs(evala(Primfield(a[3]))[1][1]);
    end if;
  else 
    # Fix for some cases where RootOf contain labels
    if(nops(a[3]) > 0) then 
      out := a[3][1];
      #Not working: (used to remove labels)
      #out := RootOf(op(out)[1]);
    end if;
  end if;
  if(debugExtension) then 
    print("Output of extension: ", out);
  end if;
  out;
end proc:

#########################################################################
# Extracts the indeterminates involved in the given element
#########################################################################
getIndet := proc(elem)
  local out, i;
  out := [];
  for i from 1 to nops(elem) do
    out := {op(out), op(indets(rhs(elem[i])))};
  end do:
  out;
end proc:


#########################################################################
# Given a symmetric matrix with coefficients affine coefficients,
# it checks if there are zeros in the diagonal and in that
# case equates all the coefficients of the row to 0, solve the equations
# and replace the entries in the matrix by the solutions.
#########################################################################
zeroRows := proc(M)
  local out, i, eqsNew, nRows, nCols, matC, vecC, solT, sol123;
  local indetsBefore;
  nRows, nCols := LinearAlgebra[Dimension](M);

  indetsBefore := nops(indets(M));
  out := M;
  eqsNew := []:
  for i from 1 to nRows do:
    if (out[i,i] = 0) then
      eqsNew := [op(eqsNew), op(Equate(LinearAlgebra[Row](out, i), Vector(nRows)))]:
    end if;
  end do;

  matC, vecC := LinearAlgebra[GenerateMatrix](eqsNew,indets(M)):
  sol123 := LinearAlgebra[LinearSolve](matC, vecC):
  
  solT := Equate([op(indets(out))], sol123):
  out := eval(out, solT):

  if(nops(indets(out)) < indetsBefore) then 
    out := zeroRows(out);
  end;
  out:
end proc:


#########################################################################
# Given a matrix and equations involving the unknowns in the entries of 
# matrix, it solves the equations and replace the solution in the 
# entries of the matrix.
#########################################################################
solveEquations := proc(M, eqs)
  local out, matC, vecC, sol123, solT;
  matC, vecC := LinearAlgebra[GenerateMatrix](eqs,indets(M)):

  sol123 := LinearAlgebra[LinearSolve](matC, vecC):

  solT := Equate([op(indets(M))], sol123):
  
  out := eval(M, solT):
  out;
end proc:


#########################################################################
# Same as numericSolverSubmatrix but we compute the rank for the
# exact matrix and not the rounded one. We use an approximation 
# only for calling SEDUMI
#########################################################################
numericSolverSubmatrixRoundBefore := proc(M, d, objFunction)
  local MMT, tVars, y, subRows, nRows, nCols, ind, i;
  local l, subMat, subsub, MApprox;

  subsub := linIndepRows(M, d);
  
  MApprox := evalf(simplify(M));
  MMT, tVars, y := solveSubset(MApprox, subsub, objFunction);

  MMT, tVars, y:
end proc:

#########################################################################
# Calls SEDUMI to compute an approximate solution.
# We restrinct to a dxd matrix where d is the rank of the input matrix
#########################################################################
numericSolverSubmatrixMaxRank := proc(M, objFunction)
  local MMT, tVars, y;
  local subsub, d;

  d := randomRank(M);
  subsub := linIndepRows(M, d);

  MMT, tVars, y := solveSubset(M, subsub, objFunction);
  MMT, tVars, y:
end proc:

#########################################################################
# Calls SEDUMI to compute an approximate solution.
# The second parameter d indicates the rank of the matrix M, so it will
# call SEDUMI with a submatrix of size d x d
#########################################################################
numericSolverSubmatrix := proc(M, d, objFunction)
  local MMT, tVars, y, subRows, nRows, nCols, ind, i;
  local l, subMat, rndRk, subsub;

  nRows, nCols := LinearAlgebra[Dimension](M);
  subRows := [];
  for i from 1 to nRows do 
    if(emptyRow(M,nRows,i) = 0) then
        subRows := [op(subRows),i];
    end if
  end do;

  # We compute linear independnt rows only if d < nRows(M)
  nRows, nCols := LinearAlgebra[Dimension](M);  
  if(d < nRows) then 
    subsub := linIndepRows(M, d);
  else 
    subsub := [seq(i, i = 1 .. nRows)];
  end;
  
  #DEBUG
  print("subsub = ", subsub);
  MMT, tVars, y := solveSubset(M, subsub, objFunction);

  MMT, tVars, y:
end proc:

# Checks if the k-th row of the nxn matrix M is null
emptyRow := proc(M,n,k)
  local out, i;
  out := 1;
  for i from 1 to n do
    if (M[k,i] <> 0) then
      out := 0;
    end if;
  end do;
  out;
end proc:

#########################################################################
# Calls SEDUMI to compute an approximate solution.
#########################################################################
numericSolver := proc(M, objFunction)
  local MMT, tVars, y, subRows, nRows, nCols, ind, i;
  subRows := [];
  nRows, nCols := LinearAlgebra[Dimension](M);
  subRows := [seq(i, i = 1 .. nRows)];
  MMT, tVars, y := solveSubset(M, subRows, objFunction);
  MMT, tVars, y:
end proc:

#########################################################################
# Computes the list of monomials that can appear in the solution.
# It assumes the starting polynomial is homogeneous and hence the
# degree of the monomials in the solution will be half the degree
# of the starting polynomial
#########################################################################
getVars := proc(p)
  local i, l, d, pVars, cfs, cf, vars;
  pVars := indets(p);
  d := degree(p);
  l := 0;
  for i from 1 to nops(pVars) do
    l := l + pVars[i];
  end do:
  l := l^(d/2);
  vars := [op(pVars)];
  cfs := [coeffs(expand(l), vars, 'cf')];
  cfs, [cf], vars;
end proc:

##########################################################################
## Checks if a given algebraic extension contains a real root.
##########################################################################
hasRealRoot := proc(L)
  local n, allV, out, i;
  n := nops(L);

  print("checking real roots in extension - algebraic extension L = ", L);

  out := 0;

  # First check
  allV := [evalf(allvalues(L))];
  for i from 1 to nops(allV) do
    if (Im(allV[i])=0) then 
      out := 1;
    end if:
  end do:

  # Second check
  # Not working when the extension L has a label.
  if (out = 0) then
    allV := [fsolve(op(L))];
    if (nops(allV) > 0) then
      print("checked extension - output of fsolve: ", allV);
      for i from 1 to nops(allV) do
        if (Im(allV[i])=0) then 
          out := 1;
          print("real root found:", allV[i]);
          break;
        end if:
      end do:
    end if;
  end if;
  
  out;
end proc:
  
#########################################################################
# MAIN ROUTINE
# Given a matrix with unknowns in the entries it will apply
# the different strategies in the paper to reduce the dimension of
# the problem.
#########################################################################

facialReduction := proc(M, symbSol, cfv, { `incremental_f`::string := "no", `eqTrace`::string := "yes", `eqPlain`::string := "yes", `forceRational_f`::string := "no", `printLevel_f` :: integer := 0})
  local out, eqsAll, L, i, nRows, nCols, vars, thisEq;
  local out1, out2, out3, out4, out5, out6, out7;
  local eqsPlain, eqsTrace, eqsStep, eqFace;
  local boundRank;
  local printLevel;

  printLevel := printLevel_f;
  if (printLevel >= 1) then print("Facial Reduction begins...") end if;

  nRows, nCols := LinearAlgebra[Dimension](M);
  vars := indets(cfv);

  # We start from M and apply facial reduction techniques to reduce the rank and number of unknowns
  out := M;
  
  # Equations from trace
  if(eqTrace = "yes") then
    print("Option traceEquations: yes - Only valid when looking for rational decompositions.");
    if (printLevel >= 1) then print("Computing trace equations...") end if;

    eqsTrace := [];

    for i from 1 to nops(symbSol) do
      if (printLevel >= 1) then print("trace equation", i) end if;

      # We check if the equations contain roots of equations involving the unknowns
      if(nops(indets(symbSol[i])) > nops(vars)) then
        if (printLevel >= 1) then print(" - extension with unknowns") end if;
        eqFace := "random";
      else 
        if (printLevel >= 1) then print(" - extension without unknowns") end if;
        eqFace := "indeterminate";
      end if;

      if(eqFace = "random") then
        boundRank := 0;
        thisEq := op(getEquationsTraceRandom(symbSol[i], cfv, out, vars, boundRank));
        eqsTrace := [op(eqsTrace), thisEq]:
      else 
        L := getExtension(symbSol[i]):
        if (hasRealRoot(L) = 1) then
          if (L <> 0) then 
            thisEq := op(getEquationsTrace(symbSol[i], cfv, out, vars, L));
            eqsTrace := [op(eqsTrace), thisEq]:
          else 
            print("No algebraic extension in this branch. Check: ", symbSol[i]);
          end if:
        else 
          print("no real roots in this solution, please check...", L);
        end if:
      end if;

      if(incremental_f = "yes") then

        if (printLevel >= 1) then print("Solving trace equations...") end if;

        out := solveEquations(out, eqsTrace):
        out1 := out;

        eqsTrace := [];

        if (printLevel >= 1) then 
          print("rank after trace equations: ", randomRank(out));
          print("indets after trace equations", nops(indets(out)));
        end if;

        if(nops(indets(out))>0) then
          if (printLevel >= 1) then print("Zero equations after incremental trace...") end if;

          out := zeroRows(out):
          out2 := out;

          out := zeroDetSRows(out,2):
          out3 := out;
        end if;
      end if;
    end do:

    if(incremental_f = "no") then
      if (printLevel >= 1) then print("Solving trace equations...") end if;
      out := solveEquations(M, eqsTrace):
      out1 := out;

      if (printLevel >= 1) then 
        print("rank after trace equations: ", randomRank(out));
        print("indets after trace equations", nops(indets(out)));
      end if;

      if(nops(indets(out))>0) then
        if (printLevel >= 1) then print("Zero equations after not incremental trace ...") end if;
        out := zeroRows(out):
        out2 := out;

        if (printLevel >= 1) then print("Two by two equations...") end if;
        out := zeroDetSRows(out,2):
        out3 := out;
      end;
    end;
  else 
    if (printLevel >= 1) then print("Trace equations are not used.") end if;
  end;

  if (printLevel >= 1) then 
    print("rank after zero det equations: ", randomRank(out));
    print("indets after zero det equations", nops(indets(out)));
  end if;

  if(nops(indets(out))>0) then
    if(eqPlain = "yes") then
      if (printLevel >= 1) then print("Computing plain equations...") end if;
      eqsPlain := []; 
      for i from 1 to nops(symbSol) do
        if (printLevel >= 1) then print("plain equation", i, ": ", symbSol[i]) end if;
if ((i = 1) or (i = 4)) then
        # We check if the equations contain roots of equations involving the unknowns
        if(nops(indets(symbSol[i])) > nops(vars)) then  # Extension with unknowns
          eqFace := "random";
        else # Extension without unknowns
          eqFace := "indeterminate";
        end if;

        # Why we dont use "indeterminate"??
        # Check why would we prefer to use random equations...
        #eqFace := "random";

        if(eqFace = "indeterminate") then
          L := getExtension(symbSol[i]);
          if (hasRealRoot(L) = 1) then
            if (printLevel >= 1) then print("Real root found") end if;
            eqsStep := getEquationsPlain(symbSol[i], cfv, out, getIndet(symbSol[i]));
            #print("Equation added: ", eqsStep);
            eqsPlain := [op(eqsPlain), op(eqsStep)]:
          else 
            if (printLevel >= 1) then print("No real roots, nothing to do.") end if;
          end if;
        else 
          eqsStep := getEquationsPlainRandom(symbSol[i], cfv, out, indets(cfv));
          eqsPlain := [op(eqsPlain), op(eqsStep)]:
        end if;

        if(incremental_f = "yes") then
          if (printLevel >= 1) then print("Solving plain equations (incremental)...") end if;
          out := solveEquations(out, eqsPlain):
          out4 := out;
          if(nops(indets(out))>0) then
            if (printLevel >= 1) then print("Zero equations after incremental plain...") end if;
            out := zeroRows(out):
            out5 := out;
            out := zeroDetSRows(out,2):
            out6 := out;
          end if;
          if (printLevel >= 1) then 
            print("indets after plain equations", nops(indets(out)));
          end if;
          eqsPlain := [];
        end;
end if;        
      end do:

      if(incremental_f = "no") then 
        if (printLevel >= 1) then print("Solving plain equations...") end if;
        if (nops(eqsPlain) > 0) then 
          out := solveEquations(out, eqsPlain):
        else 
          print("No equations found. Check!");
        end if;
        out4 := out;
      
        if(nops(indets(out))>0) then
          if (printLevel >= 1) then print("Zero equations after non-incremental plain...") end if;

          out := zeroRows(out):
          out5 := out;

          out := zeroDetSRows(out,2):
          out6 := out;
        end if;
        if (printLevel >= 1) then 
          print("rank after plain equations: ", randomRank(out));
          print("indets after plain equations", nops(indets(out)));
        end if;
      end;
    end if;
  end if;


  if(nops(indets(out))>0) then
    # Equate all non-rational coefficients to 0. 
    # This is not a necessary condition.
    if(forceRational_f = "yes") then 
      if (printLevel >= 1) then print("We force all indeterminates with non-rational coefficients to be 0...") end if;
      L := getExtension(out);

      out := primitiveMatrix(out);
      out6 := out;

      out := nonRatCoef(out, nRows, L):
      out7 := out;
    end if;
    
    if (printLevel >= 1) then print("Zero equations...") end if;
    out := zeroRows(out):
  end if;

  out;
end proc:

#########################################################################
# Evaluates a solution at random values until the dimension of
# the space generated by all the evaluations is equal to the
# expected dimension of the space.
#
# cf is the vector of monomials.
# The matriz equation for the original polynomial is
# f = cf^T * Q * cf
# so if we find values of the variables such the solution has a real root,
# we can replace this solution in the monomials in cf and obtain a vector
# such that Q must satisfy the equation cf^T * Q * cf = 0

#########################################################################

# solution -> solution of f = 0 (or q1 = q2 = ... = qs = 0)
# cf -> vector of monomials of degree d in n variable (for a polynomial f
# of degree 2d in n variables).

randomSolutions := proc(solution, cf, vars, n)
  local vecs, cfev, randomSol, randomSolAll, i, j, h, good;
  local monomials, cfNamesList, expectedRank, mSize, first, nrank, M;
  local MNew, nrankNew;
  local boundRank, den, coefList, rv, rvEval;  
  local indetsCFEV, trueIndets;
  
  print("randomSolutions begin (randomized search of real solutions)");

  vecs := [];
  cfev := eval(cf, solution);

  den := productDenominator(cfev);
  if(degree(den)>0) then
    boundRank := 0;
  else 
    boundRank := 1;
  end if;


  indetsCFEV := indets(cfev);
  trueIndets := [];
  for j from 1 to nops(indetsCFEV) do
    if(hasExtension(indetsCFEV[j]) = 0) then
      boundRank := 0;
    end if;
  end do;
  
  trueIndets := indetsCFEV;

  if(nops(indets(cfev)) > 0) then

    if(boundRank = 1) then
      monomials := [];

      unassign('cfNames');
      for i from 1 to LinearAlgebra[Dimension](cfev) do
        
        coefList := coeffs(cfev[i], trueIndets, 'cfNames'):
        cfNamesList := [cfNames];
        if(nops(indets(cfNames)) > 0) then 
          for j from 1 to nops(cfNamesList) do
            if(hasExtension(cfNamesList[j]) = 0) then
              monomials := [op(monomials), cfNamesList[j]];
            end if;
          end do;
        end if;
        unassign('cfNames');
      end do:
      
      expectedRank := nops(convert(monomials,set));
      if (expectedRank > n) then
        expectedRank := n;
      end if;
    else 
      expectedRank := n;
    end;

    mSize := LinearAlgebra[Dimension](cfev);
    first := 1;
    i := 0;
    nrank := 0:


    while ((i <= n) and (nrank < expectedRank)) do
      rv := LinearAlgebra[RandomVector](nops(vars)):
      rvEval := Equate(Vector([op(vars)]), LinearAlgebra[RandomVector](nops(vars)));
      if(eval(den, rvEval) <> 0) then
        randomSol := eval(cfev, rvEval):
        if (hasRealRoot(getExtension(randomSol)) = 1) then
          if(first = 1) then
            MNew := randomSol;
            first := 0;
          else 
            MNew := <M|randomSol>;
          end if;
          nrankNew := LinearAlgebra[Rank](evalf(MNew));
          if (nrankNew > nrank) then
            vecs := [op(vecs), randomSol];
            M := MNew;
          end if;
          nrank := nrankNew;
        end if;
      end if;
      i := i + 1;
    end do:
  else 
    # The provided solution has no indeterminates to specify
    vecs := [eval(cfev, solution)];
  end if:
  if (nops(vecs) = 0) then
    print("No real solutions found.");
  else 
    print("Total number of real points found for these equations:", nops(vecs));
  end if;
  vecs;
end proc:

#########################################################################
# Evaluates a solution at random values and computes the trace of the 
# resulting vector until the dimension of the space generated by all 
# the trace vectors is equal to the expected dimension of the space.
#########################################################################

# If boundRank = 1 it estimates a bound for the number of independent
# solutions. This can cause problems with procedure coeffs, it should
# not be used when the algebraic extension contains unknowns
randomTraceSolutions := proc(solution, cf, vars, n)
  local vecs, cfev, randomSol, randomSolAll, i, j, h, k, m, good;
  local mSize, monomials, cfNamesList, expectedRank, first, nrank, L, vecTrace;
  local MNew, nrankNew, M;

  local boundRank, den, rv, rvEval;

  vecs := [];
  cfev := eval(cf, solution);

  den := productDenominator(cfev);

  if(degree(den)>0) then
    boundRank := 0;
  else 
    boundRank := 1;
  end if;
  mSize := LinearAlgebra[Dimension](cfev);

  if(boundRank = 1) then
    monomials := [];
    unassign('cfNames');
    for i from 1 to LinearAlgebra[Dimension](cfev) do

      # We store the monomials in cfNames
      cfNamesList := [cfNames];
      if(nops(indets(cfNames)) > 0) then 
        for j from 1 to nops(cfNamesList) do
          if(hasExtension(cfNamesList[j]) = 0) then
            monomials := [op(monomials), cfNamesList[j]];
          end if;
        end do;
      end if;
      unassign('cfNames');
    end do:
    expectedRank := nops(convert(monomials,set));
    expectedRank := nops(convert(monomials,set));
    if (expectedRank > n) then
      expectedRank := n;
    end if;
  else 
    expectedRank := n;
  end if;

  # Choose a better m!!
  m := 5*n;

  first := 1;
  i := 0;
  nrank := 0:
  while ((i <= m) and (nrank < expectedRank)) do
    rv := LinearAlgebra[RandomVector](nops(vars)):
    rvEval := Equate(Vector([op(vars)]), LinearAlgebra[RandomVector](nops(vars)));

    if(eval(den, rvEval) <> 0) then
      randomSol := eval(cfev, rvEval):
      if(hasRationalSolution(randomSol) = 0) then
        L := getExtension(randomSol):
        if(hasRealRoot(L) = 1) then
          vecTrace := Vector(mSize):
          for k from 1 to mSize do
            vecTrace[k] := evala(:-Trace(randomSol[k], L, {}));
          end do:
          if(first = 1) then
            MNew := vecTrace;
            first := 0;
          else 
            MNew := <M|vecTrace>;
          end if;
          nrankNew := LinearAlgebra[Rank](MNew);
          if (nrankNew > nrank) then
            vecs := [op(vecs), vecTrace];
            M := MNew;
            nrank := nrankNew;
          end if;
        end if:
      end if:
      i := i + 1;
    end if;
  end do:

  vecs;
end proc:


# Computes the sum of square decompostion for a matrix in the spectrahedron
# Vector v is the vector of monomials indexing the columns of Q
matrixToPoly := proc(Q,v)
  local n, p, a, ci, ri, ai, pi;
  local i, j;
  local f, cfs, cfPlain, vars, cfv, cfvt, mSize, MM;
  local ex, rr, sol, MMS;
  local L, DD, Lt, aD, aDsorted;
  local cFail, nRows, nCols;

  # Check if conditions are met for SOS decomposition
  if(nops(indets(Q))> 0) then
    print("The computed Matrix contains indeterminates. SOS decomposition cannot be computed.");
    print("Q: ", Q);
  end if;

  nCols, nRows := LinearAlgebra[Dimension](Q);
  
  cFail := 0;
  for i from 1 to nCols do
    if((Q[i,i]) = 0) then
      for j from 1 to nCols do
        if(Q[i,j] <> 0) then
          cFail := 1;
        end if;
      end;
    end if;
  end;

  if(cFail = 1) then
    print("The computed matrix is not positive semidefinite (non-zero entries below a zero element in the diagonal). SOS decomposition may not exist.");
    0,Q,0,0,0,0:
  else 
    # Matrix for decomposition o3 as sum of rational squares, 
    # following SOS (Parrillo et al.)
    try
      print("Computing Cholesky decomposition...");  
      L, Lt := MatrixDecomposition(Q, method = Cholesky);
      DD := IdentityMatrix(nCols);
    catch:
      print("Cholesky decomposition failed. Matrix is not positive definite. We use LDLt decomposition.");
      try
        L, DD, Lt := MatrixDecomposition(Q, method = LDLt);
      catch: 
        print("Matrix decomposition failed for output matrix. Please check!");
        L := IdentityMatrix(nCols);
        DD := Q;
        Lt := L;
      end try;
    end try;
    
    aD := getDiag(DD);
    aDsorted := sort(abs(evalf(Vector(aD))), `>`, output = ['permutation']);

    n := LinearAlgebra[Rank](Q);
    p:=[];
    a:=[];
    f:=0;
    for i from 1 to n do
      ci := LinearAlgebra[Column](L,aDsorted[i]);
      ai := aD[aDsorted[i]];
      pi := LinearAlgebra[Transpose](Vector(v)) . ci;
      p := [op(p), pi];
      a := [op(a), ai];
      f:=f+ai*pi^2;
    end;
    L, DD, Lt, f,a,p:
  end if;
end proc:

polyToMatrix := proc(f)
  local i, j;
  local fExp, cfs, cfPlain, vars, mVars, cfv, cfvt, mSize, MM;
  local ex, rr, sol, MMS;

  # Matrix for decomposition o3 as sum of rational squares, 
  # following SOS (Parrillo et al.)
  fExp := expand(f);
  cfs, cfPlain, vars := getVars(fExp);
  
  cfv := Vector(cfPlain): 
  cfvt := LinearAlgebra[Transpose](cfv):

  mSize := nops(cfPlain);

  MM := Matrix(mSize):
  for i to mSize do 
    for j from i to mSize do 
      MM[i, j] := a_0[i, j]; 
      MM[j, i] := a_0[i, j];
    end do;
  end do; 
  
  ex := cfvt . MM . cfv:
  ex := expand(ex):

  # We find equations on the coefficients of MM so that we get a solution
  # to v^t MM v = o3
  rr := [coeffs(ex-fExp, vars)]:
  
  sol := solve(Equate(rr,Vector(nops(rr)))):
  MMS := eval(MM, sol):
  mVars := indets(MMS);
  MMS, mVars, cfPlain;
end proc:

# Matrix of the original polynomials
decompositionToMatrix := proc(p, v)
  local i, o, MT, MNEW;

  for i from 1 to nops(p) do 
    o := getCoeffs(expand(p[i]), v):
    MT := o.LinearAlgebra[Transpose](o):
    if(i = 1) then
      MNEW := MT:
    else 
      MNEW := MNEW + MT:
    end if;
  end do:
  MNEW := simplify(MNEW):
  MNEW;
end proc:




#######################################################################
# Looks for principal submatrices of dimension s of the given matrix 
# will null determinant and for any such matrix found it computes
# the corresonding equations for facial reduction
#######################################################################

zeroDetSRows := proc(M, s)
  local out, i, eqsNew, nRows, nCols, matC, vecC, solT, sol123;
  local vNonZero, l, MSub, v, kern, vKern, eqs;
      
  nRows, nCols := LinearAlgebra[Dimension](M);
  eqsNew := [];
  vNonZero := [seq(`if`(M[i,i]=0,NULL,i), i=1..nRows)];
  l := listSubsets(vNonZero, s);
  
  for i from 1 to nops(l) do
    MSub := LinearAlgebra[SubMatrix](M, l[i], l[i]):
    if(randomRank(MSub) < s) then
      v := Vector(nRows);
      kern:=LinearAlgebra[NullSpace](MSub);
      if(nops(kern) > 0) then 
        vKern := cancelDenominator(kern[1]);
        v[l[i]] := vKern;
        eqs := M.v;
        eqsNew := [op(eqsNew), op(Equate(eqs, Vector(nRows)))]:
      end if;
    end if;
  end do:
 
  if(nops(eqsNew) > 0) then
    matC, vecC := LinearAlgebra[GenerateMatrix](eqsNew,indets(M)):
    
    sol123 := LinearAlgebra[LinearSolve](matC, vecC):
    
    solT := Equate([op(indets(M))], sol123):
    out := eval(M, solT):
  else
    out := M;
  end if;

  out:
end proc:

#######################################################################
# Given a matrix M it computes a primitive element for all 
# the extensions involved in the matrix and writes all the entries of
# M in terms of this element
#######################################################################

primitiveMatrix := proc(M)
  local aAlg, aPrim, MM;
  aAlg := evala(Algfield(M)); 
  aPrim := evala(Primfield(aAlg[3]));
  MM := eval(M, aPrim[2]):
  MM;
end proc:


#######################################################################
# Computes the trace of a vector
#######################################################################

vectorTrace := proc(v)
  local aAlg, aPrim, MM, n, vPrim, vTrace, i, L;
  aAlg := evala(Algfield(v));
  aPrim := evala(Primfield(aAlg[3]));
  n := LinearAlgebra[Dimension](v);
  vPrim := Vector(n);
  vTrace := Vector(n);
  for i from 1 to n do
    vPrim[i]:=eval(v[i], aPrim[2]);
  end do:
  L := getExtension(vPrim);
  for i from 1 to n do
    vTrace[i] := evala(:-Trace(vPrim[i], L, {}));
  end do:
  vTrace;
end proc:



#######################################################################
# Given a matrix M with unknows in the entries and a solution v to 
# M.v = 0
# it solves the system and replace the entries by the solution
#######################################################################

reduceByLinearEquation := proc(M, v)
  local out, eqs, solEq, nRows, nCols;
  local matC2, vecC2, solLinear;
  
  nRows, nCols := LinearAlgebra[Dimension](M);
  
  eqs := Equate(M.v, Vector(nCols));

  solEq := solve(eqs);

  matC2, vecC2 := LinearAlgebra[GenerateMatrix](eqs,indets(eqs)):
  
  solLinear := LinearAlgebra[LinearSolve](matC2, vecC2):

  out := eval(M, solEq);
end proc:

# Fix for some weird Maple output
reduceByLinearEquationLinear := proc(M, v)
  local out, eqs, solEq, nRows, nCols;
  local matC2, vecC2, solLinear, solT2;
  
  nRows, nCols := LinearAlgebra[Dimension](M);
  
  eqs := Equate(M.v, Vector(nCols));

  eqs := simplify(eqs);
  matC2, vecC2 := LinearAlgebra[GenerateMatrix](eqs,indets(eqs)):

  solLinear := LinearAlgebra[LinearSolve](matC2, vecC2):
  
  solT2 := Equate([op(indets(eqs))], solLinear):

  out := eval(M, solT2);
end proc:

# Checks the minimum eigenvalue obtained numerically.
# If it is negative, something went wrong, there is no 
# possible SOS decomposition.

checkMinEig := proc(M)
  local nRows, nCols, rr, MMT, tVars, vSol, A10, e10;
  nRows, nCols := LinearAlgebra[Dimension](M);  
  rr := randomRank(M);
  MMT, tVars, vSol := numericSolverSubmatrix(M, rr):
  
  A10 := evalMat(M, tVars, vSol):
  e10 := eig(A10);
  print("minimum eigenvalue", min(e10));
end proc:


evalSolution := proc(eq, sol)
  local eqEval, i;
  eqEval := [];
  for i from 1 to nops(eq) do
    eqEval := {op(eqEval), op(Equate([lhs(eq[i])], [eval(rhs(eq[i]),sol)]))};
  end do;
  eqEval;
end proc: 

# Computes the product of the denominators of a vector
# Using lcm instead of product can lead to unexpected results with some polynomial appearing as denominator.
productDenominator := proc(v)
  local i, n;
  local vNew, den, denOld;

  vNew := v;
  n := LinearAlgebra[Dimension](v);
  den := 1;
  for i from 1 to n do
    denOld := den;
    den := den * denom(v[i]);
    if(denom(den)<>1) then
      print ("OUCH!!!!");
      print ("v[i]", v[i]);
      print ("denom(v[i])", denom(v[i]));
      DEBUG();
    end if;

  end do;
  den;
end proc:

# Computes the common denominator of a vector
commonDenominator := proc(v)
  local i, n;
  local vNew, den, denOld;
  vNew := v;
  n := LinearAlgebra[Dimension](v);
  den := 1;
  for i from 1 to n do
    denOld := den;
    den := lcm(den, denom(v[i]));
    if(denom(den)<>1) then
      print ("OUCH!!!!");
      print ("v[i]", v[i]);
      print ("denom(v[i])", denom(v[i]));
      DEBUG();
    end if;

  end do;
  den;
end proc:

# Multiplies by the common denominator of a vector
cancelDenominator := proc(v)
  local vNew, n, den, i;
  vNew := v;
  n := LinearAlgebra[Dimension](v);
  den := 1;
  for i from 1 to n do
    den := lcm(den, denom(v[i]));
  end do;
  for i from 1 to n do
    vNew[i] := simplify(den * v[i]);
  end do;
  vNew;
end proc:


#######################################################################
# Looks for principal submatrices of dimension s of the given matrix 
# will null determinant and for any such matrix found it computes
# the corresonding equations for facial reduction
#######################################################################

zeroDetSys := proc(M, s)
  local out, i, eqsNew, nRows, nCols, matC, vecC, solT, sol123;
  local vNonZero, l, MSub, v, kern, eqs;
  local eq;
      
  nRows, nCols := LinearAlgebra[Dimension](M);
  eqsNew := [];
  vNonZero := [seq(`if`(M[i,i]=0,NULL,i), i=1..nRows)];
  l := listSubsets(vNonZero, s);

  eqs := [];
  for i from 1 to nops(l) do
    MSub := LinearAlgebra[SubMatrix](M, l[i], l[i]):
    eq := Determinant(MSub) + (vn[i])^2;
    eqs := [op(eqs), eq];
  end do:
  eqs:
end proc:

# Find a set of indices of rows of M such that the square submatrix
# on those indices has maximal rank.
linIndepRows := proc(M, rRank := -1)
  local i, nRows, nCols;
  local rndRank, subind, MSub, subsub;
  
  if(rRank = -1) then 
    rndRank := randomRank(evalf(M));  
  else
    rndRank := rRank;
  end if;
  
  nRows, nCols := LinearAlgebra[Dimension](M);
  
  subind :=  [seq(i, i = 1 .. nRows)];
  while(nops(subind) > rndRank) do
    for i from 1 to nops(subind) do
      subsub := subsop(i=NULL, subind);
      MSub := SubMatrix(M, subsub, subsub);
      if(randomRank(evalf(MSub)) = rndRank) then
        subind := subsub;
        break;
      end if;
    end do:
  end do:
  subind;
end proc:


# Procedure for computing ghost solutions associated to a submatrix
# of the quadratic form
solveSubmatrixGeneral := proc(M, vv)
  local i, nRows, nCols;
  local Q4, Q4S3, vx, vxt;
  local ff, fco, newS, vFull, vecs;

  Q4:=M;
  nRows, nCols := LinearAlgebra[Dimension](M);

  Q4S3 := SubMatrix(Q4, vv,vv):
  vx := Vector(nops(vv));
  for i from 1 to nops(vv) do
    vx[i] := z[i];
  end;
  vxt := LinearAlgebra[Transpose](vx);
  ff := expand(vxt . Q4S3 . vx);

  # We must find the values of (z0, z1, z2) for which ff is 0 for any choice of the 
  # two parameters {a_0[4, 6], a_0[7, 9]} of the matrix Q4.
  # For this, we compute the coefficient of each of the two parameters and the independent term.

  fco := coeffs(ff, indets(Q4));

  # We get a sytem of the polynomial equations in (z0, z1, z2) and we solve it using command solve.
  newS := solve(Equate([fco], Vector(nops([fco]))));

  vFull := Vector(nRows);

  for i from 1 to nops(vv) do
    vFull[vv[i]]:=z[i];
  end do:
  
  vecs := [];
  for i from 1 to nops([newS]) do
    vecs := [op(vecs), eval(vFull, [newS][i])];
  end;

  [[fco], [newS], vecs];
end proc;

homogenize := proc(f, z)
  local d, vars, mon, fNew, i;
  d := degree(f);
  vars := indets(f);
  mon := [op(expand(f))];
  fNew := 0;
  
  for i from 1 to nops(mon) do
    fNew := fNew + mon[i]*z^(d - degree(mon[i]));
  end;
  fNew;
end proc;

isHomogeneous := proc(f, z)
  local isH, d, mon, i;
  isH := true;
  d := degree(f);
  mon := [op(expand(f))];
  for i from 1 to nops(mon) do
    if(degree(mon[i]) < d) then
      isH := false;
    end if;
  end;
  isH;
end proc;


polyToMatrixVars := proc(f, cfPlain)
  local i, j;
  local fExp, cfs, vars, mVars, cfv, cfvt, mSize, MM;
  local ex, rr, sol, MMS;

  # Matrix for decomposition o3 as sum of rational squares, 
  # following SOS (Parrillo et al.)
  fExp := expand(f);
  
  cfv := Vector(cfPlain): 
  cfvt := LinearAlgebra[Transpose](cfv):

  mSize := nops(cfPlain);

  MM := Matrix(mSize):
  for i from 1 to mSize do 
    for j from i to mSize do 
      MM[i, j] := a_0[i, j]; 
      MM[j, i] := a_0[i, j];
    end do;
  end do; 
  
  ex := cfvt . MM . cfv:
  ex := expand(ex):

  # We find equations on the coefficients of MM so that we get a solution
  # to v^t MM v = o3
  rr := [coeffs(ex-fExp, cfPlain, 'cft')]:
  
  sol := solve(Equate(rr,Vector(nops(rr))), indets(MM)):
  MMS := eval(MM, sol):
  mVars := indets(MMS);
  MMS, mVars, cfPlain;
end proc:

# Computes the minors of given size
minorsDet := proc(A, n0, d)
  local l, i, m;
  l := listSubsets([seq(i,i=1..n0)], d);
  m := [];
  for i from 1 to nops(l) do
    m := [op(m), Determinant(LinearAlgebra[SubMatrix](A, l[i], l[i]))];
  end do;
  m;
end proc:

# Computes the dimension of the Gram spectrahedrum
dimSimplex := proc(lV)
  local M, i, j, r, nVecs; 
  local dimVec;
  
  nVecs := nops(lV);
  dimVec := Dimension(lV[1]);
  M := Matrix(nVecs-1, dimVec);
  for i from 2 to nVecs do
    for j from 1 to dimVec do
      M[i-1, j] := lV[i][j]-lV[1][j];
    end do;
  end do;
  r := Rank(M);
  print("r = Rank(M)", r);
  print("SVD(M)", SingularValues(M));
  r;
end proc:


# For all zero coordinates of A (up to d digits), solve the corresponding equation of B to zero.
solveToZero := proc(A, B, d)
  local i, j, nrows, ncols;
  local a, eqs;
  local Bt, ss;
  
  Bt := B;
  nrows, ncols := LinearAlgebra[Dimension](Bt);
  eqs := [];
  for i from 1 to ncols do
    for j from i to nrows do
      if (nops(indets(Bt[i,j])) > 0) then
        if((abs(frac(A[i,j]))<10^(d*(-1))) or (abs(1-frac(A[i,j]))<10^(d*(-1)))) then 
          a := rrounde(A[i,j], d);
          eqs := Equate([Bt[i, j]], [a]):
        else 
          a := rrounde(A[i,j], d);
          eqs := Equate([Bt[i, j]], [a]):
        end if;
        if (nops(eqs) > 0) then 
          ss := solve(eqs);
          if (nops(ss) > 0) then 
            Bt := eval(Bt, solve(eqs));
          end if;
        end if;
      end if;
      
    end do;
  end do;
  Bt;
end proc;
      


end module; # rationalSOS
