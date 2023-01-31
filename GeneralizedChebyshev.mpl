
GeneralizedChebyshev := module()
description "A collection of procedures for generalized Chebyshev Polynomials";
option package;

with(combinat):
with(GroupTheory):
with(LinearAlgebra):

export Base, coroot, WeightMatrix, FWeight, RWeylGroupGen, RWeylGroup, ZWeylGroup, FundomVertexCoefficient, VertexFundom, VertexTOrbitSpace, FundamentalInvariant, HighestRoot, MonomialExponent, ChebyshevLevel, ChebyshevDegExp, ROrbit, ZOrbit, GeneralizedCosine, RGeneralizedCosine, TMultiply, TPolyRecurrence, HermiteMatrix, RHermiteMatrix, InvariantRewrite, THermiteMatrix, RTHermiteMatrix, TLocalizedPMI, TArchimedeanPMI, ChebyshevSDPdata, ChebyshevArchimedeanSDP, Pull, TruncatedTMomentMatrix;

local OrthogonalMatrixConstructor, DiagonalMatrixConstructor, esp, MonomialMultiply, TruncatedMonomialMomentMatrix, PrimalConstraintMatrix, DualConstraintMatrix, SolutionSet, MonomialExponent2, MonomialRewrite, MonomialHermiteMatrix, MonomialLocalizedPMI, CoeffInMatrix, THermiteEntries, RTHermiteEntries;

Base:=proc(Type,n) # base of a root system
local i;
 if   Type = A then
  [seq(convert(Column(IdentityMatrix(n+1),i)-Column(IdentityMatrix(n+1),i+1),list),i=1..n)]
 elif Type = B then
  [seq(convert(Column(IdentityMatrix(n),i)-Column(IdentityMatrix(n),i+1),list),i=1..n-1),[seq(0,i=1..n-1),1]]
 elif Type = C then
  [seq(convert(Column(IdentityMatrix(n),i)-Column(IdentityMatrix(n),i+1),list),i=1..n-1),[seq(0,i=1..n-1),2]]
 elif Type = D then
  [seq(convert(Column(IdentityMatrix(n),i)-Column(IdentityMatrix(n),i+1),list),i=1..n-1),convert(Column(IdentityMatrix(n),n-1)+Column(IdentityMatrix(n),n),list)]
 elif Type = F and n = 4 then
  [[0,1,-1,0],[0,0,1,-1],[0,0,0,1],[1,-1,-1,-1]/2]
 elif Type = G and n = 2 then
  [[1,-1,0],[-2,1,1]]
 else
  printf("Error: root system must be of Type A, B, C, D, F, G")
 fi;
end proc:

coroot:=proc(r::list) # coroot of the input
 local scalar, i;
 scalar:=convert([seq(r[i]^2,i=1..nops(r))],`+`);
 2/scalar*r;
end proc:

WeightMatrix:=proc(Type,n) # the matrix containing the fundamental weights as columns
local i, j;
 if Type = A then
  Transpose(Matrix([seq(1/(n+1)*((n+1-i)*convert([seq(convert(Column(IdentityMatrix(n+1),j),list),j=1..i)],`+`)-i*convert([seq(convert(Column(IdentityMatrix(n+1),j),list),j=i+1..n+1)],`+`)),i=1..n)]))
 elif Type = G then
  Transpose(Matrix(2, 3, [[0, -1, 1], [-1, -1, 2]]))
 elif Type = B or Type = C or Type = D or Type = F then
  Matrix([seq(coroot(Base(Type,n)[i]),i=1..n)])^(-1)
 else
  printf("Error: root system must be of Type A, B, C, D, F, G")
 fi;
end proc:

FWeight:=proc(Type,n) # the list of fundamental weights
local i;
 [seq(convert(Column(WeightMatrix(Type,n),i),list),i=1..n)]
end proc:

OrthogonalMatrixConstructor:=proc(Type,n,i,j)
 if i=j then
  Base(Type,n)[j]
 else
  FWeight(Type,n)[j]
 fi;
end proc:

DiagonalMatrixConstructor:=proc(n,i,j)
 if i=j then
  convert(Column(-IdentityMatrix(n),j),list)
 else
  convert(Column( IdentityMatrix(n),j),list)
 fi;
end proc:

RWeylGroupGen:=proc(Type,n) option remember; # generators of the Weyl group as a real orthogonal matrix group
local i, j, k, N, diag;
 if   Type = A then
  {seq(seq(Matrix([seq(convert(Column(IdentityMatrix(n+1),k),list),k=1..i-1),convert(Column(IdentityMatrix(n+1),j),list),seq(convert(Column(IdentityMatrix(n+1),k),list),k=i+1..j-1),convert(Column(IdentityMatrix(n+1),i),list),seq(convert(Column(IdentityMatrix(n+1),k),list),k=j+1..n+1)]),i=1..j-1),j=1..n+1)};
 elif Type = G and n = 2 then
  {Matrix(3, 3, [[0, 1, 0], [1, 0, 0], [0, 0, 1]]), Matrix(3, 3, [[-1/3, 2/3, 2/3], [2/3, 2/3, -1/3], [2/3, -1/3, 2/3]])}
 elif Type = B or Type = C or Type = D or Type = F then
  for i from 1 to n do
   N[i]:=Matrix([seq(OrthogonalMatrixConstructor(Type,n,i,j),j=1..n)]):
  od:
  for i from 1 to n do
   diag[i]:=Matrix([seq(DiagonalMatrixConstructor(n,i,j),j=1..n)]):
  od:
  for i from 1 to n do
   {seq(Transpose(N[i]^(-1).diag[i].N[i]),i=1..n)}
  od:
 else
  printf("Error: root system must be of Type A, B, C, D, F, G")
 fi;
end proc:

RWeylGroup:=proc(Type,n) option remember; # the Weyl group as a real orthogonal matrix group
local W;
 W:=Group(RWeylGroupGen(Type,n));
 [op(Elements(W))];
end proc:

ZWeylGroup:=proc(Type,n) option remember; # the Weyl group as an integer matrix group
local ZWeylGroupGen, mat, W;
 ZWeylGroupGen:=map(mat-> MatrixInverse(WeightMatrix(Type,n)).mat.WeightMatrix(Type,n),RWeylGroupGen(Type,n));
 W:=Group(ZWeylGroupGen);
 [op(Elements(W))];
end proc:

FundamentalInvariant:=proc(Type,n)
 local k, l, orb;
 global x;
 x:='x';
 if Type=A then
  [seq(expand(binomial(n+1,l)^(-1)*esp([x[1],seq(x[k]*x[k-1]^(-1),k=2..n),x[n]^(-1)],l)),l=1..n)]
 elif Type=C then
  [seq(expand(binomial(n,l)^(-1)*2^(-l)*esp([x[1]+x[1]^(-1),seq(x[k]*x[k-1]^(-1)+x[k]^(-1)*x[k-1],k=2..n)],l)),l=1..n)]
 elif Type=B then
  [seq(expand(binomial(n,l)^(-1)*2^(-l)*esp([x[1]+x[1]^(-1),seq(x[k]*x[k-1]^(-1)+x[k]^(-1)*x[k-1],k=2..n-1),x[n]^2*x[n-1]^(-1)+x[n]^(-2)*x[n-1]],l)),l=1..n-1),expand(2^(-n)*convert(map(orb->convert([seq(x[l]^(orb[l]),l=1..n)],`*`),ZOrbit(Type,n,[seq(0,k=1..n-1),1])),`+`))]
 elif Type=D then
  [seq(expand(binomial(n,l)^(-1)*2^(-l)*esp([x[1]+x[1]^(-1),seq(x[k]*x[k-1]^(-1)+x[k]^(-1)*x[k-1],k=2..n-2),x[n]*x[n-1]*x[n-2]^(-1)+x[n]^(-1)*x[n-1]^(-1)*x[n-2],x[n]*x[n-1]^(-1)+x[n]^(-1)*x[n-1]],l)),l=1..n-2),expand(2^(1-n)*convert(map(orb->convert([seq(x[l]^(orb[l]),l=1..n)],`*`),ZOrbit(Type,n,[seq(0,k=1..n-2),1,0])),`+`)),expand(2^(1-n)*convert(map(orb->convert([seq(x[l]^(orb[l]),l=1..n)],`*`),ZOrbit(Type,n,[seq(0,k=1..n-1),1])),`+`))]
 elif Type=F and n=4 then
  [x[2]/x[1]^2 + x[3]^2/(x[1]*x[2]) + 1/x[1] + x[4]^2/x[1] + x[3]^2/(x[1]*x[4]^2) + x[2]*x[4]^2/(x[1]*x[3]^2) + x[2]/(x[1]*x[4]^2) + x[2]/x[1] + x[2]^2/(x[1]*x[3]^2) + x[4]^2/x[2] + x[3]^2/(x[2]*x[4]^2) + x[3]^2/x[2] + x[2]/x[3]^2 + x[2]*x[4]^2/x[3]^2 + x[2]/x[4]^2 + x[1]*x[3]^2/x[2]^2 + x[1]/x[2] + x[1]*x[4]^2/x[2] + x[1]*x[3]^2/(x[2]*x[4]^2) + x[1]*x[4]^2/x[3]^2 + x[1]/x[4]^2 + x[1] + x[1]*x[2]/x[3]^2 + x[1]^2/x[2],
   x[1]*x[2]*x[4]^4/x[3]^4 + x[1]*x[2]/(x[3]^2*x[4]^2) + x[1]*x[2]*x[4]^2/x[3]^2 + x[1]*x[2]/x[4]^4 + x[1]*x[2]/x[4]^2 + x[1]*x[2]^2/x[3]^4 + x[1]*x[2]^2*x[4]^2/x[3]^4 + x[1]*x[2]^2/(x[3]^2*x[4]^2) + x[1]^2*x[3]^2/x[2]^3 + x[1]^2*x[3]^2*x[4]^2/x[2]^3 + x[1]^2*x[3]^4/(x[2]^3*x[4]^2) + x[1]^2*x[4]^2/(x[2]*x[3]^2) + x[1]^2*x[4]^4/(x[2]*x[3]^2) + x[1]^2/(x[2]*x[4]^2) + x[1]^2*x[4]^2/x[2] + x[1]^2*x[3]^2/(x[2]*x[4]^4) + x[1]^2*x[3]^2/(x[2]*x[4]^2) + x[1]^2*x[2]*x[4]^2/x[3]^4 + x[1]^2*x[2]/(x[3]^2*x[4]^2) + x[1]^2*x[2]/x[3]^2 + x[1]^3*x[3]^2/x[2]^3 + x[1]^3*x[4]^2/x[2]^2 + x[1]^3*x[3]^2/(x[2]^2*x[4]^2) + x[1]^3*x[4]^2/(x[2]*x[3]^2) + x[1]^3/(x[2]*x[4]^2) + x[1]^3/x[3]^2 + x[3]^4/(x[1]*x[2]^2*x[4]^2) + x[3]^4/(x[1]*x[2]^2) + x[4]^2/(x[1]*x[2]) + x[4]^4/(x[1]*x[2]) + x[3]^2/(x[1]*x[2]*x[4]^2) + x[3]^2*x[4]^2/(x[1]*x[2]) + x[3]^4/(x[1]*x[2]*x[4]^4) + x[3]^4/(x[1]*x[2]*x[4]^2) + x[4]^4/(x[1]*x[3]^2) + x[3]^2/(x[1]*x[4]^4) + x[3]^2/x[1] + x[2]/(x[1]*x[3]^2) + x[2]*x[4]^4/(x[1]*x[3]^2) + x[2]*x[3]^2/(x[1]*x[4]^4) + x[2]^2*x[4]^2/(x[1]*x[3]^4) + x[2]^2*x[4]^4/(x[1]*x[3]^4) + x[2]^2/(x[1]*x[3]^2*x[4]^2) + x[2]^2*x[4]^2/(x[1]*x[3]^2) + x[2]^2/(x[1]*x[4]^4) + x[2]^2/(x[1]*x[4]^2) + x[2]^3/(x[1]*x[3]^4) + x[2]^3*x[4]^2/(x[1]*x[3]^4) + x[2]^3/(x[1]*x[3]^2*x[4]^2) + x[1]*x[3]^2*x[4]^2/x[2]^3 + x[1]*x[3]^4/(x[2]^3*x[4]^2) + x[1]*x[3]^4/x[2]^3 + x[1]*x[4]^2/x[2]^2 + x[1]*x[4]^4/x[2]^2 + x[1]*x[3]^2/(x[2]^2*x[4]^2) + x[1]*x[3]^2*x[4]^2/x[2]^2 + x[1]*x[3]^4/(x[2]^2*x[4]^4) + x[1]*x[3]^4/(x[2]^2*x[4]^2) + x[1]*x[4]^4/(x[2]*x[3]^2) + x[1]*x[3]^2/(x[2]*x[4]^4) + x[1]*x[3]^2/x[2] + x[1]/x[3]^2 + x[1]*x[4]^4/x[3]^2 + x[1]*x[3]^2/x[4]^4 + x[1]*x[2]*x[4]^2/x[3]^4 + x[3]^2/x[1]^3 + x[2]*x[4]^2/x[1]^3 + x[2]*x[3]^2/(x[1]^3*x[4]^2) + x[2]^2*x[4]^2/(x[1]^3*x[3]^2) + x[2]^2/(x[1]^3*x[4]^2) + x[2]^3/(x[1]^3*x[3]^2) + x[3]^2/(x[1]^2*x[2]) + x[3]^2*x[4]^2/(x[1]^2*x[2]) + x[3]^4/(x[1]^2*x[2]*x[4]^2) + x[2]*x[4]^2/(x[1]^2*x[3]^2) + x[2]*x[4]^4/(x[1]^2*x[3]^2) + x[2]/(x[1]^2*x[4]^2) + x[2]*x[4]^2/x[1]^2 + x[2]*x[3]^2/(x[1]^2*x[4]^4) + x[2]*x[3]^2/(x[1]^2*x[4]^2) + x[2]^3*x[4]^2/(x[1]^2*x[3]^4) + x[2]^3/(x[1]^2*x[3]^2*x[4]^2) + x[2]^3/(x[1]^2*x[3]^2) + x[3]^2*x[4]^2/(x[1]*x[2]^2) + x[3]^4/x[2]^3 + x[4]^4/x[2] + x[3]^4/(x[2]*x[4]^4) + x[2]*x[4]^4/x[3]^4 + x[2]/x[4]^4 + x[2]^3/x[3]^4 + x[2] + x[2]^2/x[1]^3 + x[1]^3/x[2] + x[1]^3/x[2]^2 + x[2]/x[1]^3 + 1/x[2],
   x[1]*x[3]^2*x[4]/x[2]^2 + x[1]*x[3]^3/(x[2]^2*x[4]^2) + x[1]*x[3]^3/(x[2]^2*x[4]) + x[1]*x[4]^2/(x[2]*x[3]) + x[1]*x[4]^3/(x[2]*x[3]) + x[1]*x[3]/(x[2]*x[4]^2) + x[1]*x[3]*x[4]/x[2] + x[1]*x[3]^2/(x[2]*x[4]^3) + x[1]*x[3]^2/(x[2]*x[4]) + x[1]*x[4]/x[3]^2 + x[1]*x[4]^3/x[3]^2 + x[1]/(x[3]*x[4]) + x[1]*x[4]^2/x[3] + x[1]*x[3]/x[4]^3 + x[1]*x[3]/x[4]^2 + x[1]*x[2]*x[4]/x[3]^3 + x[1]*x[2]*x[4]^2/x[3]^3 + x[1]*x[2]/(x[3]^2*x[4]) + x[1]*x[2]*x[4]/x[3]^2 + x[1]*x[2]/(x[3]*x[4]^2) + x[1]*x[2]/(x[3]*x[4]) + x[1]^2*x[3]/x[2]^2 + x[1]^2*x[3]*x[4]/x[2]^2 + x[1]^2*x[3]^2/(x[2]^2*x[4]) + x[1]^2*x[4]/(x[2]*x[3]) + x[1]^2*x[4]^2/(x[2]*x[3]) + x[1]^2/(x[2]*x[4]) + x[1]^2*x[4]/x[2] + x[1]^2*x[3]/(x[2]*x[4]^2) + x[1]^2*x[3]/(x[2]*x[4]) + x[1]^2*x[4]/x[3]^2 + x[1]^2/(x[3]*x[4]) + x[1]^2/x[3] + x[2]*x[4]^2/(x[1]^2*x[3]) + x[2]/(x[1]^2*x[4]) + x[2]*x[4]/x[1]^2 + x[2]*x[3]/(x[1]^2*x[4]^2) + x[2]*x[3]/(x[1]^2*x[4]) + x[2]^2*x[4]/(x[1]^2*x[3]^2) + x[2]^2/(x[1]^2*x[3]*x[4]) + x[2]^2/(x[1]^2*x[3]) + x[3]*x[4]/(x[1]*x[2]) + x[3]*x[4]^2/(x[1]*x[2]) + x[3]^2/(x[1]*x[2]*x[4]) + x[3]^2*x[4]/(x[1]*x[2]) + x[3]^3/(x[1]*x[2]*x[4]^2) + x[3]^3/(x[1]*x[2]*x[4]) + x[4]^2/(x[1]*x[3]) + x[4]^3/(x[1]*x[3]) + x[3]/(x[1]*x[4]^2) + x[3]*x[4]/x[1] + x[3]^2/(x[1]*x[4]^3) + x[3]^2/(x[1]*x[4]) + x[2]*x[4]/(x[1]*x[3]^2) + x[2]*x[4]^3/(x[1]*x[3]^2) + x[2]/(x[1]*x[3]*x[4]) + x[2]*x[4]^2/(x[1]*x[3]) + x[2]*x[3]/(x[1]*x[4]^3) + x[2]*x[3]/(x[1]*x[4]^2) + x[2]^2*x[4]/(x[1]*x[3]^3) + x[2]^2*x[4]^2/(x[1]*x[3]^3) + x[2]^2/(x[1]*x[3]^2*x[4]) + x[2]^2*x[4]/(x[1]*x[3]^2) + x[2]^2/(x[1]*x[3]*x[4]^2) + x[2]^2/(x[1]*x[3]*x[4]) + x[1]*x[3]*x[4]/x[2]^2 + x[1]*x[3]*x[4]^2/x[2]^2 + x[1]*x[3]^2/(x[2]^2*x[4]) + x[3]/x[1]^2 + x[3]*x[4]/x[1]^2 + x[3]^2/(x[1]^2*x[4]) + x[2]*x[4]/(x[1]^2*x[3]) + x[3] + 1/x[3] + x[3]^2*x[4]/x[2]^2 + x[3]^3/(x[2]^2*x[4]) + x[3]^3/x[2]^2 + x[4]/x[2] + x[4]^3/x[2] + x[3]/(x[2]*x[4]) + x[3]*x[4]^2/x[2] + x[3]^3/(x[2]*x[4]^3) + x[3]^3/(x[2]*x[4]^2) + x[2]*x[4]^2/x[3]^3 + x[2]*x[4]^3/x[3]^3 + x[2]/(x[3]*x[4]^2) + x[2]*x[4]/x[3] + x[2]/x[4]^3 + x[2]/x[4] + x[2]^2/x[3]^3 + x[2]^2*x[4]/x[3]^3 + x[2]^2/(x[3]^2*x[4]) + x[4]^3/x[3]^2 + x[4]^3/x[3] + x[3]/x[4]^3 + x[3]^2/x[4]^3,
   x[4]/x[1] + x[3]/(x[1]*x[4]) + x[3]/x[1] + x[2]/(x[1]*x[3]) + x[2]*x[4]/(x[1]*x[3]) + x[2]/(x[1]*x[4]) + x[3]/x[2] + x[3]*x[4]/x[2] + x[3]^2/(x[2]*x[4]) + x[4]/x[3] + x[4]^2/x[3] + 1/x[4] + x[4] + x[3]/x[4]^2 + x[3]/x[4] + x[2]*x[4]/x[3]^2 + x[2]/(x[3]*x[4]) + x[2]/x[3] + x[1]*x[4]/x[2] + x[1]*x[3]/(x[2]*x[4]) + x[1]*x[3]/x[2] + x[1]/x[3] + x[1]*x[4]/x[3] + x[1]/x[4]]
 elif Type=G and n=2 then
  [x[1]/6 + x[2]/(6*x[1]) + x[1]^2/(6*x[2]) + x[2]/(6*x[1]^2) + x[1]/(6*x[2]) + 1/(6*x[1]),x[2]/6 + x[2]^2/(6*x[1]^3) + x[1]^3/(6*x[2]) + x[1]^3/(6*x[2]^2) + x[2]/(6*x[1]^3) + 1/(6*x[2])]
 else
  printf("Error: root system must be of Type A, B, C, D, F, G")
 fi;
end proc:

HighestRoot:=proc(Type,n)
local i, j;
 if   Type = A then
  convert([seq(Base(Type,n)[i],i=1..n)],`+`)
 elif Type = B then
  Base(Type,n)[1] + 2*convert([seq(Base(Type,n)[j],j=2..n)],`+`)
 elif Type = C then
  2*convert([seq(Base(Type,n)[j],j=1..n-1)],`+`) + Base(Type,n)[n]
 elif Type = D then
  Base(Type,n)[1] + 2*convert([seq(Base(Type,n)[j],j=2..n-2)],`+`) + Base(Type,n)[n-1] + Base(Type,n)[n]
 elif Type = F and n = 4 then
  [1,1,0,0]
 elif Type = G and n = 2 then
  [-1, -1, 2]
 else
  printf("Error: root system must be of Type A, B, C, D, F, G")

 fi;
end proc:

FundomVertexCoefficient:=proc(Type,n) # fundamental domain is convex hull of 0 and fundamental weights, divided by some scalars. this is the list of scalar divisors (!!!)
local i;
 [op(convert(Transpose(<op(HighestRoot(Type,n))>).WeightMatrix(Type,n),list)),1]
end proc:

ROrbit:=proc(Type,n,omega) option remember; # list of elements in an orbit under orthogonal Weyl group action, not counting multiplicities
local i, mat;
 [op({op(map(mat -> convert(mat.<omega>,list),RWeylGroup(Type,n)))})];
end proc:

ZOrbit:=proc(Type,n,alpha) option remember; # list of elements in an orbit under integer Weyl group action, not counting multiplicities
local i;
 [op({op(map(mat -> convert(mat.<alpha>,list),ZWeylGroup(Type,n)))})];
end proc:

esp:=proc(L,r) # r-th elementary symmetric polynomials, evaluated in list L
 local f, i;
 f:=product((x_-L[i]),i=1..nops(L));
 simplify(coeff(f,x_,nops(L)-r))*(-1)^r;
end proc:

GeneralizedCosine:=proc(Type,n,u::list) # generalized cosine evaluated in u
local i, j;
 if   Type = A then
  [seq( simplify(1/binomial(n+1,j)*esp([seq(exp(-2*Pi*I*u[i]),i=1..n+1)],j)) , j=1..n)]
 elif Type = B then
  [seq( simplify(1/binomial(n,j)*esp([seq(cos(2*Pi*u[i]),i=1..n)],j)) , j=1..n-1),simplify(esp([seq(cos(Pi*u[i]),i=1..n)],n))]
 elif Type = C then
  [seq( simplify(1/binomial(n,j)*esp([seq(cos(2*Pi*u[i]),i=1..n)],j)) , j=1..n)]
 elif Type = D then
  [seq( simplify(1/binomial(n,j)*esp([seq(cos(2*Pi*u[i]),i=1..n)],j)) , j=1..n-2),simplify(esp([seq(cos(Pi*u[i]),i=1..n)],n)-(-I)^n*esp([seq(sin(Pi*u[i]),i=1..n)],n)),simplify(esp([seq(cos(Pi*u[i]),i=1..n)],n)+(-I)^n*esp([seq(sin(Pi*u[i]),i=1..n)],n))]
 elif Type = G and n = 2 then
  [cos(2*Pi*(u[1] - u[2]))/3 + cos(2*Pi*(u[1] - u[3]))/3 + cos(2*Pi*(u[2] - u[3]))/3, cos(2*Pi*(u[1] - 2*u[2] + u[3]))/3 + cos(2*Pi*(u[1] + u[2] - 2*u[3]))/3 + cos((4*u[1] - 2*u[2] - 2*u[3])*Pi)/3]
 else
  printf("Error: root system must be of Type A, B, C, D")
 fi;
end proc:

RGeneralizedCosine:=proc(Type,n,u::list) # real generalized cosine evaluated in u
local i, j;
 if Type = A then
  [seq( simplify(GeneralizedCosine(Type,n,u)[j]+GeneralizedCosine(Type,n,u)[n+1-j])/2 , j=1..floor(n/2)) , seq(simplify(GeneralizedCosine(Type,n,u)[j]),j=ceil((n+1)/2)..floor((n+1)/2)) , seq( simplify(GeneralizedCosine(Type,n,u)[n+1-j]-GeneralizedCosine(Type,n,u)[j])/(2*I) , j=ceil((n+2)/2)..n)]
 elif Type = B or Type = C or (Type = G and n = 3) then
  GeneralizedCosine(Type,n,u)
 elif Type = D then
  if is(n::even) then GeneralizedCosine(Type,n,u)
  else
   [seq(GeneralizedCosine(Type,n,u)[j],j=1..n-2),simplify((GeneralizedCosine(Type,n,u)[n]-GeneralizedCosine(Type,n,u)[n-1])/(2*I)),simplify((GeneralizedCosine(Type,n,u)[n]+GeneralizedCosine(Type,n,u)[n-1])/2)]
  fi;
 else
  printf("Error: root system must be of Type A, B, C, D")
 fi;
end proc:

VertexFundom:=proc(Type,n) # list of vertices of the fundamental domain of orthogonal Weyl group
local i;
 if Type = A then
  [seq(FWeight(Type,n)[i]/FundomVertexCoefficient(Type,n)[i],i=1..n),[seq(0,i=1..n+1)]]
 elif Type = B or Type = C or Type = D or Type = G then
  [seq(FWeight(Type,n)[i]/FundomVertexCoefficient(Type,n)[i],i=1..n),[seq(0,i=1..n)]]
 fi;
end proc:

VertexTOrbitSpace:=proc(Type,n) # list of vertices of the T-orbit space
local i;
 [seq(RGeneralizedCosine(Type,n,VertexFundom(Type,n)[i]),i=1..n+1)];
end proc:

Pull := proc(Type,n,alpha) option remember; # returns the dominant weight, containing alpha as an integer vector in its orbit
local orb, i, u;
 if `and`(seq(is(alpha[i] >=0), i=1..n)) then
  alpha
 else
  orb := ZOrbit(Type,n,alpha);
  orb := select( u -> `and`( seq(is(u[i] >=0), i=1..n) ), orb);
  op(1, orb);
 end if;
end proc:

TMultiply:=proc(Type,alpha,beta) option remember; # recurrence formula for Chebyshev polynomials associated to integer vectors alpha, beta. returns indeterminates y[...]
 local n, Tp, orb, l;
 global y;
 y:='y';
 n:=nops(alpha);
 orb:=ZOrbit(Type,n,beta);
 1/nops(orb)*convert(map(l->y[op(Pull(Type,n,alpha+l))],orb),`+`);
end proc:

MonomialMultiply:=proc(alpha,beta) # recurrence formula for standard monomial basis (just for comparisons)
 global y;
 y:='y';
 y[op(alpha+beta)];
end proc:

MonomialExponent:=proc(n,degbound)
 local LL, L, i;
 [seq(op({op(map(LL->op(permute(LL)),select(L->nops(L)=n,partition(i)))),op(map(LL->op(permute(LL-[seq(1,i=1..n)])),select(L->nops(L)=n,partition(i+n))))}),i=0..degbound)];
end proc:

MonomialExponent2:=proc(n,degbound)
 local LL, L, i;
 [seq(op({op(map(LL->op(permute(LL)),select(L->nops(L)=n,partition(i)))),op(map(LL->op(permute(LL-[seq(1,i=1..n)])),select(L->nops(L)=n,partition(i+n))))}),i=0..2*degbound)];
end proc:

ChebyshevDegExp:=proc(Type,n,l,bound) option remember;
 local i, L;
 select( L-> l*FundomVertexCoefficient(Type,n)[1] = convert([seq(L[i],i=1..n)],`+`) and convert([seq(FundomVertexCoefficient(Type,n)[1..n][i]*L[i],i=1..n)],`+`) <= bound,MonomialExponent(n,bound));
end proc:

ChebyshevLevel:=proc(Type,n,l) option remember;
 local L, i;
 if Type=F and n=4 then
  select( L-> l = convert([seq(FundomVertexCoefficient(Type,n)[1..n][i]*L[i],i=1..n)],`+`),MonomialExponent(n,l))
 else
  select( L-> l*FundomVertexCoefficient(Type,n)[1] = convert([seq(FundomVertexCoefficient(Type,n)[1..n][i]*L[i],i=1..n)],`+`),MonomialExponent(n,l))
 fi;
end proc:

TruncatedTMomentMatrix:=proc(Type,n,d) option remember; # moment matrix in Chebyshev basis up to degree degbound
 local i, j, L, l;
 L:=[seq(op(ChebyshevLevel(Type,n,l)),l=0..d)];
 Matrix(nops(L),(i,j)->TMultiply(Type,L[i],L[j]));
end proc:

TruncatedMonomialMomentMatrix:=proc(n,degbound) # moment matrix in standard monomial basis up to degree degbound
 local i, j;
 Matrix(binomial(n+degbound,n),(i,j)->MonomialMultiply(MonomialExponent2(n,degbound)[i],MonomialExponent2(n,degbound)[j]));
end proc:

TPolyRecurrence:=proc(Type,n,alpha) option remember; # input list with nonnegative integer entries, at least one nonzero
local i, j, beta, orb, K, eq;
 j:=select(i->is(alpha[i]>0),[seq(i,i=1..n)])[1];
 beta:=convert(Column(IdentityMatrix(n),j),list);
 orb:=ZOrbit(Type,n,beta);
 K:=map(l->Pull(Type,n,alpha - beta + l),orb);
 eq:=convert([seq(T[op(K[i])],i=1..nops(K))],`+`);
solve(nops(orb)*T[op(beta)]*T[op(alpha-beta)]=eq,T[op(alpha)]);
end proc:

#if a Groebner basis H is given by the 'Shape lemma' in permuted Variables z then the solutions can be obtained by this procedure (assuming ideal is zero dimensional)
SolutionSet:=proc(H::list,permuts) option remember;
 local Sol,Solutions, i, j, k;
 Sol[1]:=[solve(H[1])];
 Solutions[1]:=map(l->[l],[op({op(Sol[1])})]);
 for k from 2 to nops(H) do
  for i from 1 to nops(Solutions[k-1]) do
   Sol[k,i]:=[op({solve(subs([seq(z[permuts[j]]=Solutions[k-1][i][j],j=1..k-1)],H[k]))})];
   Solutions[k]:=[op({seq(seq([ op(Solutions[k-1][i]) , Sol[k,i][j] ],j=1..nops(Sol[k,i])),i=1..nops(Solutions[k-1]))})];
  od:
 od:
 Solutions[nops(H)];
end proc:

HermiteMatrix:=proc(Type,n) # polynomial matrix which characterizes the T-orbit space, careful: for Type A the matrix is complex
 local Y, f, k, i, j, CompMat;
 global z;
 z:='z';
 if Type = A then
  Y:=[1,seq(z[i],i=1..n),1]:
  for k from 1 to n+1 do
   f[k]:=(-1)^k*convert([seq(binomial(n+1,i)*binomial(n+1,k-i)*Y[i+1]*Y[n-k+i+2],i=0..k)],`+`);
  od;
  CompMat:=Matrix(n+1,(i,j)-> if (i = 2 and j = 1) then 1
                              elif ((i = j+1 and j <= n) or (i = j-1 and j <= n)) then 1/2
                              elif j <= n then 0
                              elif i = 1 then -f[n+1]/4
                              elif i = n then (1-f[2])/2
                              else -f[n+2-i]/2
                              fi);
  Matrix(n+1,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 elif Type = B then
  Y:=[seq(z[i],i=1..n)]:
  for k from 1 to n-1 do
   f[k]:=(-1)^(k+1)*2^k*binomial(n,k)*Y[k];
  od:
  f[n]:=(-1)^(n+1)*2^n*(2^n*Y[n]^2-convert([seq(binomial(n,i)*Y[i],i=1..n-1)],`+`)-1);
  CompMat:=Matrix(n,(i,j)-> if  (i = j+1 and j <= n-1) then 1
                            elif j <= n-1 then 0
                            else f[n-i+1]
                            fi):
  Matrix(n,(i,j)->expand(4*Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 elif Type = C then
  Y:=[seq(z[i],i=1..n)]:
  for k from 1 to n do
   f[k]:=(-1)^(k+1)*2^k*binomial(n,k)*Y[k];
  od:
  CompMat:=Matrix(n,(i,j)-> if  (i = j+1 and j <= n-1) then 1
                            elif j <= n-1 then 0
                            else f[n-i+1]
                            fi):
  Matrix(n,(i,j)->expand(4*Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 elif Type = D then
  Y:=[seq(z[i],i=1..n)]:
  for k from 1 to n-2 do
   f[k]:=(-1)^(k+1)*2^k*binomial(n,k)*Y[k];
  od:
  if is(n,even) then
   f[n-1]:=(-1)^(n)*2^(n-1)*( 2^(n-1)*Y[n]*Y[n-1]       -convert([seq(binomial(n,2*i-1)*Y[2*i-1],i=1..(n-2)/2)],`+`)   );
   f[n]  :=(-1)^(n+1)*2^n  *( 2^(n-2)*(Y[n]^2+Y[n-1]^2) -convert([seq(binomial(n,2*i)  *Y[2*i]  ,i=1..(n-2)/2)],`+`) -1);
  else
   f[n-1]:=(-1)^(n)*2^(n-1)*( 2^(n-1)*Y[n]*Y[n-1]       -convert([seq(binomial(n,2*i)  *Y[2*i]  ,i=1..(n-3)/2)],`+`) -1);
   f[n]  :=(-1)^(n+1)*2^n  *( 2^(n-2)*(Y[n]^2+Y[n-1]^2) -convert([seq(binomial(n,2*i+1)*Y[2*i+1],i=1..(n-3)/2)],`+`)   );
  fi:
  CompMat:=Matrix(n,(i,j)-> if  (i = j+1 and j <= n-1) then 1
                            elif j <= n-1 then 0
                            else f[n-i+1]
                            fi):
  Matrix(n,(i,j)->expand(4*Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 else
  printf("Error: root system must be of Type A, B, C, D")
 fi;
end proc:

RHermiteMatrix:=proc(Type,n)
 local i, j, k, f, Y, CompMat;
 global z;
 z:='z';
 if Type=B or Type=C or Type=D then
  HermiteMatrix(Type,n)
 elif Type=A then 
  Y:=[1,seq(Y||i,i=1..n),1]:
  for k from 1 to n+1 do
   f[k]:=(-1)^k*convert([seq(binomial(n+1,i)*binomial(n+1,k-i)*Y[i+1]*Y[n-k+i+2],i=0..k)],`+`);
  od;
  CompMat:=Matrix(n+1,(i,j)-> if (i = 2 and j = 1) then 1
                              elif ((i = j+1 and j <= n) or (i = j-1 and j <= n)) then 1/2
                              elif j <= n then 0
                              elif i = 1 then -f[n+1]/4
                              elif i = n then (1-f[2])/2
                              else -f[n+2-i]/2
                              fi);
  CompMat:=simplify(subs([seq(Y||k=z[k]+I*z[n+1-k],k=1..floor(n/2)),seq(Y||(n+1-k)=z[k]-I*z[n+1-k],k=1..floor(n/2))  ],CompMat));
  if is((n+1)::odd) then CompMat:=CompMat else CompMat:=subs(Y||((n+1)/2)=z[(n+1)/2],CompMat) fi;
  Matrix(n+1,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 else
  printf("Error: root system must be of Type A, B, C, D")
 fi;
end proc:

InvariantRewrite:=proc(Type,n,invariant) option remember; # This proc will give an output regardless if the input is invariant or not. Input must be Lauren polynomial in x[i]
local W, TermsMatrixEntry, ExponentsMatrixEntry, SplitTermsMatrixEntry, PositiveTerms, OrbCard, i, j, k, l;
global y;
 y:='y';
 TermsMatrixEntry:=[op(expand(simplify(invariant)))];
 ExponentsMatrixEntry:=[seq([seq(degree(op(TermsMatrixEntry)[j],x[i]),i=1..n)],j=1..nops(TermsMatrixEntry))];
 SplitTermsMatrixEntry:=[seq([TermsMatrixEntry[j]*convert([seq(x[i]^(-ExponentsMatrixEntry[j][i]),i=1..n)],`*`),[seq(degree(op(TermsMatrixEntry)[j],x[i]),i=1..n)]],j=1..nops(TermsMatrixEntry))];
 PositiveTerms:=select(l->`and`(seq(is(l[2][i]>=0),i=1..n)),SplitTermsMatrixEntry);
 for i from 1 to nops(PositiveTerms) do
  OrbCard[i]:=nops(ZOrbit(Type,n,PositiveTerms[i,2]));
 od;
 convert([seq(PositiveTerms[i,1]*OrbCard[i]*y[op(PositiveTerms[i,2])],i=1..nops(PositiveTerms))],`+`);
end proc:

MonomialRewrite:=proc(n,invariant)
local TermsMatrixEntry, ExponentsMatrixEntry, SplitTermsMatrixEntry, i, j, k, l;
global y;
 y:='y';
 TermsMatrixEntry:=[op(expand(simplify(invariant)))];
 ExponentsMatrixEntry:=[seq([seq(degree(op(TermsMatrixEntry)[j],z[i]),i=1..n)],j=1..nops(TermsMatrixEntry))];
 SplitTermsMatrixEntry:=[seq([TermsMatrixEntry[j]*convert([seq(z[i]^(-ExponentsMatrixEntry[j][i]),i=1..n)],`*`),[seq(degree(op(TermsMatrixEntry)[j],z[i]),i=1..n)]],j=1..nops(TermsMatrixEntry))];
 convert([seq(SplitTermsMatrixEntry[i,1]*y[op(SplitTermsMatrixEntry[i,2])],i=1..nops(SplitTermsMatrixEntry))],`+`);
end proc:

THermiteEntries:=proc(Type,n,k) option remember;
local i, j;
global y;
 if Type = A then
  if is(k::odd) then
   n/2^k*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(y[k-2*j,seq(0,i=1..n-2)]+y[seq(0,i=1..n-2),k-2*j]),j=1..(k-1)/2)],`+`)-(y[k,seq(0,i=1..n-2)]+y[seq(0,i=1..n-2),k]) )
  else
   n/2^k*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(y[k-2*j,seq(0,i=1..n-2)]+y[seq(0,i=1..n-2),k-2*j]),j=1..k/2-1  )],`+`)-(y[k,seq(0,i=1..n-2)]+y[seq(0,i=1..n-2),k])
   +(4*binomial(k-2,k/2-1)-binomial(k,k/2))*y[0,seq(0,i=1..n-2)])
  fi;
 elif Type = B or Type = C or Type = D then
  if is(k::odd) then
   2*n*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*y[k-2*j,seq(0,i=1..n-1)],j=1..(k-1)/2)],`+`)-y[k,seq(0,i=1..n-1)])
  else
   2*n*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*y[k-2*j,seq(0,i=1..n-1)],j=1..k/2-1)],`+`)-y[k,seq(0,i=1..n-1)]+(-binomial(k,k/2)+4*binomial(k-2,k/2-1))/2*y[0,seq(0,i=1..n-1)])
  fi;
 elif Type = G then
  if is(k::odd) then
   6*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*y[k-2*j,0],j=1..(k-1)/2)],`+`)-y[k,0])
  else
   6*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*y[k-2*j,0],j=1..k/2-1  )],`+`)-y[k,0]+(-binomial(k,k/2)+4*binomial(k-2,k/2-1))/2*y[0,0])
  fi;
 else
  printf("Error: root system must be of Type A, B, C, D, G")
 fi;
end proc:

THermiteMatrix:=proc(Type,n)
local i, j;
global y;
 if Type = B or Type = C or Type = D then
  Matrix(n  ,(i,j)->THermiteEntries(Type,n,  i+j));
 elif Type = A then 
  Matrix(n+1,(i,j)->THermiteEntries(Type,n+1,i+j));
 elif Type = G then
  Matrix(3  ,(i,j)->THermiteEntries(Type,2  ,i+j));
 else
  printf("Error: root system must be of Type A, B, C, D, G")
 fi;
end proc:

RTHermiteEntries:=proc(Type,n,k)
 local i, j;
 global y;
 if Type = A then
  if is(k::odd) then
   2*n/2^k*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(y[k-2*j,seq(0,i=1..n-2)]),j=1..(k-1)/2)],`+`)-(y[k,seq(0,i=1..n-2)]))
  else
   2*n/2^k*(convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(y[k-2*j,seq(0,i=1..n-2)]),j=1..k/2-1)],`+`)-(y[k,seq(0,i=1..n-2)])+(-binomial(k,k/2)+4*binomial(k-2,k/2-1))/2*y[0,seq(0,i=1..n-2)])
  fi;
 elif Type = B or Type = C or Type = D then
  THermiteEntries(Type,n,k)
 else
  printf("Error: root system must be of Type A, B, C, D")
 fi;
end proc:

RTHermiteMatrix:=proc(Type,n)
 local i, j;
 global y;
 if Type = B or Type = C or Type = D then
  Matrix(n,(i,j)->RTHermiteEntries(Type,n,i+j));
 elif Type = A then 
  Matrix(n+1,(i,j)->RTHermiteEntries(Type,n+1,i+j));
 else
  printf("Error: root system must be of Type A, B, C, D")
 fi;
end proc:

MonomialHermiteMatrix:=proc(Type,n)
 local H, L, i, entry;
 global z, x;
 x:='x';
 z:='z';
 H:=HermiteMatrix(Type,n);
 map(entry->MonomialRewrite(n,entry),H)
end proc:

CoeffInMatrix:=proc(L,Matty) option remember; # for matrices Matty with linear (or affine) entries in L
 local d, k, TTT, TTTT, ttt, t, i, j;
 d:=RowDimension(Matty);
 for i from 1 to d do
  for j from 1 to d do
   TTT[i,j]:=[coeffs(Matty[i,j],indets(Matty[i,j]),'t')]:
   TTTT[i,j]:=select(ttt->is(ttt[2]=L),[seq([TTT[i,j][k],[t][k]],k=1..nops(TTT[i,j]))]):
  od;
 od;
 Matrix(d,(i,j)->if nops(TTTT[i,j])=1 then TTTT[i,j][1][1] else 0 fi)
end proc:

MonomialLocalizedPMI:=proc(Type,n,d) option remember;
 local i, j, k, l, ll, H, Y, YH;
 global y;
 y:='y';
 YH:=MonomialExponent2(n,2*n);
 Y:=MonomialExponent2(n,d);
 H:=MonomialHermiteMatrix(Type,n);
 H:=select(ll->not(is(Rank(ll[1])=0)),map(l->[CoeffInMatrix(y[op(l)],H),l],YH));
 <seq(Transpose(<seq(convert(map(k->k[1]*y[op(Pull(Type,n,k[2]+Y[i]+Y[j]))],H),`+`),i=1..binomial(n+d,n))>),j=1..binomial(n+d,n))>;
end proc:

TLocalizedPMI:=proc(Type,n,d) option remember; # works for Bn, Cn, D2n
 local i, j, k, l, ll, Y, N, Orbs, H, h, yy;
 global y;
 y:='y';
 Y:=[seq(op(ChebyshevLevel(Type,n,l)),l=0..d)];
 N:=nops(Y);
 Orbs:=[seq(ZOrbit(Type,n,Y[i]),i=1..N)];
 #Y:=MonomialExponent(n,d)
 #Y:=[seq(op(select(yy->Transpose(WeightMatrix(Type,n).<yy>).<HighestRoot(Type,n)> = FundomVertexCoefficient(Type,n)[1]*k,Y)),k=0..d)]
 if Type = B or Type = C or Type = D then
  H:=[seq([Matrix(n,(i,j) -> if   (is(k-i-j,odd) or (k > i+j)) then 0  # following the formula for the matrix entries 
                             elif k = i+j then -1
                             elif k = 0 then 2*binomial(i+j-2,(i+j-2)/2) - 1/2*binomial(i+j,(i+j)/2)
                             else 4*binomial(i+j-2,(i+j-k)/2-1) - binomial(i+j,(i+j-k)/2)
                             fi ) , 
           [k , seq(0 , i = 2..n)]] ,
          k = 0..2*n)];
  <seq(Transpose(<seq((convert(map(h -> h[1]*(convert(map(ll->op(map(l->y[op(Pull(Type,n,h[2]+l+ll))],Orbs[i])),Orbs[j]),`+`)),
                                   H),`+`))/nops(Orbs[i])/nops(Orbs[j]),i=1..N)>),j=1..N)>;
 elif Type = A then
  H:=[seq([Matrix(n+1,(i,j) -> if   (is(k-i-j,odd) or (k > i+j)) then 0  # following the formula for the matrix entries 
                               elif k = i+j then -1/2^(i+j)
                               elif k = 0 then (4*binomial(i+j-2,(i+j-2)/2) - binomial(i+j,(i+j)/2))/2^(i+j+1)
                               else (4*binomial(i+j-2,(i+j-k)/2-1) - binomial(i+j,(i+j-k)/2))/2^(i+j)
                               fi ) , 
           [k , seq(0 , i = 2..n)] , [seq(0 , i = 1..n-1) , k] ] ,
          k = 0..2*n+2)];
  <seq(Transpose(<seq((convert(map(h -> h[1]*(   convert(map(ll->op(map(l->y[op(Pull(Type,n,h[2]+l+ll))],Orbs[i])),Orbs[j]),`+`)
                                               + convert(map(ll->op(map(l->y[op(Pull(Type,n,h[3]+l+ll))],Orbs[i])),Orbs[j]),`+`)),
                                   H),`+`))/nops(Orbs[i])/nops(Orbs[j]),i=1..N)>),j=1..N)>;
 elif Type = G and n = 2 then
  H:=[seq([Matrix(3,(i,j) -> if   (is(k-i-j,odd) or (k > i+j)) then 0  # following the formula for the matrix entries 
                             elif k = i+j then -1
                             elif k = 0 then 2*binomial(i+j-2,(i+j-2)/2) - 1/2*binomial(i+j,(i+j)/2)
                             else 4*binomial(i+j-2,(i+j-k)/2-1) - binomial(i+j,(i+j-k)/2)
                             fi ) , [k , 0]] , k = 0..6)];
  <seq(Transpose(<seq((convert(map(h -> h[1]*(convert(map(ll->op(map(l->y[op(Pull(Type,n,h[2]+l+ll))],Orbs[i])),Orbs[j]),`+`)),
                                   H),`+`))/nops(Orbs[i])/nops(Orbs[j]),i=1..N)>),j=1..N)>;
 else
  printf("Error: root system must be of Type A, B, C, D, G")
 fi;
end proc:

ChebyshevSDPdata:=proc(Type,n,d,name) option remember; #This is for the SDP solver, d must be at least n

 local Y, N, MY, MHY, M, i, k, Constraints;

 #Y:=MonomialExponent2(n,d);
 #Y:=select(yy->Transpose(WeightMatrix(Type,n).<yy>).<HighestRoot(Type,n)> <= FundomVertexCoefficient(Type,n)[1]*2*d,Y);
 Y:=[seq(op(ChebyshevLevel(Type,n,i)),i=0..2*d)];
 N:=nops(Y);
 MY:=TruncatedTMomentMatrix(Type,n,d);
 if Type = B or Type = C or Type = D then
  MHY:=TLocalizedPMI(Type,n,d-n);
 elif Type = A or Type = G then
  MHY:=TLocalizedPMI(Type,n,d-n-1);
 fi;
 M:=<<MY|Matrix(RowDimension(MY),RowDimension(MHY))>,<Matrix(RowDimension(MHY),RowDimension(MY))|MHY>>;

 Constraints := [ seq(CoeffInMatrix(y[op(Y[i])],M),i=1..N) ] ;

 Export(name,[Constraints]);
end proc:

TArchimedeanPMI:=proc(Type,n,d) option remember; # works for Bn, Cn, D2n
 local i, j, l, ll, k, Y, N, Orbs, ExtraOrbs, H, h, yy;
 global y;
 y:='y';
 Y:=[seq(op(ChebyshevLevel(Type,n,l)),l=0..d)];
 N:=nops(Y);
 Orbs:=[seq(ZOrbit(Type,n,Y[i]),i=1..N)];
 ExtraOrbs:=[seq(ZOrbit(Type,n,convert(Column(IdentityMatrix(n),k),list)),k=1..n)];
 if Type = B or Type = C or Type = D then
  <seq(
       Transpose(
                 <seq(
                      (n-(convert(
                                  [seq(
                                       (convert(
                                                map(lll->op(map(ll->op(map(l->
                                                                           y[op(Pull(Type,n,convert(Column(IdentityMatrix(n),k),list)+l+ll+lll))]
                                                                           ,Orbs[i])),Orbs[j])),ExtraOrbs[k])
                                                ,`+`))/nops(Orbs[i])/nops(Orbs[j])/nops(ExtraOrbs[k])
                                       ,k=1..n)]
                                  ,`+`)))
                      ,i=1..N)>
                 )
       ,j=1..N)>;
 else
  printf("Error: root system must be of Type B, C, D")
 fi;
end proc:

ChebyshevArchimedeanSDP:=proc(Type,n,d,name) option remember; #This is for the SDP solver, d must be at least n

 local dH, dP, Y, N, MY, MHY, MPY, nY, nHY, nPY, M, i, k, Constraints;
 dP:=max(FundomVertexCoefficient(Type,n))/FundomVertexCoefficient(Type,n)[1];
 dH:=n;
 Y:=[seq(op(ChebyshevLevel(Type,n,i)),i=0..2*d)];
 N:=nops(Y);
 MY:=TruncatedTMomentMatrix(Type,n,d);
 if Type=B or Type=C or Type=D then
  MHY:=TLocalizedPMI(Type,n,d-dH);
  MPY:=TArchimedeanPMI(Type,n,d-dP);
 else
  printf("Error: root system must be of Type B, C, D")
 fi;
 nY :=RowDimension(MY);
 nHY:=RowDimension(MHY);
 nPY:=RowDimension(MPY);
 M:=<<MY|Matrix(nY,nHY)|Matrix(nY,nPY)>,<Matrix(nHY,nY)|MHY|Matrix(nHY,nPY)>,<Matrix(nPY,nY)|Matrix(nPY,nHY)|MPY>>;

 Constraints := [ seq(CoeffInMatrix(y[op(Y[i])],M),i=1..N) ] ;

 Export(name,[Constraints]);
end proc:

end module: #GeneralizedChebyshevNULL;
NULL;
