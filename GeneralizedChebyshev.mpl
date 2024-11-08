
GeneralizedChebyshev := module()
description "A collection of procedures for generalized Chebyshev Polynomials";
option package;

with(LinearAlgebra):

export Base, PositiveRoots, coroot, WeightMatrix, FWeight, SteinbergWeight, WeylGroupOrder, RWeylGroupGen, WeylLength, ZWeylGroupGen, VertexFundomCoefficient, VertexFundom, VertexTOrbitSpace, VertexRTOrbitSpace, FundamentalInvariant, OrbitPolynomial, AntiOrbitPolynomial, WeylDenominator, CharacterPolynomial, HighestRoot, WeightList, ChebyshevLevel, ROrbit, ZOrbit, ZOrbitCardinality, GeneralizedCosine, RGeneralizedCosine, TMultiply, TPoly, TPolyFat, TPolyRecurrence, SubsXtoY, SubsYtoX, HermiteMatrix, RHermiteMatrix, InvariantRewrite, ChebyshevInvariantRewrite, THermiteMatrix, RTHermiteMatrix, CoefficientListPoly, CoefficientListLaurentPoly, DegreePoly, DegreeLaurentPoly, DegreeWeightSet, RPull, Pull, TMomentMatrix, TLocalizedMomentMatrix, SDPMatrices, SDPCoefficients, SDPMinMaxCoefficients, TArchimedeanPMI, ChebyshevArchimedeanSDP, BigRepGenMultiplicative, IrredRepGenMultiplicative, IrredRepDimMultiplicative, CharTableMultiplicative, IsotypicDecompositionMultiplicitiesMultiplicative, IsotypicDecompositionBasisMultiplicative, BigRepGenLinear, IrredRepGenLinear, IrredRepDimLinear, CharTableLinear, IsotypicDecompositionMultiplicitiesLinear, IsotypicDecompositionBasisLinear, BigRepGenDiagonal, IrredRepGenDiagonal, IrredRepDimDiagonal, CharTableDiagonal, IsotypicDecompositionMultiplicitiesDiagonal, IsotypicDecompositionBasisDiagonal, GradedDecompositionAdditive, GradedDecompositionMultiplicative, AdditiveToMultiplicativeCoinvariantBasis;

local Reflection, RWeylGroup, ZWeylGroup, esp, MonomialMultiply, ChebyshevDegExp, TruncatedMonomialMomentMatrix, PrimalConstraintMatrix, DualConstraintMatrix, MonomialExponent, SolutionSet, MonomialExponent2, MonomialRewrite, MonomialHermiteMatrix, MonomialLocalizedPMI, CoeffInMatrix, ProcesiSchwarzMatrix, THermiteEntries, RTHermiteEntriesOld, RTHermiteEntries, InvariantDegrees, ZeroArrangement, EntryNameVecMultiplicative, GroupStructureMultiplicative, IrredRepMultiplicative, EntryNameVecLinear, GroupStructureLinear, IrredRepLinear, EntryNameVecDiagonal, GroupStructureDiagonal, IrredRepDiagonal;




########
#BASICS#
########

Base:=proc(Type,n) # base of a root system
local i, j;
 if   Type = A then
  [seq([seq(`if`(j=i,1,`if`(j=i+1,-1,0)),j=1..n+1)],i=1..n)]
 elif Type = B then
  [seq([seq(`if`(j=i,1,`if`(j=i+1,-1,0)),j=1..n)],i=1..n)]
 elif Type = C then
  [seq([seq(`if`(j=i,1,`if`(j=i+1,-1,0)),j=1..n)],i=1..n-1),[seq(0,i=1..n-1),2]]
 elif Type = D then
  [seq([seq(`if`(j=i,1,`if`(j=i+1,-1,0)),j=1..n)],i=1..n-1),[seq(`if`(j=n,1,`if`(j=n-1,1,0)),j=1..n)]]
 elif Type = E and 6 <= n and n <= 8 then
  [[1,-1,-1,-1,-1,-1,-1,1]/2,[1,1,seq(0,j=3..8)],seq([seq(`if`(j=i-1,1,`if`(j=i-2,-1,0)),j=1..8)],i=3..n)]
 elif Type = F and n = 4 then
  [[0,1,-1,0],[0,0,1,-1],[0,0,0,1],[1,-1,-1,-1]/2]
 elif Type = G and n = 2 then
  [[1,-1,0],[-2,1,1]]
 else
  printf("Error: root system must be of simple Lie type")
 fi;
end proc:

PositiveRoots:=proc(type,n)
 option remember; 
 local i,j,k,rho;
 rho:=Base(type,n);
 if type = A then
  [seq(seq([seq(if k=i then 1 elif k=j then -1 else 0 fi,k=1..n+1)],j=i+1..n+1),i=1..n  )]
 elif type = 'B' then
  [seq([seq(if k=i then 1 else 0 fi,k=1..n)],i=1..n),
   seq(seq([seq(if k=i then 1 elif k=j then -1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1),
   seq(seq([seq(if k=i then 1 elif k=j then  1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1)] 
 elif type = C then
  [seq([seq(if k=i then 2 else 0 fi,k=1..n)],i=1..n),
   seq(seq([seq(if k=i then 1 elif k=j then -1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1),
   seq(seq([seq(if k=i then 1 elif k=j then  1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1)] 
 elif type = D then
  [seq(seq([seq(if k=i then 1 elif k=j then -1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1),
   seq(seq([seq(if k=i then 1 elif k=j then  1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1)] 
 elif type = F and n = 4 then
  [seq([seq(if k=i then 1 else 0 fi,k=1..n)],i=1..n),
   seq(seq([seq(if k=i then 1 elif k=j then -1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1),
   seq(seq([seq(if k=i then 1 elif k=j then  1 else 0 fi,k=1..n  )],j=i+1..n  ),i=1..n-1),
   1/2*[1,1,1,1],1/2*[1,1,1,-1],1/2*[1,1,-1,1],1/2*[1,-1,1,1],1/2*[1,1,-1,-1],1/2*[1,-1,1,-1],1/2*[1,-1,-1,1],1/2*[1,-1,-1,-1]]
 elif type = G and n = 2 then
  [rho[1],rho[1]+rho[2],2*rho[1]+rho[2],3*rho[1]+rho[2],3*rho[1]+2*rho[2],rho[2]]
 fi;
end proc:


coroot:=proc(r::list) # coroot of the input
 local scalar, i;
 scalar:=convert([seq(r[i]^2,i=1..nops(r))],`+`);
 2/scalar*r;
end proc:

WeightMatrix:=proc(Type,n) # the matrix containing the fundamental weights as columns
 MatrixInverse(Matrix(map(v->coroot(v),Base(Type,n))))
end proc:

FWeight:=proc(Type,n) # the list of fundamental weights
local i;
 [seq(convert(Column(WeightMatrix(Type,n),i),list),i=1..n)]
end proc:

HighestRoot:=proc(Type,n)
local i, j;
 if   Type = A then
  FWeight(Type,n)[1]+FWeight(Type,n)[n]
 elif Type = B then
  Base(Type,n)[1] + 2*convert([seq(Base(Type,n)[j],j=2..n)],`+`)
 elif Type = C then
  2*FWeight(Type,n)[1]
 elif Type = D then
  Base(Type,n)[1] + 2*convert([seq(Base(Type,n)[j],j=2..n-2)],`+`) + Base(Type,n)[n-1] + Base(Type,n)[n]
 elif Type = E and n = 6 then
  FWeight(Type,n)[2]
 elif Type = E and n = 7 then
  FWeight(Type,n)[1]
 elif Type = E and n = 8 then
  FWeight(Type,n)[8]
 elif Type = F and n = 4 then
  FWeight(Type,n)[1]
 elif Type = G and n = 2 then
  FWeight(Type,n)[2]
 else
  printf("Error: root system must be of simple Lie type")
 fi;
end proc:

VertexFundomCoefficient:=proc(Type,n) # fundamental domain is convex hull of 0 and fundamental weights, divided by some scalars. this is the list of scalar divisors (!!!)
local i;
 [op(convert(Transpose(<op(HighestRoot(Type,n))>).WeightMatrix(Type,n),list)),1]
end proc:

InvariantDegrees:=proc(Type,n)
local i;
 if Type=A then
  return [seq(i,i=2..n+1)]
 elif Type=B or Type=C then
  return [seq(2*i,i=1..n)]
 elif Type=D then
  return [seq(2*i,i=1..n-1),n]
 elif Type=E and n=6 then
  return [2,5,6,8,9,12]
 elif Type=E and n=7 then
  return [2,6,8,10,12,14,18]
 elif Type=E and n=8 then
  return [2,8,12,14,18,20,24,30]
 elif Type=F and n=4 then
  return [2,6,8,12]
 elif Type=G and n=2 then
  return [2,6]
 fi;
end proc:

WeylGroupOrder:=proc(Type,n) # The Weyl group order is the product of the degrees
 convert(InvariantDegrees(Type,n),`*`)
end proc:

RWeylGroupGen:=proc(Type,n) option remember; # generators of the Weyl group as a real orthogonal matrix group
 local i, j, k, N, diag;
 if   Type = A then
  return [seq(Matrix([seq([seq(`if`(i=k,1,0),i=1..n+1)],k=1..j-1),[seq(`if`(i=j+1,1,0),i=1..n+1)],[seq(`if`(i=j,1,0),i=1..n+1)],seq([seq(`if`(i=k,1,0),i=1..n+1)],k=j+2..n+1)]),j=1..n)];
 elif Type = G and n = 2 then
  return [Matrix(3, 3, [[0, 1, 0], [1, 0, 0], [0, 0, 1]]), Matrix(3, 3, [[-1/3, 2/3, 2/3], [2/3, 2/3, -1/3], [2/3, -1/3, 2/3]])];
 elif Type = E and n = 6 then
  for i from 1 to n do
   N[i]:=Matrix([seq(`if`(j=i,Base(Type,n)[j],FWeight(Type,n)[j]),j=1..n),[seq(if j=6 then 1 elif j=7 then -1 else 0 fi,j=1..n+2)],[seq(if j=7 or j=8 then 1 else 0 fi,j=1..n+2)]]);
   diag[i]:=Matrix([seq(`if`(j=i,[seq(`if`(k=j,-1,0),k=1..n+2)],[seq(`if`(k=j,1,0),k=1..n+2)]),j=1..n+2)]);
  od:
  return [seq(Transpose(MatrixInverse(N[i]).diag[i].N[i]),i=1..n)]
 elif Type = E and n = 7 then
  for i from 1 to n do
   N[i]:=Matrix([seq(`if`(j=i,Base(Type,n)[j],FWeight(Type,n)[j]),j=1..n),[seq(if j=7 or j=8 then 1 else 0 fi,j=1..n+1)]]);
   diag[i]:=Matrix([seq(`if`(j=i,[seq(`if`(k=j,-1,0),k=1..n+1)],[seq(`if`(k=j,1,0),k=1..n+1)]),j=1..n+1)]);
  od:
  return [seq(Transpose(MatrixInverse(N[i]).diag[i].N[i]),i=1..n)]
 else
  for i from 1 to n do
   N[i]:=Matrix([seq(`if`(j=i,Base(Type,n)[j],FWeight(Type,n)[j]),j=1..n)]);
   diag[i]:=Matrix([seq(`if`(j=i,[seq(`if`(k=j,-1,0),k=1..n)],[seq(`if`(k=j,1,0),k=1..n)]),j=1..n)]);
  od:
  return [seq(Transpose(MatrixInverse(N[i]).diag[i].N[i]),i=1..n)]
 fi;
end proc:

RWeylGroup:=proc(Type,n) option remember; # the Weyl group as a real orthogonal matrix group
 local W;
 W:=GroupTheory[Group]({op(RWeylGroupGen(Type,n))});
 return [op(Elements(W))];
end proc:

ZWeylGroupGen:=proc(Type,n) option remember; # the Weyl group as an integer matrix group
 local mat;
 map(mat-> MatrixInverse(WeightMatrix(Type,n)).mat.WeightMatrix(Type,n),RWeylGroupGen(Type,n));
end proc:

ZWeylGroup:=proc(Type,n) option remember; # the Weyl group as an integer matrix group
 local W;
 W:=GroupTheory[Group]({op(ZWeylGroupGen(Type,n))});
 return [op(Elements(W))];
end proc:

WeylLength:=proc(type,n,s)
 option remember;
 local rho, rho2, L, PosRoots;
 PosRoots:=PositiveRoots(type,n);
 L:=map(rho->convert(-s.<rho>,list),PosRoots);
 L:=select(rho->`or`(op(map(rho2->is(rho=rho2),PosRoots))),L);
 return nops(L);
end proc:

ZeroArrangement:=proc(L)
 local LL, LLL, LLLL, n, nn, Maxi, Mini, Upper, Lower, l, k, i;
 if `and`(seq(is(L[i]=0),i=1..nops(L))) then
  return [nops(L)];
 elif `and`(seq(is(L[i]>0),i=1..nops(L))) then
  return [0];
 else
  LL:=convert(ArrayTools[SearchArray](Array(L)),list);
  Mini:=min(LL);
  Maxi:=max(LL);
  LL:=[seq([i,LL[i]],i=1..nops(LL))];
  LLL:=[seq(LL[i],i=2..nops(LL))];
  LLLL:=[seq(LL[i],i=1..nops(LL)-1)];
  Upper:=map(k->k[2],select(l->-LL[l[1]-1][2]+l[2]>=2,LLL));
  Lower:=map(k->k[2],select(l->LL[l[1]+1][2]-l[2]>=2,LLLL));
  return select(l->is(l>0),[Mini-1,seq(Upper[i]-Lower[i]-1,i=1..nops(Upper)),nops(L)-Maxi]);
 fi;
end proc:

ZOrbitCardinality:=proc(Type,beta) option remember;
local W, alpha, n, k, l, i, L, m;

 if `and`(op(map(l->is(l=0),beta))) then
  return 1;
 fi;

 n:=nops(beta);
 alpha:=Pull(Type,beta);
 alpha:=map(l->if l>0 then 1 else 0 fi,alpha);
 W:=WeylGroupOrder(Type,n);
 
 if Type=A then
  k:=convert(map(l->factorial(l+1),ZeroArrangement(alpha)),`*`);
  return W/k;

 elif Type=D and n>=4 then
  if alpha[n]>0 then
   k:=convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=1..n-1)])),`*`);
  elif alpha[n-1]>0 then
   k:=convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=1..n-2),alpha[n]])),`*`);
  else
   L:=select(l->l[2]>0,[seq([i,alpha[i]],i=1..n-2)]);
   m:=L[nops(L)][1];
   if m=n-2 then
    k:=4*convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=1..m-1)])),`*`);
   elif m=n-3 then
    k:=24*convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=1..m-1)])),`*`);
   else
    k:=WeylGroupOrder(D,n-m+1)
     *convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=1..m-1)])),`*`);
   fi;
  fi;
  return W/k;

 elif Type=E and n>=6 and n<=8 then

  if alpha[2]>0 then
   k:=convert(map(l->factorial(l+1),ZeroArrangement([alpha[1],seq(alpha[i],i=3..n)])),`*`);

  elif alpha[3]>0 then

   k:=convert(map(l->factorial(l+1),ZeroArrangement([alpha[2],seq(alpha[i],i=4..n)])),`*`)
     *convert(map(l->factorial(l+1),ZeroArrangement([alpha[1]])),`*`);

  elif alpha[5]>0 then
   k:=convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=6..n)])),`*`)
     *convert(map(l->factorial(l+1),ZeroArrangement([alpha[1],alpha[3],alpha[4],alpha[2]])),`*`);

  elif alpha[4]>0 then
   k:=convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=5..n)])),`*`)
     *convert(map(l->factorial(l+1),ZeroArrangement([alpha[1],alpha[3]])),`*`)
     *convert(map(l->factorial(l+1),ZeroArrangement([alpha[3]])),`*`);

  elif alpha[1]>0 and alpha[6]>0 then # alpha[2]=alpha[3]=alpha[4]=alpha[5]=0, alpha[1]>0
   if n=6 then
    k:=WeylGroupOrder(D,4);
   else
    k:=WeylGroupOrder(D,4)
      *convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=7..n)])),`*`);
   fi;

  elif alpha[1]>0 and alpha[6]=0 then
   if n=6 then
    k:=WeylGroupOrder(D,5);
   elif n=7 then
    if alpha[7]>0 then
     k:=WeylGroupOrder(D,5);
    else
     k:=WeylGroupOrder(D,6);
    fi;
   else
    if alpha[7]>0 then
     k:=WeylGroupOrder(D,5)
       *convert(map(l->factorial(l+1),ZeroArrangement([alpha[8]])),`*`);
    elif alpha[8]>0 then
     k:=WeylGroupOrder(D,6);
    else
     k:=WeylGroupOrder(D,7);
    fi;
   fi;

  elif alpha[6]>0 then  #alpha[1]=alpha[2]=alpha[3]=alpha[4]=alpha[5]=0
   if n=6 then
    k:=WeylGroupOrder(D,5);
   else
    k:=WeylGroupOrder(D,5)
      *convert(map(l->factorial(l+1),ZeroArrangement([seq(alpha[i],i=7..n)])),`*`);
   fi;

  elif n=6 then
   k:=W

  elif n=7 then
   if alpha[7]>0 then
    k:=WeylGroupOrder(E,6);
   else
    k:=W;
   fi;

  elif n=8 then
   if alpha[7]>0 then
    k:=WeylGroupOrder(E,6)
      *convert(map(l->factorial(l+1),ZeroArrangement([alpha[8]])),`*`);
   elif alpha[8]>0 then 
    k:=WeylGroupOrder(E,7);
   else
    k:=W;
   fi;

  fi;
  return W/k;
 else
  L:=convert(WeightMatrix(Type,n).<alpha>,list);
  return nops(ROrbit(Type,n,L));
 fi;
end proc:

Reflection:=proc(rho,omega)  
 omega - ListTools[DotProduct](coroot(rho),omega)*rho;
end:

ROrbit:=proc(Type,n,omega) option remember;
 local Orb, i, stack_omega, next_omega, new_omega;
 Orb := {omega};
 stack_omega := stack[new](omega);
 while (not stack[empty](stack_omega)) do
  next_omega := stack[pop](stack_omega);
  for i from 1 to n do
   new_omega := Reflection(Base(Type,n)[i],next_omega);
   if (not (new_omega in Orb)) then
    Orb := Orb union {new_omega};
    stack[push](new_omega, stack_omega);
   end if;
  od;
 od;
 Orb := [op(simplify(Orb))];
end proc:

ZOrbit:=proc(Type,alpha) option remember; 
 local n, Orb, v, M;
 n:=nops(alpha);
 Orb:=ROrbit(Type,n,convert(WeightMatrix(Type,n).<alpha>,list));
 M:=MatrixInverse(WeightMatrix(Type,n));
 return map(v->convert(M.<v>,list),Orb);
end proc:

SteinbergWeight:=proc(type,n,s)
 option remember;
 local omega, i, Gens, L;
 omega:=FWeight(type,n);
 Gens:=RWeylGroupGen(type,n);
 L:=select(i->is(WeylLength(type,n,s.Gens[i])<WeylLength(type,n,s)),[seq(1..n)]);
 return convert(s.<convert(map(i->omega[i],L),`+`)>,list);
end proc:



SubsXtoY:=proc(Type,n,f) 
 global y;
 y:='y';
 local i, j;
 if Type = A then
  subs([seq(x[i]=convert([seq(y[j],j=1..i)],`*`),i=1..n  )                                                         ],f)
 elif Type = C then
  subs([seq(x[i]=convert([seq(y[j],j=1..i)],`*`),i=1..n  )                                                         ],f)
 elif Type = B then
  subs([seq(x[i]=convert([seq(y[j],j=1..i)],`*`),i=1..n-1),x[n  ]=sqrt(convert([seq(y[j],j=1..n  )],`*`)          )],f)
 elif Type = D then
  subs([seq(x[i]=convert([seq(y[j],j=1..i)],`*`),i=1..n-2),x[n  ]=sqrt(convert([seq(y[j],j=1..n  )],`*`)          )
                                                          ,x[n-1]=sqrt(convert([seq(y[j],j=1..n-1)],`*`)*y[n]^(-1))],f)
 elif Type = G then
  subs([x[1]=y[1],x[2]=y[1]^2*y[3]],f)
 else
  prinf("Error: root system must be of simple Lie type")
 fi;
end proc:

SubsYtoX:=proc(Type,n,f) 
 global x;
 x:='x';
 local i, j;
 if Type = A then
  subs([y[1]=x[1],seq(y[i]=x[i]*x[i-1]^(-1),i=2..n),y[n+1]=x[n]^(-1),convert([seq(y[j],j=1..n+1)],`*`)=1],f)
 elif Type = C then
  subs([y[1]=x[1],seq(y[i]=x[i]*x[i-1]^(-1),i=2..n-1),y[n]=x[n]*x[n-1]^(-1)],f)
 elif Type = B then
  subs([y[1]=x[1],seq(y[i]=x[i]*x[i-1]^(-1),i=2..n-1),y[n]=x[n]^2*x[n-1]^(-1)],f)
 elif Type = D then
  subs([y[1]=x[1],seq(y[i]=x[i]*x[i-1]^(-1),i=2..n-2),y[n-1]=x[n]*x[n-1]*x[n-2]^(-1),y[n]=x[n]*x[n-1]^(-1)],f)
 elif Type = G and n = 2 then
  subs([y[1]=x[1],y[2]=x[1]*x[2]^(-1),y[3]=x[1]^(-2)*x[2],y[1]*y[2]*y[3]=1],f)
 else
  prinf("Error: root system must be of simple Lie type A, B, C, D, G")
 fi;
end proc:

GradedDecompositionMultiplicative:=proc(f,n,var)
option remember;

 if f=0 then
  [0]
 else

 local ord, i, j, InvRel, k, Gen, AugIdeal, h, g, L;
 global x;

 ord:=lexdeg([seq(var[i],i=1..2*n)]);

 InvRel:=PolynomialIdeals[PolynomialIdeal](seq(1-var[i]*var[i+n],i=1..n));

 k:=1;
 g:=expand(subs([seq(seq(var[i]^(-j)=var[i+n]^j,i=1..n),j=1..6*n)],expand(f)));
 L:=[];

 while not(g=0) do
  if k=1 then
   Gen[k]:=PolynomialIdeals[PolynomialIdeal](seq(1-var[i],i=1..2*n))
  else
   Gen[k]:=PolynomialIdeals[Multiply](Gen[1],Gen[k-1])
  fi;
  AugIdeal[k]:=PolynomialIdeals[Add](Gen[k],InvRel);
  h:=Groebner[NormalForm](g,Groebner[Basis]([op(PolynomialIdeals[Generators](AugIdeal[k]))],ord),ord);
  g:=g-h;
  L:=[op(L),h];
  k:=k+1
 od;
 nops(L),subs([seq(var[i+n]=var[i]^(-1),i=1..n)],L);
 fi;
end proc:

GradedDecompositionAdditive:=proc(f,n,var)
option remember;

 if f=0 then
  [0]
 else

 local ord, i, InvRel, k, Gen, AugIdeal, h, g, L;
 global omega;

 ord:=lexdeg([seq(var[i],i=1..n)]);

 k:=1;
 g:=expand(f);
 L:=[];

 while not(g=0) do
  if k=1 then
   AugIdeal[k]:=PolynomialIdeals[PolynomialIdeal](seq(var[i],i=1..n))
  else
   AugIdeal[k]:=PolynomialIdeals[Multiply](AugIdeal[1],AugIdeal[k-1])
  fi;
  h:=Groebner[NormalForm](g,Groebner[Basis]([op(PolynomialIdeals[Generators](AugIdeal[k]))],ord),ord);
  g:=g-h;
  L:=[op(L),h];
  k:=k+1
 od;
 nops(L)-1,L;
 fi;
end proc:

AdditiveToMultiplicativeCoinvariantBasis:=proc(type,n,B)

local i,j,SubsStandardToFWeight,g,f,ff,mindeg,ord,G,N,NN,L,LL,HilbertIdeal,M;

SubsStandardToFWeight:=[seq(Y[j]=Transpose(MatrixInverse(WeightMatrix(Type,n)))[j].<seq(X[i],i=1..n)>                  ,j=1..RowDimension(WeightMatrix(Type,n)))];

g:=expand(subs(SubsStandardToFWeight,B));

f:=expand(subs([seq(X[i]=1-x[i]^(-1),i=1..n)],g));
ff:=map(_->GradedDecompositionMultiplicative(_,n,x)[2],f):
mindeg:=map(_->min(select(i->not(is(_[i]=0)),[seq(1..nops(_))]))-1,ff);
ff:=[seq(ff[i][mindeg[i]+1],i=1..nops(ff))]:
ff:=map(_->subs([seq(seq(x[i]^(-j)=x[i+n]^j,i=1..n),j=1..n^10)],_),ff):

HilbertIdeal:=PolynomialIdeals[PolynomialIdeal](op(subs([seq(seq(x[i]^(-j)=x[i+n]^j,i=1..n),j=1..6*n)],FundamentalInvariant(Type,n))),seq(1-x[i]*x[i+n],i=1..n)):
ord:=lexdeg([seq(x[i],i=1..2*n)]):
G:=Groebner[Basis](HilbertIdeal,ord):
N:=Groebner[NormalSet](G,ord)[1];
NN:=map(_->[seq(degree(_,x[i]),i=1..2*n)],N):

L:=map(_->Groebner[NormalForm](_,G,ord),ff);
LL:=[seq(map(_->[subs([seq(x[i]=1,i=1..2*n)],_),[seq(degree(_,x[i]),i=1..2*n)]],convert(L[j],list)),j=1..nops(L))]:

M:=Matrix(nops(NN),(i,j)->op(map(_->if nops(_)=0 then 0 else op(_) fi,[map(_->_[1],select(_->is(_[2]=NN[i]),LL[j]))])));

return M, Determinant(M);

end proc:


############
#INVARIANTS#
############

FundamentalInvariant:=proc(Type,n) option remember; # as Laurent polynomials
 local i, j, k, l, orb;
 global x;
 x:='x';
 if Type=A then
  [seq(expand(binomial(n+1,l)^(-1)*esp([x[1],seq(x[k]*x[k-1]^(-1),k=2..n),x[n]^(-1)],l)),l=1..n)]
 elif Type=C then
  [seq(expand(binomial(n,l)^(-1)*2^(-l)*esp([x[1]+x[1]^(-1),seq(x[k]*x[k-1]^(-1)+x[k]^(-1)*x[k-1],k=2..n)],l)),l=1..n)]
 elif Type=B then
  [seq(expand(binomial(n,l)^(-1)*2^(-l)*esp([x[1]+x[1]^(-1),seq(x[k]*x[k-1]^(-1)+x[k]^(-1)*x[k-1],k=2..n-1),x[n]^2*x[n-1]^(-1)+x[n]^(-2)*x[n-1]],l)),l=1..n-1),expand(2^(-n)*convert(map(orb->convert([seq(x[l]^(orb[l]),l=1..n)],`*`),ZOrbit(Type,[seq(0,k=1..n-1),1])),`+`))]
 elif Type=D then
  [seq(expand(binomial(n,l)^(-1)*2^(-l)*esp([x[1]+x[1]^(-1),seq(x[k]*x[k-1]^(-1)+x[k]^(-1)*x[k-1],k=2..n-2),x[n]*x[n-1]*x[n-2]^(-1)+x[n]^(-1)*x[n-1]^(-1)*x[n-2],x[n]*x[n-1]^(-1)+x[n]^(-1)*x[n-1]],l)),l=1..n-2),expand(2^(1-n)*convert(map(orb->convert([seq(x[l]^(orb[l]),l=1..n)],`*`),ZOrbit(Type,[seq(0,k=1..n-2),1,0])),`+`)),expand(2^(1-n)*convert(map(orb->convert([seq(x[l]^(orb[l]),l=1..n)],`*`),ZOrbit(Type,[seq(0,k=1..n-1),1])),`+`))]
 elif Type=F and n=4 then
  [x[2]/x[1]^2 + x[3]^2/(x[1]*x[2]) + 1/x[1] + x[4]^2/x[1] + x[3]^2/(x[1]*x[4]^2) + x[2]*x[4]^2/(x[1]*x[3]^2) + x[2]/(x[1]*x[4]^2) + x[2]/x[1] + x[2]^2/(x[1]*x[3]^2) + x[4]^2/x[2] + x[3]^2/(x[2]*x[4]^2) + x[3]^2/x[2] + x[2]/x[3]^2 + x[2]*x[4]^2/x[3]^2 + x[2]/x[4]^2 + x[1]*x[3]^2/x[2]^2 + x[1]/x[2] + x[1]*x[4]^2/x[2] + x[1]*x[3]^2/(x[2]*x[4]^2) + x[1]*x[4]^2/x[3]^2 + x[1]/x[4]^2 + x[1] + x[1]*x[2]/x[3]^2 + x[1]^2/x[2],
   x[1]*x[2]*x[4]^4/x[3]^4 + x[1]*x[2]/(x[3]^2*x[4]^2) + x[1]*x[2]*x[4]^2/x[3]^2 + x[1]*x[2]/x[4]^4 + x[1]*x[2]/x[4]^2 + x[1]*x[2]^2/x[3]^4 + x[1]*x[2]^2*x[4]^2/x[3]^4 + x[1]*x[2]^2/(x[3]^2*x[4]^2) + x[1]^2*x[3]^2/x[2]^3 + x[1]^2*x[3]^2*x[4]^2/x[2]^3 + x[1]^2*x[3]^4/(x[2]^3*x[4]^2) + x[1]^2*x[4]^2/(x[2]*x[3]^2) + x[1]^2*x[4]^4/(x[2]*x[3]^2) + x[1]^2/(x[2]*x[4]^2) + x[1]^2*x[4]^2/x[2] + x[1]^2*x[3]^2/(x[2]*x[4]^4) + x[1]^2*x[3]^2/(x[2]*x[4]^2) + x[1]^2*x[2]*x[4]^2/x[3]^4 + x[1]^2*x[2]/(x[3]^2*x[4]^2) + x[1]^2*x[2]/x[3]^2 + x[1]^3*x[3]^2/x[2]^3 + x[1]^3*x[4]^2/x[2]^2 + x[1]^3*x[3]^2/(x[2]^2*x[4]^2) + x[1]^3*x[4]^2/(x[2]*x[3]^2) + x[1]^3/(x[2]*x[4]^2) + x[1]^3/x[3]^2 + x[3]^4/(x[1]*x[2]^2*x[4]^2) + x[3]^4/(x[1]*x[2]^2) + x[4]^2/(x[1]*x[2]) + x[4]^4/(x[1]*x[2]) + x[3]^2/(x[1]*x[2]*x[4]^2) + x[3]^2*x[4]^2/(x[1]*x[2]) + x[3]^4/(x[1]*x[2]*x[4]^4) + x[3]^4/(x[1]*x[2]*x[4]^2) + x[4]^4/(x[1]*x[3]^2) + x[3]^2/(x[1]*x[4]^4) + x[3]^2/x[1] + x[2]/(x[1]*x[3]^2) + x[2]*x[4]^4/(x[1]*x[3]^2) + x[2]*x[3]^2/(x[1]*x[4]^4) + x[2]^2*x[4]^2/(x[1]*x[3]^4) + x[2]^2*x[4]^4/(x[1]*x[3]^4) + x[2]^2/(x[1]*x[3]^2*x[4]^2) + x[2]^2*x[4]^2/(x[1]*x[3]^2) + x[2]^2/(x[1]*x[4]^4) + x[2]^2/(x[1]*x[4]^2) + x[2]^3/(x[1]*x[3]^4) + x[2]^3*x[4]^2/(x[1]*x[3]^4) + x[2]^3/(x[1]*x[3]^2*x[4]^2) + x[1]*x[3]^2*x[4]^2/x[2]^3 + x[1]*x[3]^4/(x[2]^3*x[4]^2) + x[1]*x[3]^4/x[2]^3 + x[1]*x[4]^2/x[2]^2 + x[1]*x[4]^4/x[2]^2 + x[1]*x[3]^2/(x[2]^2*x[4]^2) + x[1]*x[3]^2*x[4]^2/x[2]^2 + x[1]*x[3]^4/(x[2]^2*x[4]^4) + x[1]*x[3]^4/(x[2]^2*x[4]^2) + x[1]*x[4]^4/(x[2]*x[3]^2) + x[1]*x[3]^2/(x[2]*x[4]^4) + x[1]*x[3]^2/x[2] + x[1]/x[3]^2 + x[1]*x[4]^4/x[3]^2 + x[1]*x[3]^2/x[4]^4 + x[1]*x[2]*x[4]^2/x[3]^4 + x[3]^2/x[1]^3 + x[2]*x[4]^2/x[1]^3 + x[2]*x[3]^2/(x[1]^3*x[4]^2) + x[2]^2*x[4]^2/(x[1]^3*x[3]^2) + x[2]^2/(x[1]^3*x[4]^2) + x[2]^3/(x[1]^3*x[3]^2) + x[3]^2/(x[1]^2*x[2]) + x[3]^2*x[4]^2/(x[1]^2*x[2]) + x[3]^4/(x[1]^2*x[2]*x[4]^2) + x[2]*x[4]^2/(x[1]^2*x[3]^2) + x[2]*x[4]^4/(x[1]^2*x[3]^2) + x[2]/(x[1]^2*x[4]^2) + x[2]*x[4]^2/x[1]^2 + x[2]*x[3]^2/(x[1]^2*x[4]^4) + x[2]*x[3]^2/(x[1]^2*x[4]^2) + x[2]^3*x[4]^2/(x[1]^2*x[3]^4) + x[2]^3/(x[1]^2*x[3]^2*x[4]^2) + x[2]^3/(x[1]^2*x[3]^2) + x[3]^2*x[4]^2/(x[1]*x[2]^2) + x[3]^4/x[2]^3 + x[4]^4/x[2] + x[3]^4/(x[2]*x[4]^4) + x[2]*x[4]^4/x[3]^4 + x[2]/x[4]^4 + x[2]^3/x[3]^4 + x[2] + x[2]^2/x[1]^3 + x[1]^3/x[2] + x[1]^3/x[2]^2 + x[2]/x[1]^3 + 1/x[2],
   x[1]*x[3]^2*x[4]/x[2]^2 + x[1]*x[3]^3/(x[2]^2*x[4]^2) + x[1]*x[3]^3/(x[2]^2*x[4]) + x[1]*x[4]^2/(x[2]*x[3]) + x[1]*x[4]^3/(x[2]*x[3]) + x[1]*x[3]/(x[2]*x[4]^2) + x[1]*x[3]*x[4]/x[2] + x[1]*x[3]^2/(x[2]*x[4]^3) + x[1]*x[3]^2/(x[2]*x[4]) + x[1]*x[4]/x[3]^2 + x[1]*x[4]^3/x[3]^2 + x[1]/(x[3]*x[4]) + x[1]*x[4]^2/x[3] + x[1]*x[3]/x[4]^3 + x[1]*x[3]/x[4]^2 + x[1]*x[2]*x[4]/x[3]^3 + x[1]*x[2]*x[4]^2/x[3]^3 + x[1]*x[2]/(x[3]^2*x[4]) + x[1]*x[2]*x[4]/x[3]^2 + x[1]*x[2]/(x[3]*x[4]^2) + x[1]*x[2]/(x[3]*x[4]) + x[1]^2*x[3]/x[2]^2 + x[1]^2*x[3]*x[4]/x[2]^2 + x[1]^2*x[3]^2/(x[2]^2*x[4]) + x[1]^2*x[4]/(x[2]*x[3]) + x[1]^2*x[4]^2/(x[2]*x[3]) + x[1]^2/(x[2]*x[4]) + x[1]^2*x[4]/x[2] + x[1]^2*x[3]/(x[2]*x[4]^2) + x[1]^2*x[3]/(x[2]*x[4]) + x[1]^2*x[4]/x[3]^2 + x[1]^2/(x[3]*x[4]) + x[1]^2/x[3] + x[2]*x[4]^2/(x[1]^2*x[3]) + x[2]/(x[1]^2*x[4]) + x[2]*x[4]/x[1]^2 + x[2]*x[3]/(x[1]^2*x[4]^2) + x[2]*x[3]/(x[1]^2*x[4]) + x[2]^2*x[4]/(x[1]^2*x[3]^2) + x[2]^2/(x[1]^2*x[3]*x[4]) + x[2]^2/(x[1]^2*x[3]) + x[3]*x[4]/(x[1]*x[2]) + x[3]*x[4]^2/(x[1]*x[2]) + x[3]^2/(x[1]*x[2]*x[4]) + x[3]^2*x[4]/(x[1]*x[2]) + x[3]^3/(x[1]*x[2]*x[4]^2) + x[3]^3/(x[1]*x[2]*x[4]) + x[4]^2/(x[1]*x[3]) + x[4]^3/(x[1]*x[3]) + x[3]/(x[1]*x[4]^2) + x[3]*x[4]/x[1] + x[3]^2/(x[1]*x[4]^3) + x[3]^2/(x[1]*x[4]) + x[2]*x[4]/(x[1]*x[3]^2) + x[2]*x[4]^3/(x[1]*x[3]^2) + x[2]/(x[1]*x[3]*x[4]) + x[2]*x[4]^2/(x[1]*x[3]) + x[2]*x[3]/(x[1]*x[4]^3) + x[2]*x[3]/(x[1]*x[4]^2) + x[2]^2*x[4]/(x[1]*x[3]^3) + x[2]^2*x[4]^2/(x[1]*x[3]^3) + x[2]^2/(x[1]*x[3]^2*x[4]) + x[2]^2*x[4]/(x[1]*x[3]^2) + x[2]^2/(x[1]*x[3]*x[4]^2) + x[2]^2/(x[1]*x[3]*x[4]) + x[1]*x[3]*x[4]/x[2]^2 + x[1]*x[3]*x[4]^2/x[2]^2 + x[1]*x[3]^2/(x[2]^2*x[4]) + x[3]/x[1]^2 + x[3]*x[4]/x[1]^2 + x[3]^2/(x[1]^2*x[4]) + x[2]*x[4]/(x[1]^2*x[3]) + x[3] + 1/x[3] + x[3]^2*x[4]/x[2]^2 + x[3]^3/(x[2]^2*x[4]) + x[3]^3/x[2]^2 + x[4]/x[2] + x[4]^3/x[2] + x[3]/(x[2]*x[4]) + x[3]*x[4]^2/x[2] + x[3]^3/(x[2]*x[4]^3) + x[3]^3/(x[2]*x[4]^2) + x[2]*x[4]^2/x[3]^3 + x[2]*x[4]^3/x[3]^3 + x[2]/(x[3]*x[4]^2) + x[2]*x[4]/x[3] + x[2]/x[4]^3 + x[2]/x[4] + x[2]^2/x[3]^3 + x[2]^2*x[4]/x[3]^3 + x[2]^2/(x[3]^2*x[4]) + x[4]^3/x[3]^2 + x[4]^3/x[3] + x[3]/x[4]^3 + x[3]^2/x[4]^3,
   x[4]/x[1] + x[3]/(x[1]*x[4]) + x[3]/x[1] + x[2]/(x[1]*x[3]) + x[2]*x[4]/(x[1]*x[3]) + x[2]/(x[1]*x[4]) + x[3]/x[2] + x[3]*x[4]/x[2] + x[3]^2/(x[2]*x[4]) + x[4]/x[3] + x[4]^2/x[3] + 1/x[4] + x[4] + x[3]/x[4]^2 + x[3]/x[4] + x[2]*x[4]/x[3]^2 + x[2]/(x[3]*x[4]) + x[2]/x[3] + x[1]*x[4]/x[2] + x[1]*x[3]/(x[2]*x[4]) + x[1]*x[3]/x[2] + x[1]/x[3] + x[1]*x[4]/x[3] + x[1]/x[4]]
 elif Type=E and n>=6 and n<=8 then
  orb:=[seq(ZOrbit(Type,[seq(`if`(i=j,1,0),i=1..n)]),j=1..n)];
  [seq(1/nops(orb[j])*convert(map(v->convert([seq(x[i]^v[i],i=1..n)],`*`),orb[j]),`+`),j=1..n)]
 elif Type=G and n=2 then
  [x[1]/6 + x[2]/(6*x[1]) + x[1]^2/(6*x[2]) + x[2]/(6*x[1]^2) + x[1]/(6*x[2]) + 1/(6*x[1]),x[2]/6 + x[2]^2/(6*x[1]^3) + x[1]^3/(6*x[2]) + x[1]^3/(6*x[2]^2) + x[2]/(6*x[1]^3) + 1/(6*x[2])]
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D, F, G")
 fi;
end proc:

OrbitPolynomial:=proc(Type,alpha)
 option remember;
 local n, orb, v, i;
 global x;

 n:=nops(alpha);
 orb:=ZOrbit(Type,alpha);
 1/nops(orb)*convert(map(v->convert([seq(x[i]^v[i],i=1..n)],`*`),orb),`+`);
end proc;

AntiOrbitPolynomial:=proc(Type,alpha)
 option remember;
 local n, G, i, j;
 global x;

 n:=nops(alpha);

 G:=GroupTheory[Group](ZWeylGroupGen(Type,n));
 G:=[op(GroupTheory[Elements](G))];

 1/nops(G)*convert([seq(Determinant(G[j])*convert([seq(x[i]^((G[j].<alpha>)[i]),i=1..n)],`*`),j=1..nops(G))],`+`);
end proc;

WeylDenominator:=proc(Type,n)
 option remember;
 local i, delta;
 delta:=[seq(1,i=1..n)];
 AntiOrbitPolynomial(Type,delta)
end proc;

CharacterPolynomial:=proc(Type,alpha)
 option remember;
 local n, G, i, delta;

 n:=nops(alpha);
 delta:=[seq(1,i=1..n)];

 expand(simplify(AntiOrbitPolynomial(Type,alpha+delta)/AntiOrbitPolynomial(Type,delta)))
end proc:

esp:=proc(L,r) # r-th elementary symmetric polynomials, evaluated in list L
 local f, i;
 f:=product((x_-L[i]),i=1..nops(L));
 simplify(coeff(f,x_,nops(L)-r))*(-1)^r;
end proc:

GeneralizedCosine:=proc(Type,n,u::list) # generalized cosine evaluated in u
 local i, j, orb, v;
 if   Type = A then
  [seq( simplify(1/binomial(n+1,j)*esp([seq(exp(-2*Pi*I*u[i]),i=1..n+1)],j)) , j=1..n)]
 elif Type = B then
  [seq( simplify(1/binomial(n,j)*esp([seq(cos(2*Pi*u[i]),i=1..n)],j)) , j=1..n-1),simplify(esp([seq(cos(Pi*u[i]),i=1..n)],n))]
 elif Type = C then
  [seq( simplify(1/binomial(n,j)*esp([seq(cos(2*Pi*u[i]),i=1..n)],j)) , j=1..n)]
 elif Type = D then
  [seq( simplify(1/binomial(n,j)*esp([seq(cos(2*Pi*u[i]),i=1..n)],j)) , j=1..n-2),simplify(esp([seq(cos(Pi*u[i]),i=1..n)],n)-(-I)^n*esp([seq(sin(Pi*u[i]),i=1..n)],n)),simplify(esp([seq(cos(Pi*u[i]),i=1..n)],n)+(-I)^n*esp([seq(sin(Pi*u[i]),i=1..n)],n))]
 elif Type = F and n = 4 then
  [cos(Pi*u[1])*cos(Pi*u[2])/6 + cos(Pi*u[1])*cos(Pi*u[3])/6 + cos(Pi*u[1])*cos(Pi*u[4])/6 + cos(Pi*u[2])*cos(Pi*u[3])/6 + cos(Pi*u[2])*cos(Pi*u[4])/6 + cos(Pi*u[3])*cos(Pi*u[4])/6,
   cos(Pi*u[1])*cos(Pi*u[4])*cos(Pi*u[2])^2/6 + cos(Pi*u[1])*cos(Pi*u[2])*cos(Pi*u[3])^2/6 + cos(Pi*u[1])*cos(Pi*u[2])*cos(Pi*u[4])^2/6 + cos(Pi*u[1])*cos(Pi*u[4])*cos(Pi*u[3])^2/6 + cos(Pi*u[1])*cos(Pi*u[3])*cos(Pi*u[4])^2/6 + cos(Pi*u[1])^2*cos(Pi*u[2])*cos(Pi*u[3])/6 + cos(Pi*u[1])^2*cos(Pi*u[2])*cos(Pi*u[4])/6 + cos(Pi*u[1])^2*cos(Pi*u[3])*cos(Pi*u[4])/6 + cos(Pi*u[2])*cos(Pi*u[4])*cos(Pi*u[3])^2/6 + cos(Pi*u[2])*cos(Pi*u[3])*cos(Pi*u[4])^2/6 + cos(Pi*u[2])^2*cos(Pi*u[3])*cos(Pi*u[4])/6 - cos(Pi*u[1])*cos(Pi*u[2])/6 - cos(Pi*u[1])*cos(Pi*u[3])/6 - cos(Pi*u[1])*cos(Pi*u[4])/6 - cos(Pi*u[2])*cos(Pi*u[3])/6 - cos(Pi*u[2])*cos(Pi*u[4])/6 - cos(Pi*u[3])*cos(Pi*u[4])/6 + cos(Pi*u[1])*cos(Pi*u[3])*cos(Pi*u[2])^2/6,
   cos((3*Pi*u[1])/2)*cos(Pi*u[2]/2)*cos(Pi*u[3]/2)*cos(Pi*u[4]/2)/6 + cos(Pi*u[1])*cos(Pi*u[2])*cos(Pi*u[3])/12 + cos(Pi*u[1])*cos(Pi*u[2])*cos(Pi*u[4])/12 + cos(Pi*u[1])*cos(Pi*u[3])*cos(Pi*u[4])/12 + cos(Pi*u[2])*cos(Pi*u[3])*cos(Pi*u[4])/12 + cos(Pi*u[1]/2)*cos((3*Pi*u[2])/2)*cos(Pi*u[3]/2)*cos(Pi*u[4]/2)/6 + cos(Pi*u[1]/2)*cos(Pi*u[2]/2)*cos((3*Pi*u[3])/2)*cos(Pi*u[4]/2)/6 + cos(Pi*u[1]/2)*cos(Pi*u[2]/2)*cos(Pi*u[3]/2)*cos((3*Pi*u[4])/2)/6,
   cos(Pi*u[1])/12 + cos(Pi*u[2])/12 + cos(Pi*u[3])/12 + cos(Pi*u[4])/12 + (2*cos(Pi*u[1]/2)*cos(Pi*u[2]/2)*cos(Pi*u[3]/2)*cos(Pi*u[4]/2))/3]
 elif Type = E then
  orb:=[seq(ROrbit(Type,n,FWeight(E,n)[i]),i=1..n)];
  [seq(simplify(1/nops(orb[i])*convert(map(v->exp(-2*Pi*I*(<v>.<u>)),orb[i]),`+`)),i=1..n)]
 elif Type = G and n = 2 then
  [cos(2*Pi*(u[1] - u[2]))/3 + cos(2*Pi*(u[1] - u[3]))/3 + cos(2*Pi*(u[2] - u[3]))/3, cos(2*Pi*(u[1] - 2*u[2] + u[3]))/3 + cos(2*Pi*(u[1] + u[2] - 2*u[3]))/3 + cos((4*u[1] - 2*u[2] - 2*u[3])*Pi)/3]
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D, E, F, G")
 fi;
end proc:

RGeneralizedCosine:=proc(Type,n,u::list) # real generalized cosine evaluated in u
 local i, j, GenCos;
 GenCos:=GeneralizedCosine(Type,n,u);
 if Type = A then
  return [seq( simplify(GenCos[j]+GenCos[n+1-j])/2 , j=1..floor(n/2)) , seq(simplify(GenCos[j]),j=ceil((n+1)/2)..floor((n+1)/2)) , seq( simplify(GenCos[n+1-j]-GenCos[j])/(2*I) , j=ceil((n+2)/2)..n)]
 elif Type = D and is(n::odd) then
  return [seq(GenCos[j],j=1..n-2),simplify((GenCos[n]-GenCos[n-1])/(2*I)),simplify((GenCos[n]+GenCos[n-1])/2)]
 elif Type = E and n = 6 then
  return [(GenCos[1]+GenCos[6])/2,GenCos[2],(GenCos[3]+GenCos[5])/2,GenCos[4],(GenCos[3]-GenCos[5])/2/I,(GenCos[1]-GenCos[6])/2/I]
 else
  return GenCos;
 fi;
end proc:

VertexFundom:=proc(Type,n) # list of vertices of the fundamental domain of orthogonal Weyl group
 local i, L, f;
 L:=VertexFundomCoefficient(Type,n);
 f:=FWeight(Type,n);
 if Type = A or (Type = G and n = 2) then
  [seq(f[i]/L[i],i=1..n),[seq(0,i=1..n+1)]]
 elif Type = B or Type = C or Type = D or (Type = F and n = 4) then
  [seq(f[i]/L[i],i=1..n),[seq(0,i=1..n)]]
 elif Type = E and (n=6 or n=7 or n=8) then 
  [seq(f[i]/L[i],i=1..n),[seq(0,i=1..8)]]
 fi;
end proc:

RPull:=proc(Type,n,omega) option remember;
 local M, mu, L, i, v;
 M:=MatrixInverse(WeightMatrix(Type,n));
 mu:=omega;
 L:=map(v->sign(v),M.<mu>);
 while `or`(seq(is(L[i]=-1),i=1..n)) do
  for i from 1 to n do
   if L[i]=-1 then
    mu:=Reflection(Base(Type,n)[i],mu)
   fi;
  od;
  L:=map(v->sign(v),M.<mu>);
 od;
 mu;
end proc:

Pull := proc(Type,alpha) option remember;
 local n, M, mu;
 n:=nops(alpha);
 M:=WeightMatrix(Type,n);
 mu:=convert(M.<alpha>,list);
 convert(MatrixInverse(M).<RPull(Type,n,mu)>,list);
end proc:

###########
#CHEBYSHEV#
###########

TMultiply:=proc(Type,alpha,beta) option remember; # recurrence formula for Chebyshev polynomials associated to integer vectors alpha, beta. returns indeterminates y[...]
 local n, Tp, orb, l;
 global y;
 y:='y';
 n:=nops(alpha);
 orb:=ZOrbit(Type,beta);
 1/nops(orb)*convert(map(l->y[op(Pull(Type,alpha+l))],orb),`+`);
end proc:

TPolyRecurrence:=proc(Type,alpha) option remember; # input list with nonnegative integer entries, at least one nonzero
 local n, N, i, j, beta, gamma, orb, K, eq;
 n:=nops(alpha);
 N:=WeylGroupOrder(Type,n);
 beta:=Pull(Type,alpha);
 if `and`(seq(is(beta[i]=0),i=1..n)) then
  return T[seq(0,i=1..n)]
 fi;
 j:=select(i->is(beta[i]>0),[seq(i,i=1..n)])[1];
 gamma:=[seq(`if`(i=j,1,0),i=1..n)];
 orb:=ZOrbit(Type,gamma);
 K:=map(l->Pull(Type,beta - gamma + l),orb);
 eq:=convert([seq(T[op(K[i])],i=1..nops(K))],`+`);
 solve(nops(orb)*T[op(gamma)]*T[op(beta-gamma)]=eq,T[op(beta)]);
end proc:

TPoly:=proc(Type,alpha) #for normalized orbit polynomials as in the article
 option remember;
 local n, N, beta, i, j, index, gamma, orb, K, KK, KKK, l, k;
 n:=nops(alpha);
 beta:=Pull(Type,alpha);
 global z;
 z:='z';
 if `and`(seq(is(beta[i]=0),i=1..n)) then
  return 1
 fi;
 for j from 1 to n do
  if beta[j]=1 and `and`(seq(is(beta[i]=0),i=1..j-1)) and `and`(seq(is(beta[i]=0),i=j+1..n)) then
   return z[j]
  fi;
 od;
 #Now comes the actual procedure:
 index:=select(i->is(beta[i]>0),[seq(1..n)])[1];
 gamma:=[seq(`if`(j=index,1,0),j=1..n)];
 orb:=ZOrbit(Type,gamma);
 K:=map(l->Pull(Type,beta-gamma + l),orb);
 KK:=select(k->`and`(seq(    is(k[i]=beta[i]) ,i=1..n)),K);
 KKK:=select(k->`or`(seq(not(is(k[i]=beta[i])),i=1..n)),K);
 expand(1/nops(KK)*(nops(orb)*TPoly(Type,gamma)*TPoly(Type,beta-gamma)-convert(map(k->TPoly(Type,k),KKK),`+`)));
end proc:

TPolyFat:=proc(Type,alpha) #for not-normailzed orbit polynomials
 option remember;
 local n, N, beta, i, j, index, gamma, orb, K, KK, KKK, l, k;
 n:=nops(alpha);
 N:=WeylGroupOrder(Type,n);
 beta:=Pull(Type,alpha);
 global z;
 z:='z';
 if `and`(seq(is(beta[i]=0),i=1..n)) then
  return N
 fi;
 for j from 1 to n do
  if beta[j]=1 and `and`(seq(is(beta[i]=0),i=1..j-1)) and `and`(seq(is(beta[i]=0),i=j+1..n)) then
   return z[j]
  fi;
 od;
 #Now comes the actual procedure:
 index:=select(i->is(beta[i]>0),[seq(1..n)])[1];
 gamma:=[seq(`if`(j=index,1,0),j=1..n)];
 orb:=ZOrbit(Type,gamma);
 K:=map(l->Pull(Type,beta-gamma + l),orb);
 KK:=select(k->`and`(seq(    is(k[i]=beta[i]) ,i=1..n)),K);
 KKK:=select(k->`or`(seq(not(is(k[i]=beta[i])),i=1..n)),K);
 expand(1/nops(KK)*(nops(orb)/N*TPoly(Type,gamma)*TPoly(Type,beta-gamma)-convert(map(k->TPoly(Type,k),KKK),`+`)));
end proc:

ChebyshevInvariantRewrite:=proc(Type,n,invariant) option remember; # This proc will give an output regardless if the input is invariant or not. Input must be Laurent polynomial in x[i]
local W, Var, Terms, Expo, Split, NewTerms, Coset, i, j, k, l;
global T; 
 T:='T'; 
 Var:=[seq(x[i],i=1..n)]; 
 Terms:=[op(expand(invariant))]; 
 Expo:=map(k->map(l->degree(k,l),Var), Terms); 
 Split:=[seq([Terms[j]*convert([seq(Var[i]^(-Expo[j][i]),i=1..n)],`*`),map(l->degree(Terms[j],l),Var)], j=1..nops(Terms))]; 
 NewTerms:=select(l->`and`(seq(is(l[2][i]>=0),i=1..n)), Split); 
 convert(map(l->ZOrbitCardinality(Type,l[2])*l[1]*T[op(l[2])], NewTerms),`+`);  # nops(ZOrbit(Type,map(k->if k>=1 then 1 else 0 fi,l[2])))
end proc:

InvariantRewrite:=proc(Type,n,invariant) option remember; # This proc will give an output regardless if the input is invariant or not. Input must be Laurent polynomial in x[i]
local W, Var, Terms, Expo, Split, NewTerms, i, j, k, l;
global y; 
 y:='y'; 
 Var:=[seq(x[i],i=1..n)]; 
 Terms:=[op(expand(invariant))]; 
 Expo:=map(k->map(l->degree(k,l),Var),Terms); 
 Split:=[seq([Terms[j]*convert([seq(Var[i]^(-Expo[j][i]),i=1..n)],`*`),map(l->degree(Terms[j],l),Var)],j=1..nops(Terms))]; 
 NewTerms:=select(l->`and`(seq(is(l[2][i]>=0),i=1..n)), Split); 
 convert(map(l->ZOrbitCardinality(Type,l[2])*l[1]*TPoly(Type,l[2]), NewTerms),`+`); 
end proc:

MonomialMultiply:=proc(alpha,beta) # recurrence formula for standard monomial basis (just for comparisons)
 global y;
 y:='y';
 y[op(alpha+beta)];
end proc:

MonomialExponent:=proc(n,degbound)
 local LL, L, i;
 [seq(op({op(map(LL->op(combinat[permute](LL)),select(L->nops(L)=n,combinat[partition](i)))),op(map(LL->op(combinat[permute](LL-[seq(1,i=1..n)])),select(L->nops(L)=n,combinat[partition](i+n))))}),i=0..degbound)];
end proc:

MonomialExponent2:=proc(n,degbound)
 local LL, L, i;
 [seq(op({op(map(LL->op(combinat[permute](LL)),select(L->nops(L)=n,combinat[partition](i)))),op(map(LL->op(combinat[permute](LL-[seq(1,i=1..n)])),select(L->nops(L)=n,combinat[partition](i+n))))}),i=0..2*degbound)];
end proc:

ChebyshevDegExp:=proc(Type,n,l,bound) option remember;
 local i, L;
 select( L-> l*VertexFundomCoefficient(Type,n)[1] = convert([seq(L[i],i=1..n)],`+`) and convert([seq(VertexFundomCoefficient(Type,n)[1..n][i]*L[i],i=1..n)],`+`) <= bound,MonomialExponent(n,bound));
end proc:

WeightList:=proc(Type,n,d)
 local L, i, k;
 L:=[seq(op(map(k->op(ZOrbit(Type,k)),ChebyshevLevel(Type,n,i))),i=0..d)];
end proc:

ChebyshevLevel:=proc(Type,n,l) option remember;
 local F, L, i;
 F:=VertexFundomCoefficient(Type,n);
 if Type='F' and n=4 then
  select( L-> l = convert([seq(F[1..n][i]*L[i],i=1..n)],`+`),MonomialExponent(n,l))
 else
  select( L-> l*F[1] = convert([seq(F[1..n][i]*L[i],i=1..n)],`+`),MonomialExponent(n,l))
 fi;
end proc:

#if a Groebner basis H is given by the 'Shape lemma' in permuted Variables z then the variety can be obtained by this procedure (assuming ideal is zero dimensional)
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

ProcesiSchwarzMatrix:=proc(Type,n)
 option remember;
 local i, j, S, theta, gradtheta, D, x;
 theta:=FundamentalInvariant(Type,n):
 for i from 1 to n do
  for j from 1 to n do
   if i=j then
    D[i](x[j]):=x[j]
   else
    D[i](x[j]):=0
   fi;
  od;
 od;
 gradtheta:=[seq(<seq(D[j](theta[i]),j=1..n)>,i=1..n)]:
 #GP:=ZWeylGroup(Type,n): S:=convert(map(g->Transpose(g).g,GP),`+`)/nops(GP):   #alternative invariant matrix
 S:=Transpose(WeightMatrix(Type,n)).WeightMatrix(Type,n):
 if Type=A then
  return -Matrix( n , (i,j) -> InvariantRewrite(Type,n,expand( Transpose(gradtheta[i]).S.gradtheta[n+1-j] ) ) ) ;
 elif Type=D and is(n,odd) then
  return -Matrix( n , (i,j) -> InvariantRewrite(Type,n,expand( Transpose(gradtheta[i]).S.gradtheta[if j=n-1 then n elif j=n then n-1 else j fi] ) ) ) ;
 elif Type=E and n=6 then
  return -Matrix( n , (i,j) -> InvariantRewrite(Type,n,expand( Transpose(gradtheta[i]).S.gradtheta[if j=1 then 6 elif j=3 then 5 elif j=5 then 3 elif j=6 then 1 else j fi] ) ) ) ;
 else
  return -Matrix( n , (i,j) -> InvariantRewrite(Type,n,expand( Transpose(gradtheta[i]).S.gradtheta[    j] ) ) ) ;
 fi:
end proc:

CoefficientListPoly:=proc(Type,n,d,poly) option remember;
local Var, Inv, i, k, N, L, Weights;
global x; 
if type(poly,list) then
 N:=max(map(k->Transpose(WeightMatrix(Type,n).<k[1]>).<HighestRoot(Type,n)>/VertexFundomCoefficient(Type,n)[1],poly));
 L:=[seq(op(ChebyshevLevel(Type,n,k)),k=0..N)];
 L:=map(l -> if nops(l) = 1 then l[1] else 0 fi, map(l -> map(k -> k[2], select(k -> is(k[1] = l), poly)), L)); 
 Weights:=[seq(op(ChebyshevLevel(Type,n,k)),k=0..2*d)];
 return [op(L),seq(0,i=nops(L)+1..nops(Weights))];
else
 x:='x'; 
 Var:=[seq(x[i],i=1..n)]; 
 Inv:=expand(subs([seq(z[i]=FundamentalInvariant(Type,n)[i],i=1..n)],poly));
 return CoefficientListLaurentPoly(Type,n,d,Inv)
fi;
end proc:

CoefficientListLaurentPoly:=proc(Type,n,d,Inv) option remember;
local Var, Terms, Expo, Split, NewTerms, i, j, k, l, fun, N, L, Weights;
global x; 
 x:='x'; 
 Var:=[seq(x[i],i=1..n)]; 
 Terms:=[op(expand(Inv))]; 
 Expo:=map(k->map(l->degree(k,l),Var),Terms); 
 Split:=[seq([Terms[j]*convert([seq(Var[i]^(-Expo[j][i]),i=1..n)],`*`),map(l->degree(Terms[j],l),Var)],j=1..nops(Terms))]; 
 NewTerms:=select(l->`and`(seq(is(l[2][i]>=0),i=1..n)), Split); 
 fun:=map(l->[ZOrbitCardinality(Type,l[2])*l[1],l[2]],NewTerms);
 N:=max(map(k->Transpose(WeightMatrix(Type,n).<k[2]>).<HighestRoot(Type,n)>/VertexFundomCoefficient(Type,n)[1],fun));
 L:=[seq(op(ChebyshevLevel(Type,n,k)),k=0..N)];
 L:=map(l -> if nops(l) = 1 then l[1] else 0 fi, map(l -> map(k -> k[1], select(k -> is(k[2] = l), fun)), L)); 
 Weights:=[seq(op(ChebyshevLevel(Type,n,k)),k=0..2*d)];
 return [op(L),seq(0,i=nops(L)+1..nops(Weights))];
end proc:

DegreePoly:=proc(Type,n,poly) option remember;
local Var, Inv, VertCoeff, i, k, N, L;
global x; 
if type(poly,list) then
 VertCoeff:=[seq(VertexFundomCoefficient(Type,n)[i],i=1..n)]/VertexFundomCoefficient(Type,n)[1];
 return max(map(k-><k[1]>.<VertCoeff>,poly));
else
 x:='x'; 
 Var:=[seq(x[i],i=1..n)]; 
 Inv:=expand(subs([seq(z[i]=FundamentalInvariant(Type,n)[i],i=1..n)],poly));
 return DegreeLaurentPoly(Type,n,Inv)
fi;
end proc:

DegreeLaurentPoly:=proc(Type,n,Inv) option remember;
local Var, Terms, Expo, VertCoeff, i, j, k, l, fun, N, L;
global x; 
 x:='x'; 
 Var:=[seq(x[i],i=1..n)]; 
 Terms:=[op(expand(Inv))]; 
 Expo:=map(k->map(l->degree(k,l),Var),Terms); 
 VertCoeff:=[seq(VertexFundomCoefficient(Type,n)[i],i=1..n)]/VertexFundomCoefficient(Type,n)[1];
 return max(map(k-><Pull(Type,k)>.<VertCoeff>,Expo));
end proc:

DegreeWeightSet:=proc(Type,n,Set) option remember;
local Var, Inv, VertCoeff, i, k, N, L;
global x; 
 VertCoeff:=[seq(VertexFundomCoefficient(Type,n)[i],i=1..n)]/VertexFundomCoefficient(Type,n)[1];
 return max(map(k-><k>.<VertCoeff>,Set));
end proc:


#############
#TORBITSPACE#
#############

VertexTOrbitSpace:=proc(Type,n) # list of vertices of the T-orbit space
 local i;
 return [seq(GeneralizedCosine(Type,n,VertexFundom(Type,n)[i]),i=1..n+1)];
end proc:

VertexRTOrbitSpace:=proc(Type,n) # list of vertices of the T-orbit space
 local i;
 return [seq(RGeneralizedCosine(Type,n,VertexFundom(Type,n)[i]),i=1..n+1)];
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
   f[k]:=(-1)^(k+1)*binomial(n,k)*Y[k];
  od:
  f[n]:=(-1)^(n+1)*(2^n*Y[n]^2-convert([seq(binomial(n,i)*Y[i],i=1..n-1)],`+`)-1);
  CompMat:=Matrix(n,(i,j)-> if  (i = j+1 and j <= n-1) then 1
                            elif j <= n-1 then 0
                            else f[n-i+1]
                            fi):
  Matrix(n,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 elif Type = C then
  Y:=[seq(z[i],i=1..n)]:
  for k from 1 to n do
   f[k]:=(-1)^(k+1)*binomial(n,k)*Y[k];
  od:
  CompMat:=Matrix(n,(i,j)-> if  (i = j+1 and j <= n-1) then 1
                            elif j <= n-1 then 0
                            else f[n-i+1]
                            fi):
  Matrix(n,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 elif Type = D then
  Y:=[seq(z[i],i=1..n)]:
  for k from 1 to n-2 do
   f[k]:=(-1)^(k+1)*binomial(n,k)*Y[k];
  od:
  if is(n,even) then
   f[n-1]:=(-1)^(n)*( 2^(n-1)*Y[n]*Y[n-1]       -convert([seq(binomial(n,2*i-1)*Y[2*i-1],i=1..(n-2)/2)],`+`)   );
   f[n]  :=(-1)^(n+1)*( 2^(n-2)*(Y[n]^2+Y[n-1]^2) -convert([seq(binomial(n,2*i)  *Y[2*i]  ,i=1..(n-2)/2)],`+`) -1);
  else
   f[n-1]:=(-1)^(n)*( 2^(n-1)*Y[n]*Y[n-1]       -convert([seq(binomial(n,2*i)  *Y[2*i]  ,i=1..(n-3)/2)],`+`) -1);
   f[n]  :=(-1)^(n+1)*( 2^(n-2)*(Y[n]^2+Y[n-1]^2) -convert([seq(binomial(n,2*i+1)*Y[2*i+1],i=1..(n-3)/2)],`+`)   );
  fi:
  CompMat:=Matrix(n,(i,j)-> if  (i = j+1 and j <= n-1) then 1
                            elif j <= n-1 then 0
                            else f[n-i+1]
                            fi):
  Matrix(n,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 elif Type = G and n = 2 then
  f[3]:=3*z[1]:
  f[2]:=-3*(z[1]+z[2])/2:
  f[1]:=(9*z[1]^2-3*z[1]-3*z[2]-1)/2:
  CompMat:=Matrix(n+1,(i,j)-> if  (i = j+1 and j <= n) then 1
                              elif j <= n then 0
                              else f[i]
                              fi):
  Matrix(n+1,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D, G")
 fi;
end proc:

RHermiteMatrix:=proc(Type,n)
 local i, j, k, f, Y, CompMat;
 global z;
 z:='z';
 if Type=B or Type=C or Type=G then
  HermiteMatrix(Type,n)
 elif Type=D and is(n,even) then
  HermiteMatrix(Type,n)
 elif Type=D and is(n,odd) then
  Y:=[seq(z[i],i=1..n)]:
  for k from 1 to n-2 do
   f[k]:=(-1)^(k+1)*binomial(n,k)*Y[k];
  od:
  f[n-1]:=(-1)^(n  )*(2^(n-1)*(Y[n]^2+Y[n-1]^2)-convert([seq(binomial(n,2*i)  *Y[2*i]  ,i=1..(n-3)/2)],`+`) -1);
  f[n]  :=(-1)^(n+1)*(2^(n-1)* Y[n]^2          -convert([seq(binomial(n,2*i+1)*Y[2*i+1],i=1..(n-3)/2)],`+`)   );
  CompMat:=Matrix(n,(i,j)-> if  (i = j+1 and j <= n-1) then 1
                            elif j <= n-1 then 0
                            else f[n-i+1]
                            fi):
  Matrix(n,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
 elif Type = G and n = 2 then
  f[3]:=3*z[1]:
  f[2]:=-3*(z[1]+z[2])/2:
  f[1]:=(9*z[1]^2-3*z[1]-3*z[2]-1)/2:
  CompMat:=Matrix(n+1,(i,j)-> if  (i = j+1 and j <= n) then 1
                              elif j <= n then 0
                              else f[i]
                              fi):
  Matrix(n+1,(i,j)->expand(Trace(CompMat^(i+j-2))-Trace(CompMat^(i+j))))
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
  printf("Error: root system must be of simple Lie Type A, B, C, D, G")
 fi;
end proc:

MonomialRewrite:=proc(n,invariant)
local TermsMatrixEntry, ExponentsMatrixEntry, SplitTermsMatrixEntry, i, j, k, l;
global y;
 y:='y';
 TermsMatrixEntry:=[op(expand(invariant))];
 ExponentsMatrixEntry:=[seq([seq(degree(op(TermsMatrixEntry)[j],z[i]),i=1..n)],j=1..nops(TermsMatrixEntry))];
 SplitTermsMatrixEntry:=[seq([TermsMatrixEntry[j]*convert([seq(z[i]^(-ExponentsMatrixEntry[j][i]),i=1..n)],`*`),[seq(degree(op(TermsMatrixEntry)[j],z[i]),i=1..n)]],j=1..nops(TermsMatrixEntry))];
 convert([seq(SplitTermsMatrixEntry[i,1]*y[op(SplitTermsMatrixEntry[i,2])],i=1..nops(SplitTermsMatrixEntry))],`+`);
end proc:

THermiteEntries:=proc(Type,n,k) option remember;
local i, j;
global T;
 if Type = A then
  if is(k::odd) then
   (convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(T[k-2*j,seq(0,i=1..n-2)]+T[seq(0,i=1..n-2),k-2*j]),j=1..(k-1)/2)],`+`)-(T[k,seq(0,i=1..n-2)]+T[seq(0,i=1..n-2),k]) )
  else
   (convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(T[k-2*j,seq(0,i=1..n-2)]+T[seq(0,i=1..n-2),k-2*j]),j=1..k/2-1  )],`+`)-(T[k,seq(0,i=1..n-2)]+T[seq(0,i=1..n-2),k])
   +(4*binomial(k-2,k/2-1)-binomial(k,k/2))*T[0,seq(0,i=1..n-2)])
  fi;
 elif Type = B or Type = C or Type = D then
  if is(k::odd) then
   (convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*T[k-2*j,seq(0,i=1..n-1)],j=1..(k-1)/2)],`+`)-T[k,seq(0,i=1..n-1)])
  else
   (convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*T[k-2*j,seq(0,i=1..n-1)],j=1..k/2-1)],`+`)-T[k,seq(0,i=1..n-1)]
   +(-binomial(k,k/2)+4*binomial(k-2,k/2-1))/2*T[0,seq(0,i=1..n-1)])
  fi;
 elif Type = G then
  if is(k::odd) then
   (convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*T[k-2*j,0],j=1..(k-1)/2)],`+`)-T[k,0])
  else
   (convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*T[k-2*j,0],j=1..k/2-1  )],`+`)-T[k,0]+(-binomial(k,k/2)+4*binomial(k-2,k/2-1))/2*T[0,0])
  fi;
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D, G")
 fi;
end proc:

THermiteMatrix:=proc(Type,n)
local i, j;
global T;
 if Type = B or Type = C or Type = D then
  Matrix(n  ,(i,j)->THermiteEntries(Type,n,  i+j));
 elif Type = A then 
  Matrix(n+1,(i,j)->THermiteEntries(Type,n+1,i+j));
 elif Type = G and n = 2 then
  Matrix(3  ,(i,j)->THermiteEntries(Type,2  ,i+j));
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D, G")
 fi;
end proc:

RTHermiteEntriesOld:=proc(Type,n,k)
 local i, j;
 global T;
 if Type = A then
  if is(k::odd) then
   convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(y[k-2*j,seq(0,i=1..n-2)]),j=1..(k-1)/2)],`+`)-(y[k,seq(0,i=1..n-2)])
  else
   convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(y[k-2*j,seq(0,i=1..n-2)]),j=1.. k/2 -1)],`+`)-(y[k,seq(0,i=1..n-2)])+(-binomial(k,k/2)+4*binomial(k-2,k/2-1))/2*y[0,seq(0,i=1..n-2)]
  fi;
 elif Type = B or Type = C or Type = D then
  THermiteEntries(Type,n,k)
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D")
 fi;
end proc:

RTHermiteEntries:=proc(n,k)
 local i, j;
 global T;
  if is(k::odd) then
   convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(T[k-2*j,seq(0,i=1..n-1)]),j=1..(k-1)/2)],`+`)-(T[k,seq(0,i=1..n-1)])
  else
   convert([seq((4*binomial(k-2,j-1)-binomial(k,j))*(T[k-2*j,seq(0,i=1..n-1)]),j=1.. k/2 -1)],`+`)-(T[k,seq(0,i=1..n-1)])
   +(-binomial(k,k/2)+4*binomial(k-2,k/2-1))/2*T[0,seq(0,i=1..n-1)]
  fi;
end proc:

RTHermiteMatrix:=proc(Type,n)
 local i, j;
 global y;
 if Type = A or (Type = G and n = 2) then 
  Matrix(n+1,(i,j)->RTHermiteEntries(n,i+j));
 elif Type = B or Type = C or Type = D then
  Matrix(n  ,(i,j)->RTHermiteEntries(n,i+j));
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D, G")
 fi;
end proc:

#########
#Moments#
#########

TMomentMatrix:=proc(Type,n,d) option remember; # moment matrix in Chebyshev basis up to degree degbound
 local i, j, L, l;
 L:=[seq(op(ChebyshevLevel(Type,n,l)),l=0..d)];
 Matrix(nops(L),(i,j)->TMultiply(Type,L[i],L[j]));
end proc:

TruncatedMonomialMomentMatrix:=proc(n,degbound) # moment matrix in standard monomial basis up to degree degbound
 local i, j;
 Matrix(binomial(n+degbound,n),(i,j)->MonomialMultiply(MonomialExponent2(n,degbound)[i],MonomialExponent2(n,degbound)[j]));
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
 <seq(Transpose(<seq(convert(map(k->k[1]*y[op(Pull(Type,k[2]+Y[i]+Y[j]))],H),`+`),i=1..binomial(n+d,n))>),j=1..binomial(n+d,n))>;
end proc:

TLocalizedMomentMatrix:=proc(Type,n,d) option remember; # works for Bn, Cn, D2n
 local i, j, k, l, ll, Y, N, Orbs, H, h, yy;
 global y;
 y:='y';
 Y:=[seq(op(ChebyshevLevel(Type,n,l)),l=0..d)];
 N:=nops(Y);
 Orbs:=[seq(ZOrbit(Type,Y[i]),i=1..N)];
 #Y:=MonomialExponent(n,d)
 #Y:=[seq(op(select(yy->Transpose(WeightMatrix(Type,n).<yy>).<HighestRoot(Type,n)> = VertexFundomCoefficient(Type,n)[1]*k,Y)),k=0..d)]
 if Type = B or Type = C or Type = D then
  H:=[seq([Matrix(n,(i,j) -> if   (is(k-i-j,odd) or (k > i+j)) then 0  # following the formula for the matrix entries 
                             elif k = i+j then -1
                             elif k = 0 then 2*binomial(i+j-2,(i+j-2)/2) - 1/2*binomial(i+j,(i+j)/2)
                             else 4*binomial(i+j-2,(i+j-k)/2-1) - binomial(i+j,(i+j-k)/2)
                             fi ) , 
           [k , seq(0 , i = 2..n)]] ,
          k = 0..2*n)];
  <seq(Transpose(<seq((convert(map(h -> h[1]*(convert(map(ll->op(map(l->y[op(Pull(Type,h[2]+l+ll))],Orbs[i])),Orbs[j]),`+`)),
                                   H),`+`))/nops(Orbs[i])/nops(Orbs[j]),i=1..N)>),j=1..N)>;
 elif Type = A then
  H:=[seq([Matrix(n+1,(i,j) -> if   (is(k-i-j,odd) or (k > i+j)) then 0  # following the formula for the matrix entries 
                               elif k = i+j then -1/2^(i+j)
                               elif k = 0 then (4*binomial(i+j-2,(i+j-2)/2) - binomial(i+j,(i+j)/2))/2^(i+j+1)
                               else (4*binomial(i+j-2,(i+j-k)/2-1) - binomial(i+j,(i+j-k)/2))/2^(i+j)
                               fi ) , 
           [k , seq(0 , i = 2..n)] , [seq(0 , i = 1..n-1) , k] ] ,
          k = 0..2*n+2)];
  <seq(Transpose(<seq((convert(map(h -> h[1]*(   convert(map(ll->op(map(l->y[op(Pull(Type,h[2]+l+ll))],Orbs[i])),Orbs[j]),`+`)
                                               + convert(map(ll->op(map(l->y[op(Pull(Type,h[3]+l+ll))],Orbs[i])),Orbs[j]),`+`)),
                                   H),`+`))/nops(Orbs[i])/nops(Orbs[j]),i=1..N)>),j=1..N)>;
 elif Type = G and n = 2 then
  H:=[seq([Matrix(3,(i,j) -> if   (is(k-i-j,odd) or (k > i+j)) then 0  # following the formula for the matrix entries 
                             elif k = i+j then -1
                             elif k = 0 then 2*binomial(i+j-2,(i+j-2)/2) - 1/2*binomial(i+j,(i+j)/2)
                             else 4*binomial(i+j-2,(i+j-k)/2-1) - binomial(i+j,(i+j-k)/2)
                             fi ) , [k , 0]] , k = 0..6)];
  <seq(Transpose(<seq((convert(map(h -> h[1]*(convert(map(ll->op(map(l->y[op(Pull(Type,h[2]+l+ll))],Orbs[i])),Orbs[j]),`+`)),
                                   H),`+`))/nops(Orbs[i])/nops(Orbs[j]),i=1..N)>),j=1..N)>;
 else
  printf("Error: root system must be of simple Lie Type A, B, C, D, G")
 fi;
end proc:

SDPMatrices:=proc(Type,n,d,name) option remember; #This is for the SDP solver, d must be at least n

 local Y, N, MY, MHY, M, i, k, Constraints, Mat;

 #Y:=MonomialExponent2(n,d);
 #Y:=select(yy->Transpose(WeightMatrix(Type,n).<yy>).<HighestRoot(Type,n)> <= VertexFundomCoefficient(Type,n)[1]*2*d,Y);
 Y:=[seq(op(ChebyshevLevel(Type,n,i)),i=0..2*d)];
 N:=nops(Y);
 MY:=TMomentMatrix(Type,n,d);
 if Type = B or Type = C or Type = D then
  MHY:=TLocalizedMomentMatrix(Type,n,d-n);
 elif Type = A or Type = G then
  MHY:=TLocalizedMomentMatrix(Type,n,d-n-1);
 fi;
 M:=<<MY|Matrix(RowDimension(MY),RowDimension(MHY))>,<Matrix(RowDimension(MHY),RowDimension(MY))|MHY>>;

 Constraints := map(Mat->convert(Mat,listlist),[seq(CoeffInMatrix(y[op(Y[i])],M),i=1..N)]);

 Export(name,['A0,A'=op([Constraints[1],[seq(Constraints[i],i=2..nops(Constraints))]])]);
end proc:

SDPCoefficients:=proc(Type,n,d,poly,name)
 local Coef, i;
 Coef:=CoefficientListPoly(Type,n,d,poly);
 Export(name,['C0,C'=op([Coef[1],[seq(Coef[i],i=2..nops(Coef))]])]);
end proc:

SDPMinMaxCoefficients:=proc(Type,n,d,SS,bb,LU,name)
 local i, L, l, s, Input;
 Input:=[seq([SS[i],LU[i],bb[i]], i=1..nops(SS))];
 L:=[seq(op(ChebyshevLevel(Type,n,i)), i=0..2*d)]:
 L:=[seq([L[i],i],i=1..nops(L))]:
 L:=map(l->select(s->is(s[1] = l[1]),Input),L):
 L:=[seq(if nops(L[i])=0 then [[0,0],0] else [op(L[i])[2],op(L[i])[3]] fi, i=1..nops(L))];
 Export(name,['b,L,U' = op([[seq(L[i][2],i=2..nops(L))],[seq(L[i][1][1],i=2..nops(L))],[seq(L[i][1][2],i=2..nops(L))]])]);
end proc:

TArchimedeanPMI:=proc(Type,n,d) option remember; # works for Bn, Cn, D2n
 local i, ii, j, l, ll, lll, k, Y, N, Orbs, ExtraOrbs, H, h, yy;
 global y;
 y:='y';
 Y:=[seq(op(ChebyshevLevel(Type,n,l)),l=0..d)];
 N:=nops(Y);
 Orbs:=[seq(ZOrbit(Type,Y[i]),i=1..N)];
 ExtraOrbs:=[seq(ZOrbit(Type,[seq(`if`(i=k,1,0),i=1..n)]),k=1..n)];
 if Type = B or Type = C or Type = D then
  <seq(
       Transpose(
                 <seq(
                      (n-(convert(
                                  [seq(
                                       (convert(
                                                map(lll->op(map(ll->op(map(l->
                                                                           y[op(Pull(Type,[seq(`if`(ii=k,1,0),ii=1..n)]+l+ll+lll))]
                                                                           ,Orbs[i])),Orbs[j])),ExtraOrbs[k])
                                                ,`+`))/nops(Orbs[i])/nops(Orbs[j])/nops(ExtraOrbs[k])
                                       ,k=1..n)]
                                  ,`+`)))
                      ,i=1..N)>
                 )
       ,j=1..N)>;
 else
  printf("Error: root system must be of simple Lie Type B, C, D")
 fi;
end proc:

ChebyshevArchimedeanSDP:=proc(Type,n,d,name) option remember; #This is for the SDP solver, d must be at least n
 local dH, dP, Y, N, MY, MHY, MPY, nY, nHY, nPY, M, i, k, Constraints;
 dP:=max(VertexFundomCoefficient(Type,n))/VertexFundomCoefficient(Type,n)[1];
 dH:=n;
 Y:=[seq(op(ChebyshevLevel(Type,n,i)),i=0..2*d)];
 N:=nops(Y);
 MY:=TMomentMatrix(Type,n,d);
 if Type=B or Type=C or Type=D then
  MHY:=TLocalizedMomentMatrix(Type,n,d-dH);
  MPY:=TArchimedeanPMI(Type,n,d-dP);
 else
  printf("Error: root system must be of simple Lie Type B, C, D")
 fi;
 nY :=RowDimension(MY);
 nHY:=RowDimension(MHY);
 nPY:=RowDimension(MPY);
 M:=<<MY|Matrix(nY,nHY)|Matrix(nY,nPY)>,<Matrix(nHY,nY)|MHY|Matrix(nHY,nPY)>,<Matrix(nPY,nY)|Matrix(nPY,nHY)|MPY>>;

 Constraints := [ seq(CoeffInMatrix(y[op(Y[i])],M),i=1..N) ] ;
 
 Export(name,[Constraints]);
end proc:


####################
#SYMMETRYADAPTATION#
####################

EntryNameVecMultiplicative:=proc(Type,n,d,k) option remember;
 local i, L;
 L:=WeightList(Type,n,d);
 for i from 1 to nops(L) do
  if k=L[i] then
   return i
  fi;
 od;
end proc:

BigRepGenMultiplicative:=proc(Type,n,d) option remember;
 local i, j, k, l, listy, L, s, W; 
 s:=ZWeylGroupGen(Type,n); 
 L:=WeightList(Type,n,d); 
 listy:=[seq([seq([EntryNameVecMultiplicative(Type,n,d,L[k]),EntryNameVecMultiplicative(Type,n,d,convert(s[l].<L[k]>,list))],k=1..nops(L))],l=1..n)]; 
 [seq(Matrix(nops(L),(i,j)->if `or`(seq(is([i,j]=listy[l][k]),k=1..nops(listy[l]))) then 1 else 0 fi),l=1..n)]; 
end proc: 

IrredRepGenMultiplicative:=proc(Type,n) option remember;
 if Type = A and n = 2 then 
  [[Matrix([[ 1]]),Matrix([[ 1]])],
   [Matrix([[-1]]),Matrix([[-1]])],
   [Matrix([[-1,1],[0,1]]),Matrix([[1,0],[1,-1]])]]
 elif (Type = B or Type = C) and n = 2 then
  [[Matrix([[ 1]]),Matrix([[ 1]])],
   [Matrix([[-1]]),Matrix([[ 1]])],
   [Matrix([[ 1]]),Matrix([[-1]])],
   [Matrix([[-1]]),Matrix([[-1]])],
   [Matrix([[0,1],[1,0]]),Matrix([[1,0],[0,-1]])]]
 elif Type = G and n = 2 then
  [[Matrix([[ 1]]),Matrix([[ 1]])],
   [Matrix([[-1]]),Matrix([[ 1]])],
   [Matrix([[-1]]),Matrix([[-1]])],
   [Matrix([[ 1]]),Matrix([[-1]])],
   [Matrix([[-1, 0],[ 1, 1]]),Matrix([[ 1, 3],[ 0,-1]])],
   [Matrix([[-2,-3],[ 1, 2]]),Matrix([[ 1, 3],[ 0,-1]])]]
 elif Type = D and n = 3 then
  [[Matrix([[ 1]]),
    Matrix([[ 1]]),
    Matrix([[ 1]])],
   [Matrix([[-1]]),
    Matrix([[-1]]),
    Matrix([[-1]])],
   [Matrix([[-1,-1],[ 0, 1]]),
    Matrix([[ 0, 1],[ 1, 0]]),
    Matrix([[ 0, 1],[ 1, 0]])],
   [Matrix([[ 0, 1, 0],[ 1, 0, 0],[ 0, 0, 1]]),
    Matrix([[ 1, 0, 0],[ 0, 0, 1],[ 0, 1, 0]]),
    Matrix([[ 1, 0, 0],[ 0, 0,-1],[ 0,-1, 0]])],
   [Matrix([[-1, 0, 0],[ 0, 0, 1],[ 0, 1, 0]]),
    Matrix([[ 0, 1, 0],[ 1, 0, 0],[ 0, 0,-1]]),
    Matrix([[ 0,-1, 0],[-1, 0, 0],[ 0, 0,-1]])]]
 elif Type = B and n = 3 then
  [[Matrix([[ 1]]),Matrix([[ 1]]),Matrix([[ 1]])],
   [Matrix([[ 1]]),Matrix([[ 1]]),Matrix([[-1]])],
   [Matrix([[-1]]),Matrix([[-1]]),Matrix([[ 1]])],
   [Matrix([[-1]]),Matrix([[-1]]),Matrix([[-1]])],
   [Matrix([[-1,1],[0,1]]),Matrix([[1,0],[1,-1]]),Matrix([[1,0],[0,1]])],
   [Matrix([[-1,1],[0,1]]),Matrix([[1,0],[1,-1]]),Matrix([[-1,0],[0,-1]])],
   [Matrix([[0,1,0],[1,0,0],[0,0,1]]),Matrix([[1,0,0],[0,0,1],[0,1,0]]),Matrix([[1,0,0],[0,1,0],[0,0,-1]])],
   [Matrix([[1,0,0],[0,0,1],[0,1,0]]),Matrix([[0,1,0],[1,0,0],[0,0,1]]),Matrix([[1,0,0],[0,-1,0],[0,0,-1]])],
   [Matrix([[-1,0,0],[0,0,1],[0,1,0]]),Matrix([[0,1,0],[1,0,0],[0,0,-1]]),Matrix([[-1,0,0],[0,1,0],[0,0,1]])],
   [Matrix([[-1,0,0],[0,0,1],[0,1,0]]),Matrix([[0,1,0],[1,0,0],[0,0,-1]]),Matrix([[1,0,0],[0,-1,0],[0,0,-1]])]]
 else
  printf("Error: Only works for A2, B2, B3, C2, D3, G2")
 fi;
end proc:

GroupStructureMultiplicative:=proc(Type,n,L) option remember;
 local L1, L2, L3:
 if Type = A and n = 2 then
  [L[1]^2,L[1],L[2],L[1].L[2],L[2].L[1],L[1].L[2].L[1]];
 elif (Type = B or Type = C) and n = 2 then
  [L[1]^2,L[1],L[2],L[1].L[2],L[2].L[1],L[1].L[2].L[1],L[2].L[1].L[2],L[1].L[2].L[1].L[2]];
 elif Type = D and n = 3 then
  L1:=L[1]: L2:=L[2]: L3:=L[3]: 
  [L1^2, L1, L2, L3, L1.L2, L1.L3, L2.L1, L3.L1, L2.L3, L1.L2.L3, L2.L1.L3, L2.L3.L1, L3.L1.L2, L1.L2.L1, L1.L2.L3.L1, L1.L2.L1.L3, L1.L3.L1.L2, L2.L1.L3.L1, L2.L3.L1.L2, L1.L2.L3.L1.L2, L1.L2.L3.L2.L1, L1.L3.L2.L1.L3, L1.L2.L3.L1.L2.L3, L1.L2.L3.L1.L2.L3.L1];
 elif Type = B and n = 3 then
  L1:=L[1]: L2:=L[2]: L3:=L[3]: 
  [L1^2,L1, L2, L3,L1.L2, L1.L3, L2.L1, L2.L3, L3.L2,L1.L2.L1, L1.L2.L3, L1.L3.L2, L2.L1.L3, L2.L3.L2, L3.L2.L1, L3.L2.L3,L1.L2.L3.L1, L1.L2.L3.L2, L1.L3.L2.L1, L1.L3.L2.L3, L2.L1.L3.L2, L2.L3.L2.L1, L2.L3.L2.L3, L3.L2.L1.L3,L1.L2.L1.L3.L2, L1.L2.L3.L2.L1, L1.L2.L3.L2.L3, L1.L3.L2.L1.L3, L2.L1.L3.L2.L1, L2.L1.L3.L2.L3, L2.L3.L2.L1.L3, L3.L2.L1.L3.L2,L1.L2.L1.L3.L2.L1, L1.L2.L1.L3.L2.L3, L1.L2.L3.L2.L1.L3, L1.L3.L2.L1.L3.L2, L2.L1.L3.L2.L1.L3, L2.L3.L2.L1.L3.L2, L3.L2.L1.L3.L2.L3,L1.L2.L1.L3.L2.L1.L3, L1.L2.L3.L2.L1.L3.L2, L2.L1.L3.L2.L1.L3.L2, L2.L3.L2.L1.L3.L2.L3, L3.L2.L1.L2.L3.L2.L3, L3.L2.L1.L3.L2.L3.L1.L2, L3.L2.L1.L3.L2.L3.L2.L1,L1.L2.L1.L3.L2.L1.L3.L2,L1.L2.L1.L3.L2.L1.L3.L2.L3];
 elif Type = G and n = 2 then
  [L[1]^2,L[1],L[2],L[1].L[2],L[2].L[1],L[1].L[2].L[1],L[2].L[1].L[2],L[1].L[2].L[1].L[2],L[2].L[1].L[2].L[1],L[1].L[2].L[1].L[2].L[1],L[2].L[1].L[2].L[1].L[2].L[1],L[1].L[2].L[1].L[2].L[1].L[2].L[1]]
 else
  printf("Error: Only works for A2, B2, B3, C2, D3, G2")
 fi;
end proc:

IrredRepMultiplicative:=proc(Type,n) option remember;
 local Irr, h, i;
 Irr:=IrredRepGenMultiplicative(Type,n);
 h:=nops(Irr);
 return [seq(GroupStructureMultiplicative(Type,n,Irr[i]),i=1..h)];
end proc:

IrredRepDimMultiplicative:=proc(Type,n) option remember;
 local s;
 map(s->ColumnDimension(s[1]),IrredRepGenMultiplicative(Type,n));
end proc:

CharTableMultiplicative:=proc(Type,n) option remember;
 local Irr, BigRep, h, g, i, j;
 Irr:=IrredRepGenMultiplicative(Type,n);
 h:=nops(Irr);
 g:=WeylGroupOrder(Type,n);
 Transpose(Matrix(h,g,(i,j)->simplify(Trace(IrredRepMultiplicative(Type,n)[i][j]))));
end proc:

IsotypicDecompositionMultiplicitiesMultiplicative:=proc(Type,n,d) option remember;
 local W, WW, L, l, k, BigChar, i;
 W:=ZWeylGroupGen(Type,n);
 W:=GroupStructureMultiplicative(Type,n,W);
 L:=WeightList(Type,n,d);
 WW:=WeylGroupOrder(Type,n);
 BigChar:=Vector(WW,i->nops(select(k->is(k[1]=k[2]),map(l->[convert(W[i].<l>,list),l],L))));
 convert(LinearSolve(CharTableMultiplicative(Type,n),BigChar),list);
end proc:

IsotypicDecompositionBasisMultiplicative:=proc(Type,n,d) option remember;
 local s, i, j, h, l, L, BigRep, Irr, IrredRep, CharTable, BigChar, mm, dd, PPP , ColSpace, SymVec, T, PolyBasis, output;

 L:=WeightList(Type,n,d);

 if ((Type = A or Type = B or Type = C or Type = G) and n = 2) or ((Type = B or Type = D) and n = 3) then 

  BigRep:=GroupStructureMultiplicative(Type,n,BigRepGenMultiplicative(Type,n,d)):
 
  Irr:=IrredRepGenMultiplicative(Type,n);
  h:=nops(Irr);
  dd:=map(s->ColumnDimension(s[1]),IrredRepGenMultiplicative(Type,n)): #dimensions

  for i from 1 to h do
   IrredRep[i]:=GroupStructureMultiplicative(Type,n,Irr[i])
  od:
 
  CharTable:=Transpose(Matrix(h,nops(BigRep),(i,j)->Trace(IrredRep[i][j]))): #character table
  BigChar:=Vector(nops(BigRep),i->Trace(BigRep[i])): 
  mm:=convert(LinearSolve(CharTable,BigChar),list): #multiplicities
 
  for i from 1 to h do
   for l from 1 to dd[i] do
    PPP[i,l]:=simplify(dd[i]/nops(W)*convert([seq((IrredRep[i][j]^(-1))[1,l]*BigRep[j],j=1..nops(BigRep))],`+`))
   od;
  od;

  for i from 1 to nops(dd) do 
   ColSpace[i]:=ColumnSpace(PPP[i,1]); 
   for j from 1 to mm[i] do 
    SymVec[i,1,j]:=ColSpace[i][j]; 
    for l from 2 to dd[i] do 
     SymVec[i,l,j]:=PPP[i,l].SymVec[i,1,j] 
    od; 
   od; 
  od:
  
  T:=Matrix([seq(seq(seq(SymVec[i,l,j],l=1..dd[i]),j=1..mm[i]),i=1..nops(dd))]): 
  # blockdiagonalizes the matrices of the "big" representation, 
  # columns correspond to the irreducible representations as they occur in the isotypic components
  
  #Matrix([seq(seq(seq(SymVec[i,l,j],j=1..mm[i]),l=1..dd[i]),i=1..nops(dd))]): 
  # blockdiagonalizes equivariant matrices

  PolyBasis:=<map(weight->convert([seq(x[i]^weight[i],i=1..n)],`*`),L)>; 
  # basis of Laurent polynomials up to degree d

  output:=Transpose(T).PolyBasis;
  output:=map(s->s/subs([seq(x[i]=1,i=1..n)],convert(s,list)[1]),output);

  return [output,map(l->T^(-1).l.T,BigRepGenMultiplicative(Type,n,d))]; 
  # the coinvariant basis

 else
  printf("Error: Only works for A2, B2, B3, C2, D3, G2")
 fi;

end proc:



### For linear invariants (so far only G2)

EntryNameVecLinear:=proc(n,d,k) option remember;
 local i, L;
 L:=[seq(op(ChebyshevLevel('C',n,i)),i=0..d)];
 for i from 1 to nops(L) do
  if k=L[i] then
   return i
  fi;
 od;
end proc:

IrredRepGenLinear:=proc(n) option remember;
 local a; 
 a:=exp(2*Pi*I/6); 
  [[Matrix([[ 1]]),Matrix([[ 1]])],
   [Matrix([[ 1]]),Matrix([[-1]])],
   [Matrix([[-1]]),Matrix([[-1]])],
   [Matrix([[-1]]),Matrix([[ 1]])],
   [Matrix([[a,0],[0,1-a]]),Matrix([[0,1-a],[a,0]])],
   [Matrix([[a-1,0],[0,-a]]),Matrix([[0,-a],[a-1,0]])]]
end proc:

GroupStructureLinear:=proc(n,L) option remember;
  [L[1]^6,L[1]^5,L[1]^4,L[1]^3,L[1]^2,L[1],L[2].L[1]^6,L[2].L[1]^5,L[2].L[1]^4,L[2].L[1]^3,L[2].L[1]^2,L[2].L[1]]
end proc:

IrredRepLinear:=proc(n) option remember;
 local Irr, h, i;
 Irr:=IrredRepGenLinear(n);
 h:=nops(Irr);
 return [seq(GroupStructureLinear(n,Irr[i]),i=1..h)];
end proc:

IrredRepDimLinear:=proc(n) option remember;
 local s;
 map(s->ColumnDimension(s[1]),IrredRepGenLinear(n));
end proc:

CharTableLinear:=proc(n) option remember;
 local Irr, BigRep, h, g, i, j;
 Irr:=IrredRepGenLinear(n);
 h:=nops(Irr);
 g:=12;
 Transpose(Matrix(h,g,(i,j)->simplify(Trace(IrredRepLinear(n)[i][j]))));
end proc:

BigRepGenLinear:=proc(n,d) option remember; #ONLY FOR DIHEDRAL GROUP D6=G2
 local a, i, j, k, l, listy, L, s, W; 
 a:=exp(2*Pi*I/6);
 s:=[Matrix([[1,0],[0,1]]),Matrix([[0,1],[1,0]])];
 L:=[seq(op(ChebyshevLevel('C',n,i)),i=0..d)]; 
 listy:=[seq([seq([k,EntryNameVecLinear(n,d,convert(s[l].<L[k]>,list))],k=1..nops(L))],l=1..nops(s))]; 
 [seq(Transpose(map(expand,Matrix(nops(L),(i,j)->if `or`(seq(is([i,j]=listy[l][k]),k=1..nops(listy[l]))) then (a)^(L[i][1])*(1-a)^(L[i][2]) else 0 fi))),l=1..nops(s))]; 
end proc: 

IsotypicDecompositionMultiplicitiesLinear:=proc(n,d) option remember;
 local BigRep, BigChar, i;
 BigRep:=GroupStructureLinear(n,BigRepGenLinear(n,d)):
 BigChar:=Vector(nops(BigRep),i->Trace(BigRep[i])): 
 convert(LinearSolve(CharTableLinear(n),BigChar),list);
end proc:

IsotypicDecompositionBasisLinear:=proc(n,d) option remember;
 local s, i, j, h, l, L, BigRep, Irr, IrredRep, CharTable, BigChar, mm, dd, PPP , ColSpace, SymVec, T, PolyBasis, output;

 L:=[seq(op(ChebyshevLevel('C',n,i)),i=0..d)];

  BigRep:=GroupStructureLinear(n,BigRepGenLinear(n,d)):
 
  Irr:=IrredRepGenLinear(n);
  h:=nops(Irr);
  dd:=map(s->ColumnDimension(s[1]),IrredRepGenLinear(n)): #dimensions

  for i from 1 to h do
   IrredRep[i]:=GroupStructureLinear(n,Irr[i])
  od:
 
  CharTable:=Transpose(Matrix(h,nops(BigRep),(i,j)->Trace(IrredRep[i][j]))): #character table
  BigChar:=Vector(nops(BigRep),i->Trace(BigRep[i])): 
  mm:=convert(LinearSolve(CharTable,BigChar),list): #multiplicities
 
  for i from 1 to h do
   for l from 1 to dd[i] do
    PPP[i,l]:=simplify(dd[i]/nops(W)*convert([seq((IrredRep[i][j]^(-1))[1,l]*BigRep[j],j=1..nops(BigRep))],`+`))
   od;
  od;

  for i from 1 to nops(dd) do 
   ColSpace[i]:=ColumnSpace(PPP[i,1]); 
   for j from 1 to mm[i] do 
    SymVec[i,1,j]:=ColSpace[i][j]; 
    for l from 2 to dd[i] do 
     SymVec[i,l,j]:=PPP[i,l].SymVec[i,1,j] 
    od; 
   od; 
  od:
  
  T:=Matrix([seq(seq(seq(SymVec[i,l,j],l=1..dd[i]),j=1..mm[i]),i=1..nops(dd))]): 
  # blockdiagonalizes the matrices of the "big" representation, 
  # columns correspond to the irreducible representations as they occur in the isotypic components
  
  #Matrix([seq(seq(seq(SymVec[i,l,j],j=1..mm[i]),l=1..dd[i]),i=1..nops(dd))]): 
  # blockdiagonalizes equivariant matrices

  PolyBasis:=<map(weight->convert([seq(z[i]^weight[i],i=1..n)],`*`),L)>; 
  # basis of Laurent polynomials up to degree d

  output:=Transpose(T).PolyBasis;
  output:=map(s->s/subs([seq(z[i]=1,i=1..n)],convert(s,list)[1]),output);

  return [output,T,map(l->T^(-1).l.T,BigRepGenLinear(n,d))]; 
  # the coinvariant basis

end proc:



### For diagonal invariants (so far only G2)

EntryNameVecDiagonal:=proc(n,d,k) option remember;
 local i, L;
 L:=[seq(op(ChebyshevLevel('C',2*n,i)),i=0..d)];
 for i from 1 to nops(L) do
  if k=L[i] then
   return i
  fi;
 od;
end proc:

IrredRepGenDiagonal:=proc(n) option remember;
 local a; 
 a:=exp(2*Pi*I/6); 
  [[Matrix([[ 1]]),Matrix([[ 1]])],
   [Matrix([[ 1]]),Matrix([[-1]])],
   [Matrix([[-1]]),Matrix([[-1]])],
   [Matrix([[-1]]),Matrix([[ 1]])],
   [Matrix([[a,0],[0,1-a]]),Matrix([[0,1-a],[a,0]])],
   [Matrix([[a-1,0],[0,-a]]),Matrix([[0,-a],[a-1,0]])]]
end proc:

GroupStructureDiagonal:=proc(n,L) option remember;
  [L[1]^6,L[1]^5,L[1]^4,L[1]^3,L[1]^2,L[1],L[2].L[1]^6,L[2].L[1]^5,L[2].L[1]^4,L[2].L[1]^3,L[2].L[1]^2,L[2].L[1]]
end proc:

IrredRepDiagonal:=proc(n) option remember;
 local Irr, h, i;
 Irr:=IrredRepGenDiagonal(n);
 h:=nops(Irr);
 return [seq(GroupStructureDiagonal(n,Irr[i]),i=1..h)];
end proc:

IrredRepDimDiagonal:=proc(n) option remember;
 local s;
 map(s->ColumnDimension(s[1]),IrredRepGenDiagonal(n));
end proc:

CharTableDiagonal:=proc(n) option remember;
 local Irr, BigRep, h, g, i, j;
 Irr:=IrredRepGenDiagonal(n);
 h:=nops(Irr);
 g:=12;
 Transpose(Matrix(h,g,(i,j)->simplify(Trace(IrredRepDiagonal(n)[i][j]))));
end proc:

BigRepGenDiagonal:=proc(n,d) option remember; #ONLY FOR DIHEDRAL GROUP D6=G2 
 local a, i, j, k, l, listy, L, s, W; 
 a:=exp(2*Pi*I/6); 
 s:=[Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]),Matrix([[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]])]; 
 L:=[seq(op(ChebyshevLevel('C',2*n,i)),i=0..d)]; 
 listy:=[seq([seq([k,EntryNameVecDiagonal(n,d,convert(s[l].<L[k]>,list))],k=1..nops(L))],l=1..nops(s))]; 
 [seq(Transpose(map(expand,Matrix(nops(L),(i,j)->if `or`(seq(is([i,j]=listy[l][k]),k=1..nops(listy[l]))) then (a)^(L[i][1]+L[i][4])*(1-a)^(L[i][2]+L[i][3]) else 0 fi))),l=1..nops(s))]; 
end proc: 

IsotypicDecompositionMultiplicitiesDiagonal:=proc(n,d) option remember;
 local BigRep, BigChar, i;
 BigRep:=GroupStructureDiagonal(n,BigRepGenDiagonal(n,d)):
 BigChar:=Vector(nops(BigRep),i->Trace(BigRep[i])): 
 convert(LinearSolve(CharTableDiagonal(n),BigChar),list);
end proc:

IsotypicDecompositionBasisDiagonal:=proc(n,d) option remember;
 local s, i, j, h, l, L, BigRep, Irr, IrredRep, CharTable, BigChar, mm, dd, PPP , ColSpace, SymVec, T, PolyBasis, output;

 L:=[seq(op(ChebyshevLevel('C',2*n,i)),i=0..d)];

  BigRep:=GroupStructureDiagonal(n,BigRepGenDiagonal(n,d)):
 
  Irr:=IrredRepGenDiagonal(n);
  h:=nops(Irr);
  dd:=map(s->ColumnDimension(s[1]),IrredRepGenDiagonal(n)): #dimensions

  for i from 1 to h do
   IrredRep[i]:=GroupStructureDiagonal(n,Irr[i])
  od:
 
  CharTable:=Transpose(Matrix(h,nops(BigRep),(i,j)->Trace(IrredRep[i][j]))): #character table
  BigChar:=Vector(nops(BigRep),i->Trace(BigRep[i])): 
  mm:=convert(LinearSolve(CharTable,BigChar),list): #multiplicities
 
  for i from 1 to h do
   for l from 1 to dd[i] do
    PPP[i,l]:=simplify(dd[i]/nops(W)*convert([seq((IrredRep[i][j]^(-1))[1,l]*BigRep[j],j=1..nops(BigRep))],`+`))
   od;
  od;

  for i from 1 to nops(dd) do 
   ColSpace[i]:=ColumnSpace(PPP[i,1]); 
   for j from 1 to mm[i] do 
    SymVec[i,1,j]:=ColSpace[i][j]; 
    for l from 2 to dd[i] do 
     SymVec[i,l,j]:=PPP[i,l].SymVec[i,1,j] 
    od; 
   od; 
  od:
  
  T:=Matrix([seq(seq(seq(SymVec[i,l,j],l=1..dd[i]),j=1..mm[i]),i=1..nops(dd))]): 
  # blockdiagonalizes the matrices of the "big" representation, 
  # columns correspond to the irreducible representations as they occur in the isotypic components
  
  #Matrix([seq(seq(seq(SymVec[i,l,j],j=1..mm[i]),l=1..dd[i]),i=1..nops(dd))]): 
  # blockdiagonalizes equivariant matrices

  PolyBasis:=<map(weight->convert([seq(x[i]^weight[i],i=1..n)],`*`)*convert([seq(y[i]^weight[n+i],i=1..n)],`*`),L)>; 
  # basis of Laurent polynomials up to degree d

  output:=Transpose(T).PolyBasis;
  output:=map(s->s/subs([seq(x[i]=1,i=1..n),seq(y[i]=1,i=1..n)],convert(s,list)[1]),output);

  return [output,T,map(l->T^(-1).l.T,BigRepGenDiagonal(n,d))]; 
  # the coinvariant basis

end proc:

end module:


NULL;
