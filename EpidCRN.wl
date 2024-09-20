(* ::Package:: *)

ClearAll["EpidCRN`*"];
BeginPackage["EpidCRN`"];
Global`ome;Global`u;Global`v;
Par::usage = "Par[dyn,var]";exp;
Cof::usage = "co=Cof[mat]";
ACM::usage = "A2=ACM[A,k]";
CompMat::usage = "A2m=CompMat[A,k]";
cons::usage = "con=cons[A,cp]";
Idx;IaHJF::usage = "{oU,taF}=Ia[vert,edg]";
SpeComInc::usage = "SpeComInc[comp,spec]";
expM;makeLPM;countMS;onlyP;
Hur3M::usage = "{co,h3,ine}=Hur3M[A]";
Hur4M::usage = "{co,h4,ine}=Hur4M[A]";Hur5M;
H4;
H6;

DFE::usage = "DFE[mod_,inf_]";
fix::usage = "fix[mod_,cn_:{}]";
fix2::usage = "fix2[mod_,plc_:{},cn_:{}]";
JTD::usage = "JTD[mod,cn_:{}]";
JTDP::usage = "JTDP[mod,\[Zeta]_:\[Zeta],cn_:{}]";
NGM::usage = "NGM[mod_,inf_], {M,V1,F1,F,V,K}"; 
NGM1::usage = "NGM[mod_,infc_], {M,V1,F1,F,V,K}"; 
elP::usage ="[mod_,inf_] ";
Res1F;Deg;
RUR::usage = "RUR[mod,ind,cn_:{}]";
GBH::usage = "GBH[pol_,var_,sc_,cn_:{}]";

Stodola;DerL;

mSim::usage = "mSim[mod,cN, cInit,T,excluded]";Bif1;

Sta::usage = "numeric";
Stab::usage = "Stab[mod_,cfp_,cn_:{}]";

JR0::usage = "JR0[mod,inf,u,cn_:{}],{chp,R0,K,jac,tr,det}";
JR02;
L1Planar::usage = "L1Planar[fg,eq:{}]";
DerEq::usage = "DerEq[fg,eq:{}]; eq is condition";
GetVec::usage = "GetVec[A,om],used in L13,L23";
L13;L23;(*DerSc::usage ="DerSc[f]";
RescaleODE::usage ="RescaleODE[f,equilcon];necessary
before calling DerSc ";*)

Begin["`Private`"];
exp:=Exponent[#,Variables[#]]&;
expM=Inner[OperatorApplied[Power],#2,#1,Times]&;
Par[RHS_,X_]:=Complement[Variables[RHS],X];
SpeComInc[comp_,spec_]:=Coefficient[#,spec]&/@comp;
(*creates the species-complex incidence matrix*)
countMS[m_]:=m//Together//(*put polynomials in standard form*)
NumeratorDenominator//(*get polys*)Map@CoefficientArrays//
(*get coefficients of polys*)
ReplaceAll[sa_SparseArray:>sa["NonzeroValues"]]//
(*get nonzero coeffs*)Flatten//(*preconditioner for AllTrue*)
Count[#, _?Negative] &;
onlyP[m_]:=m//Together//(*put polynomials in standard form*)
NumeratorDenominator//(*get polys*)Map@CoefficientArrays//
(*get coefficients of polys*)
ReplaceAll[sa_SparseArray:>sa["NonzeroValues"]]//
(*get nonzero coeffs*)Flatten//(*preconditioner for AllTrue*)
AllTrue[#,NonNegative]& (*has 0 if constant term is zero*);
   
Cof[A_?MatrixQ]:=Module[{x},
Drop[Reverse[CoefficientList[(-1)^(Length@A)
CharacteristicPolynomial[A,x],x]],1]];
ACM[matrix_,k_]:=
D[Minors[IdentityMatrix[Length@matrix]+t*matrix,k],t]/. t->0;
CompMat[A_?MatrixQ,k_Integer]:=
Module[{m,n,p,q},{m,n}=Dimensions[A];
p=Subsets[Range[1,m],{k}];
q=Subsets[Range[1,n],{k}];
Table[Det[A[[i,j]]],{i,p},{j,q}]];
(*A={{a11,a12,a13},{a21,a22,a23},{a31,a32,a33}};
CompMat[A,2]*)
makeLPM[mat_] := Table[Det@mat[[1 ;; i, 1 ;; i]], {i, 1, Length@mat}];
cons[mat_,cp_:{}] := Module[{X, sol, dim, cv}, 
(*Parametrize the kernel to the left , using only pos
pars*)
X = Array[x, Length[mat]];
  sol = SolveValues[Join[Thread[X . mat == 0],cp], X, NonNegativeIntegers];
(*particularize  the Mathematica constants C[i] determining
a point in the conservations cone, by choosing exactly one
parameter to be one, and the rest to be 0*)
  dim = NullSpace[mat // Transpose] // Length;
  cv = Table[C[i], {i, dim}];
  Flatten /@ 
   Table[sol /. Thread[cv -> IdentityMatrix[dim][[i]]], {i, dim}]];

Idx[set_,n_PositiveInteger]:=Module[{seq},
seq=(Table[Count[set,i],{i,n}]/.List->Sequence);seq];

IaHJF[vert_,edg_]:=Module[{gg,oU,taF},gg[a_,b_]:=
Which[a===b[[1]],-1,a===b[[2]],1,True,0];
oU=Outer[gg,vert,edg];
taF=TableForm[oU,TableHeadings->{vert,edg},
TableAlignments->{Right,Top}];
{oU,taF}
];


 Hur3M[A_]:=Module[{co,h3,ine,\[Omega]},
co=CoefficientList[(-1)^Length[A] CharacteristicPolynomial[A,\[Omega]],\[Omega]];
h3=co[[ 2]]* co[[ 3]]-co[[ 1]] *co[[ 4]];ine={co[[ 1]]>0,co[[ 2]]>0};
{co,h3,ine}];
(*A={{-j[1]-j[3]+j[4],j[4],j[3]},{-2 j[4],-j[2]-j[4],0},{j[3],0,-j[3]}};
Hur3M[A]*)

Hur4M[mat_]:=Module[{lm,ch,cot,co,H4,h4,ine},
lm=mat//Length;
ch=((-1)^lm * CharacteristicPolynomial[mat,\[Lambda]]//Factor);
cot=CoefficientList[ch,\[Lambda]];
co=Reverse[Drop[cot,-1]];(*co[[0]]=1 is lead coef*)
H4={{co[[1]],1,0,0},
{co[[3]],co[[2]],co[[1]],1},
{0,co[[4]],co[[3]],co[[2]]},
{0,0,0,co[[4]]}};h4=Det[H4];
ine=Thread[co>0];{co,h4,ine}];

H4[co_]:={{co[[1]],1,0,0},
{co[[3]],co[[2]],co[[1]],1},
{0,co[[4]],co[[3]],co[[2]]},
{0,0,0,co[[4]]}};

Hur5M[jac_]:=Module[{lm,ch,cot,co,H5,h5,ine},
lm=jac//Length;
ch=((-1)^lm * CharacteristicPolynomial[jac,\[Lambda]]//Factor);
cot=CoefficientList[ch,\[Lambda]];
co=Reverse[Drop[cot,-1]];
H5={{co[[1]],1,0,0,0},{co[[3]],co[[2]],co[[1]],1,0},
{co[[5]],co[[4]],co[[3]],co[[2]],co[[1]]},
{0,0,co[[5]],co[[4]],co[[3]]},
{0,0,0,0,co[[5]]}};h5=Det[H5];
ine=Append[Thread[co>0],co[[1]] co[[2]]>co[[3]]];{co,h5,ine,H5}];
(*
H5[co_]:=Module[{hm},hm={{co[[1]],1,0,0,0},
{co[[3]],co[[2]],co[[1]],1,0},
{co[[5]],co[[4]],co[[3]],co[[2]],co[[1]]},
{0,0,co[[5]],co[[4]],co[[3]]},
{0,0,0,0,co[[5]]}}];*)

H6[co_]:=Module[{hm},hm={{co[[1]],1,0,0,0,0},
{co[[3]],co[[2]],co[[1]],1,0,0},
{co[[5]],co[[4]],co[[3]],co[[2]],co[[1]],1},
{0,co[[6]],co[[5]],co[[4]],co[[3]],co[[2]]},
{0,0,0,co[[6]],co[[5]],co[[4]]},
{0,0,0,0,0,co[[6]]}}];

JTD[mod_,cn_:{}]:=
Module[{dyn,X,jac,tr,det},dyn=mod[[1]];X=mod[[2]];
jac=Grad[dyn,X]/.cn;
tr=Tr[jac];
det=Det[jac];
{jac,tr,det}];
JTDP[mod_,\[Zeta]_:\[Zeta],cn_:{}]:=
Module[{dyn,X,jac,tr,det,chp,cof},dyn=mod[[1]];X=mod[[2]];
jac=Grad[dyn,X]/.cn;
tr=Tr[jac];
det=Det[jac];
chp=CharacteristicPolynomial[jac,\[Zeta]];cof=CoefficientList[chp,\[Zeta]];
{jac,tr,det,cof,chp}];
(*Collect[JTDP[SIRG,x][[4]],x]
JTDP[SIRG][[1]]//MatrixForm*)
Res1F[mod_,csr_,pol_,in_,cn_:{}]:=
Module[{jac,det,res,chp,cof},
jac=JTDP[mod][[1]]/.csr/.cn;
det=Numerator[Together[Det[jac]]];
res=Resultant[det,pol,in]//Factor
];

DFE[mod_,inf_:{},cn_:{}]:=Module[{dyn,X},
    dyn=mod[[1]]/.cn;X=mod[[2]];
    Quiet[Solve[Thread[dyn==0]/.Thread[X[[inf]]->0],X]]];

fix[mod_,cn_:{}]:=Module[{dyn,X,fp,Xp},(*mostly numerical*)
   dyn=mod[[1]]//.cn;X=mod[[2]];
   fp=X/.Quiet[Solve[Thread[(dyn)==0],X]];
   If[cn!={},Xp=Cases[_?(AllTrue[NonNegative]@#&)]@fp;
   fp=SortBy[Xp,{ #[[1]]&,#[[2]]&}]];fp];
   
fix2[mod_,cn_:{},plc_:{}]:=Module[{dyn,X,pl,fp,Xp,Xs,sp,Gp,xM,yM,
   r1,r2},
   dyn=mod[[1]]//.cn;X=mod[[2]];pl=Complement[Range[Length[X]],plc];
   fp=X/.Quiet[NSolve[Thread[(dyn)==0],X]];
   Xp=Cases[_?(AllTrue[NonNegative]@#&)]@fp;
   xM=Max/@Transpose[Xp];
   Xs=SortBy[Xp,{ #[[1]]&,#[[2]]&}];
   r1={X[[pl[[1]]]],0,xM[[pl[[1]]]]+.5};
   r2={X[[pl[[2]]]],0,xM[[pl[[2]]]]+.5};
   sp=StreamDensityPlot[{dyn[[pl[[1]]]],dyn[[pl[[2]]]]},r1,r2,
   ColorFunction->"Pastel",
   Frame->True,
   FrameLabel->{"x[t]","y[t]"},
   PlotLabel->Style["Phase portrait",Large],LabelStyle->18];
   Gp=Graphics[{PointSize[0.03],{Red,Black,Cyan},Point[Xp]}];
   cP=ContourPlot[{dyn[[1]],dyn[[2]]},r1,r2,
   FrameLabel->{"x[t]","y[t]"},ContourStyle->{Red,Cyan},
   LabelStyle->Directive[Black,Medium]];
   {Xs,sp,Gp,cP}
   ]
NGM[mod_,inf_:{}]:=Module[{dyn,X,infc,M,V,F,F1,V1,K,cz},
   dyn=mod[[1]];X=mod[[2]];
   infc=Complement[Range[Length[X]],inf];
   M=Grad[dyn[[inf]],X[[inf]]];
   (*The jacobian of the infectious equations*)
   V1=-M/.Thread[X[[infc]]->0];
   (*V1 is a first guess for V, retains all gradient terms which
   disappear when the non infectious components are null*)
   cz=Thread[X[[inf]]->0];
   F1=M+V1/.cz;
   (*F1 is a first guess for F, containing all other 
   gradient terms*)
   F=Replace[F1, _. _?Negative -> 0, {2}];
   (*all terms in F1 containing minuses are set to 0*);
   V=F-M;
   K=(F . Inverse[V])/.Thread[X[[inf]]->0]//FullSimplify;
 {M,V1,F1,F,V,K}]
 NGM1[mod_,infc_:{}]:=Module[{dyn,X,inf,M,V,F,F1,V1,K,cz},
   dyn=mod[[1]];X=mod[[2]];
   inf=Complement[Range[Length[X]],infc];
   M=Grad[dyn[[inf]],X[[inf]]]
   (*The jacobian of the infectious equations*);
   V1=-M/.Thread[X[[infc]]->0]
   (*V1 is a first guess for V, retains all gradient terms which
   disappear when the non infectious components are null*);
   cz=Thread[X[[inf]]->0];
   F1=M+(V1/.cz)
   (*F1 is a first guess for F, 
   containing all other gradient terms*);
   F=Replace[F1, _. _?Negative -> 0, {2}];
   (*all terms in F1 containing minuses are set to 0*);
   V=F-M;
   K=(F . Inverse[V]);
  K1=(F1 . Inverse[V1]);
 {M,V1,F1,F,V,K}]
 (*K=NGM[SEIR,Range[2]][[4]];eig=Eigenvalues[K]/.Thread[X[[inf]]->0];*) 
   
elP[mod_,inf_]:=Module[{X,Xi,qv,ov,ngm,fv,eq},X=mod[[2]];Xi=X[[inf]];
 qv=Array[q,Length[Xi]];
 ov=Table[1,{j,Length[Xi]}];ngm=NGM[mod,inf];F=ngm[[4]];V=ngm[[5]];fv=ov . F;
 eq=(qv . F)*qv-qv*fv+(ov-qv) . V];

RUR[mod_, ind_, cn_ : {}] (*ind is a list*):= 
Module[{RHS, var, par, elim,ratsub,pol,polc,rat1},
       RHS = mod[[1]]/.cn; var = mod[[2]]; par = mod[[3]]; 
       elim = Complement[Range[Length[var]], ind];
       ratsub = Solve[Delete[Thread[RHS == 0], List /@ind], 
       var[[elim]]];
       pol = GroebnerBasis[Numerator[Together[RHS//.ratsub]], 
         Join[par, var[[ind]]], var[[elim]],
         MonomialOrder->EliminationOrder]; 
       rat1=Append[(ratsub/.var[[ind]]->1),var[[ind]]->1];
    {ratsub, pol,rat1}
      ]
      
GBH[pol_,var_,sc_,cn_:{}]:=Module[{li,pa},
li={pol,sc};pa=Complement[Variables[li],{var}];
GroebnerBasis[{Numerator[Together[pol]],
Numerator[Together[sc]]}/.cn,pa,{var},
MonomialOrder->EliminationOrder]];
Stodola[pol_,var_] :=Equal@@Sign[CoefficientList[pol,var]]



mSim[mod_,cN_, cInit_,T_:100,exc_:{}]:=
Module[{dyn, X,vart,diff,diffN,initcond,eqN,ndesoln,ind}, 
dyn=mod[[1]];X=mod[[2]];vart=Through[X[t]];
diff= D[vart,t] \[Minus] (dyn/.Thread[X->vart]);
diffN=diff//.cN;
initcond = (vart/.t->0)- cInit;
eqN=Thread[Flatten[{diffN, initcond}] == 0];
ndesoln = Chop[NDSolveValue[eqN,vart,{t, 0, T}]];
ind=Complement[Range[Length[X]],exc];
pl=Plot[ndesoln[[ind]],{t,0,T},AxesLabel->{"t"," "}];pl];

 Bif1[mod_,cN_,indX_,bifv_,pl0_:0,pL_:10,y0_:-1, yM_:10,cH_,cca_,ccb_:{}]:=
Module[{dyn, X,fp,pl,epi,plf,lin1,lin1c,lin2,lin2c},dyn=mod[[1]]/.cN;X=mod[[2]];
fp=Quiet[Solve[Thread[(dyn)==0],X]//N];
lin1=Line[{{ cca,0},{ cca,10}}];
lin1c=Graphics[{Thick,Black,Dotted,lin1}];
lin2=Line[{{ ccb,0},{ ccb,10}}];
lin2c=Graphics[{Thick,Black,Dotted,lin2}];
epi={Text["\!\(\*SubscriptBox[\(c\), \(H\)]\)",Offset[{10,10},{ cH,0}]],
{PointSize[Large],Style[Point[{ cH,0}],Purple]},Text["\!\(\*SubscriptBox[\(c\), \(1  c\)]\)",Offset[{-10,10},{ cca,0}]],
{PointSize[Large],Style[Point[{ cca,0}],Cyan]},Text["\!\(\*SubscriptBox[\(c\), \(2  c\)]\)",Offset[{10,10},{ ccb,0}]],
{PointSize[Large],Style[Point[{ ccb,0}],Black]}};
pl=Plot[Evaluate@(X[[indX]]/.fp),{bifv,pl0,pL}, 
PlotStyle->{Blue,Green,Red,Green}];
plf=Show[{pl,lin1c,lin2c},Epilog->epi,PlotRange->{{pl0,pL},{y0,yM}},AxesLabel->{bifv,X[[indX]]}];
{fp,plf}];

Stab[mod_,cfp_,cn_:{}]:=Module[{dyn,X,par,jac,jacfp,eig},
 dyn=mod[[1]];X=mod[[2]];par=mod[[3]];
 jac=Grad[dyn,X];
 jacfp=jac//.cfp;
 eig=Eigenvalues[jacfp/.cn]
]
(*Stab[SEIR,cfp[[1]]]//FullSimplify*)

Sta[jac_,X_,Xv_]:=Map[Max[Re[Eigenvalues[jac/.Thread[X->#]]]]&,Xv];

JR0[mod_,inf_,u_,cn_:{}]:=
  Module[{dyn,X,par,cinf,cp,cdfe,cX,jac,tr,det,chp,ngm,K,R0},
    dyn=mod[[1]];X=mod[[2]];par=mod[[3]];
   (* Print[" dyn=",dyn//FullSimplify//MatrixForm,X,par];*)
    cinf=Thread[X[[inf]]->0];
    cp=Thread[par>0];cX=Thread[X>0];
    cdfe=Join[DFE[mod,inf],cinf];
    jac=Grad[dyn,X]/.cinf/.cn;
    tr=Tr[jac];
    det=Det[jac];
    chp=CharacteristicPolynomial[jac,u];
    ngm=NGM[mod,inf];
    K=ngm[[6]];
   (*Print["K=",K//MatrixForm];*)
   R0=Assuming[Join[cp,cX],Eigenvalues[K]//FullSimplify];
  {chp,R0,K,jac,tr,det}];
(*Collect[JR0[SIRG,x][[4]],x]
JR0[SIRG][[1]]//MatrixForm*)
JR02[pol_,u_]:=Module[{co,co1,cop,con,R0J},co=CoefficientList[pol,u];
  Print["the  factor  has degree ",Length[co]-1];
  Print["its leading  coefficient  is ",co[[Length[co]]]];
  co1=Expand[co[[1]] ];
  Print["its  constant coefficient  is ",co1];
  cop=Replace[co1, _. _?Negative -> 0, {1}](*level 1 here ?*);
  con=cop-co1;
  Print["R0J is"];
  R0J=con/cop//FullSimplify;
{R0J,co}
]



(*The first focal value for the differential equation
Overscript[x, .]\[LongEqual]-\[Omega]y+Underscript[\[Sum], i+j\[GreaterEqual]2]Subscript[F, ij]/(i!j!)x^iy^j, Overscript[y, .]\[LongEqual]\[Omega]x+Underscript[\[Sum], i+j\[GreaterEqual]2]Subscript[G, ij]/(i!j!)x^iy^j is 
Subscript[L, 1]\[LongEqual]Subscript[F, 30]+Subscript[F, 12]+Subscript[G, 03]+Subscript[G, 21]+1/\[Omega][Subscript[F, 11](Subscript[F, 20]+Subscript[F, 02])-Subscript[G, 11](Subscript[G, 20]+Subscript[G, 02])+Subscript[F, 02]Subscript[G, 02]-Subscript[F, 20]Subscript[G, 20]]*)
L1Planar[fg_,var_,equilcon_:{}]:=
Module[{J,xyshift,Tm,Tinvuv,FG,derivatives,a,b,i,j,L1,x,y,F,G,normForm},
(*Variables*){x,y}=var;
(*Jacobian at equilibrium*)
J=Simplify[D[fg,{var}]/. equilcon];
(*Shift variables to equilibrium*)
xyshift={x->x+(x/. equilcon),y->y+(y/. equilcon)};
(*Transformation matrix*)
Tm={{1,0},{-a/Global`ome,-b/Global`ome}};
Tinvuv=Inverse[Tm] . {Global`u,Global`v};
(*Transformed FG*)
FG=(Tm . fg/. xyshift)/. {x->Tinvuv[[1]],y->Tinvuv[[2]]}/. {a->J[[1,1]],b->J[[1,2]]};
(*Compute derivatives*)
derivatives={};
For[i=0,i<=3,i++,For[j=0,j<=3-i,j++,derivatives=Join[derivatives,{Subscript[F,i,j]->(D[FG[[1]],{Global`u,i},{Global`v,j}]/. {Global`u->0,Global`v->0}),Subscript[G,i,j]->(D[FG[[2]],{Global`u,i},{Global`v,j}]/. {Global`u->0,Global`v->0})}]]];
(*Compute L1 coefficient*)
L1=Subscript[F,3,0]+Subscript[F,1,2]+Subscript[G,0,3]+Subscript[G,2,1]+1/Global`ome*(Subscript[F,1,1]*(Subscript[F,2,0]+Subscript[F,0,2])-Subscript[G,1,1]*(Subscript[G,2,0]+Subscript[G,0,2])+Subscript[F,0,2]*Subscript[G,0,2]-Subscript[F,2,0]*Subscript[G,2,0]);
(*Substitute derivatives into L1*)
L1=L1/. derivatives;
(*Construct the normal form up to cubic terms*)
F1=Sum[Subscript[F,i,j] Global`u^i Global`v^j,{i,0,3},{j,0,3-i}];
G1=Sum[Subscript[G,i,j] Global`u^i Global`v^j,{i,0,3},{j,0,3-i}];
normForm={F1,G1}/. derivatives;
(*Return L1 coefficient and normal form*)
{L1,FG,normForm}
];


DerEq[f_,var_,equilcon_]:=Module[
{derivatives,order,deriv,i,j,k,A,B,CC,DD,EE,x,y,z,par,cp},
n=Length[f];
A=D[f,{var}]/.equilcon;
{x,y,z}=var;par=Par[f,var];cp=Thread[par>0];
derivatives={};
order=2;
For[i=0,i<=order,i++,For[j=0,j<=order-i,j++,For[k=0,k<=order-i-j,k++,
deriv=Simplify[D[f,{x,i},{y,j},{z,k}]/.equilcon];
derivatives=Join[derivatives,Simplify[{Subscript[F, i,j,k]->deriv[[1]],Subscript[G, i,j,k]->deriv[[2]],Subscript[H, i,j,k]->deriv[[3]]}]];
]]];
B[x_,y_]:=Sum[{Subscript[F, Idx[{k,l},n]],Subscript[G, Idx[{k,l},n]],Subscript[H, Idx[{k,l},n]]}x[[k]]y[[l]]/.derivatives,{k,n},{l,n}];
(*CC[x_,y_,z_]:=Sum[{Subscript[F, Idx[{k,l,m},n]],Subscript[G, Idx[{k,l,m},n]],Subscript[H, Idx[{k,l,m},n]]}x[[k]]y[[l]]z[[m]]/.derivatives,{k,n},{l,n},{m,n}];*)
(* because of the bimolecularity, all derivatives of order 3 and higher vanish *)
CC[x_,y_,z_]:={0,0,0};
DD[x_,y_,z_,s_]:={0,0,0};
EE[x_,y_,z_,s_,t_]:={0,0,0};
(* the reason for the double symbols CC, DD, EE is that C, D, E are protected in Mathematica *)
{A,B,CC(*,DD,EE*)}
];


GetVec[A_,om_]:=Module[{n,mtx,pconj,q,qconj,normalize},
n=Length[A];
mtx=A-om I IdentityMatrix[n];
q=NullSpace[mtx[[Range[1,n-1]]]][[1]];
(* Notice that q is not normalised. The normalisation has relevance only when the second focal value is computed for parameter values, where the first focal value does not vanish. *)
mtx=A\[Transpose]-om I IdentityMatrix[n];
pconj=NullSpace[mtx[[Range[1,n-1]]]][[1]];
normalize=FullSimplify[pconj . q];
pconj=pconj/normalize;
qconj=FullSimplify[ComplexExpand[q\[Conjugate]]];
{pconj,q,qconj}
];


L13[A_,B_,CC_,cp_]:=
Module[{n,pconj,q,qconj,v1,v2,v3,c1,numer,denom,a,b,c,d,L1\[Kappa]\[Omega]},
n=Length[A];
{pconj,q,qconj}= GetVec[A,ome];
v1=CC[q,q,qconj];
v2=B[q,Inverse[-A] . B[q,qconj]];
v3=B[qconj,Inverse[2I ome IdentityMatrix[n]-A] . B[q,q]];
c1=pconj . (1/2 v1+v2+1/2 v3);
(* We take the real part in a bit complicated way: 
Re (a+b\[ImaginaryI])/(c+d\[ImaginaryI])=((ac+bd)/(c^2+d^2)).
It seems to be faster than the standard solution would be. *)
numer=Numerator[c1];
denom=Denominator[c1];
a=Simplify[ComplexExpand[Re[numer]],cp];
b=Simplify[ComplexExpand[Im[numer]],cp];
c=Simplify[ComplexExpand[Re[denom]],cp];
d=Simplify[ComplexExpand[Im[denom]],cp];
L1\[Kappa]\[Omega]=Simplify[(a c+b d)/(c^2+d^2)]];


L23[A_,B_,CC_:{0,0,0},DD_:{0,0,0},EE_:{0,0,0}]:=
Module[{n,Id,omega,invA,inv2,inv3,pconj,q,qconj,h,prec,c,invbig},
n=Length[A];
Id=IdentityMatrix[n];
omega=Sqrt[Det[A]/Tr[A]];
invA=Inverse[A];
inv2=Simplify[Inverse[2 omega I Id-A]];
inv3=Simplify[Inverse[3 omega I Id-A]];
{pconj,q,qconj}= GetVec[A,omega];
q=FullSimplify[q/. {\[Omega]->omega}];
pconj=FullSimplify[pconj/. {\[Omega]->omega}];
Subscript[h, 2,0]=FullSimplify[inv2 . B[q,q]];
Subscript[h, 1,1]=FullSimplify[-invA . B[q,q\[Conjugate]]];
prec=FullSimplify[CC[q,q,q\[Conjugate]]+2 B[q,Subscript[h, 1,1]]+B[q\[Conjugate],Subscript[h, 2,0]]];
Subscript[c, 1]=FullSimplify[1/2 (pconj . prec)];
invbig=FullSimplify[Inverse[Join[Join[omega I Id-A,{q}\[Transpose],2],{Join[pconj,{0}]}]]];
Subscript[h, 2,1]=FullSimplify[invbig . Join[FullSimplify[prec-2 Subscript[c, 1] q],{0}]][[1;;n]];
Subscript[h, 3,0]=FullSimplify[inv3 . (CC[q,q,q]+3 B[q,Subscript[h, 2,0]])];
Subscript[h, 3,1]=FullSimplify[inv2 . (DD[q,q,q,q\[Conjugate]]+3 CC[q,q,Subscript[h, 1,1]]+3 CC[q,q\[Conjugate],Subscript[h, 2,0]]+3 B[Subscript[h, 2,0],Subscript[h, 1,1]]+B[q\[Conjugate],Subscript[h, 3,0]]+3 B[q,Subscript[h, 2,1]]-6 Subscript[c, 1] Subscript[h, 2,0])];
Subscript[h, 2,2]=FullSimplify[-invA . (DD[q,q,q\[Conjugate],q\[Conjugate]]+4 CC[q,q\[Conjugate],Subscript[h, 1,1]]+CC[q\[Conjugate],q\[Conjugate],Subscript[h, 2,0]]+CC[q,q,Subscript[h, 2,0]\[Conjugate]]+2 B[Subscript[h, 1,1],Subscript[h, 1,1]]+2 B[q,Subscript[h, 2,1]\[Conjugate]]+2 B[q\[Conjugate],Subscript[h, 2,1]]+B[Subscript[h, 2,0]\[Conjugate],Subscript[h, 2,0]])];
Subscript[c, 2]=FullSimplify[1/12 (pconj . (EE[q,q,q,q\[Conjugate],q\[Conjugate]]+DD[q,q,q,Subscript[h, 2,0]\[Conjugate]]+3 DD[q,q\[Conjugate],q\[Conjugate],Subscript[h, 2,0]]+6 DD[q,q,q\[Conjugate],Subscript[h, 1,1]]+CC[q\[Conjugate],q\[Conjugate],Subscript[h, 3,0]]+3 CC[q,q,Subscript[h, 2,1]\[Conjugate]]+6 CC[q,q\[Conjugate],Subscript[h, 2,1]]+3 CC[q,Subscript[h, 2,0]\[Conjugate],Subscript[h, 2,0]]+6 CC[q,Subscript[h, 1,1],Subscript[h, 1,1]]+6 CC[q\[Conjugate],Subscript[h, 2,0],Subscript[h, 1,1]]+2 B[q\[Conjugate],Subscript[h, 3,1]]+3 B[q,Subscript[h, 2,2]]+B[Subscript[h, 2,0]\[Conjugate],Subscript[h, 3,0]]+3 B[Subscript[h, 2,1]\[Conjugate],Subscript[h, 2,0]]+6 B[Subscript[h, 1,1],Subscript[h, 2,1]]))];
ComplexExpand[Re[Subscript[c, 2]]]
];


(*RescaleODE[f_,equilcon_]:=Module[{X,Y,Z,fscaled,f\[Kappa]1,fnew,
\[Alpha]\[Beta]\[Gamma],A,i,factor,\[Kappa]2\[Alpha]\[Beta]\[Gamma]},
X=x/.equilcon;
Y=y/.equilcon;
Z=z/.equilcon;
fscaled=Simplify[DiagonalMatrix[{1/X,1/Y,1/Z}] . (f/.{x->u X,y->v Y,z->w Z}),\[Kappa]positive];
fnew=fscaled/.{Subscript[\[Kappa], 1]->1,Subscript[\[Kappa], 2]->1,Subscript[\[Kappa], 3]->1,Subscript[\[Kappa], 4]->1};
\[Alpha]\[Beta]\[Gamma]=Simplify[fscaled/fnew,\[Kappa]positive];
(* now we hide in \[Alpha],\[Beta],\[Gamma] all the common factors *)
A=D[fnew,{{u,v,w}}]/.{u->1,v->1,w->1};
For[i=1,i<=Length[A],i++,{
factor=LCM[Denominator[A[[i]]/Max[Abs[A[[i]]]]]/.List->Sequence]/Max[Abs[A[[i]]]];
fnew[[i]]=fnew[[i]]factor;
\[Alpha]\[Beta]\[Gamma][[i]]=\[Alpha]\[Beta]\[Gamma][[i]]/factor;
}];
fnew=DiagonalMatrix[{\[Alpha],\[Beta],\[Gamma]}] . fnew;
\[Kappa]2\[Alpha]\[Beta]\[Gamma]={\[Alpha]->\[Alpha]\[Beta]\[Gamma][[1]],\[Beta]->\[Alpha]\[Beta]\[Gamma][[2]],\[Gamma]->\[Alpha]\[Beta]\[Gamma][[3]]};
{fnew,\[Kappa]2\[Alpha]\[Beta]\[Gamma]}
];
DerSc[f_]:=Module[{equil,derivatives,order,deriv,i,j,k,A,B,CC,DD,EE},
(*Assumes {u->1,v->1,w->1}*)
n=Length[f];
equil={u->1,v->1,w->1};
A=D[f,{{u,v,w}}]/.equil;
derivatives={};
order=2;
For[i=0,i<=order,i++,For[j=0,j<=order-i,j++,For[k=0,k<=order-i-j,k++,
deriv=Simplify[D[f,{u,i},{v,j},{w,k}]/.equil];
derivatives=Join[derivatives,Simplify[{Subscript[F, i,j,k]->deriv[[1]],Subscript[G, i,j,k]->deriv[[2]],Subscript[H, i,j,k]->deriv[[3]]}]];
]]];
B[x_,y_]:=Sum[{Subscript[F, Idx[{k,l},n]],Subscript[G, Idx[{k,l},n]],Subscript[H, Idx[{k,l},n]]}x[[k]]y[[l]]/.derivatives,{k,n},{l,n}];
(*CC[x_,y_,z_]:=Sum[{Subscript[F, Idx[{k,l,m},n]],Subscript[G, Idx[{k,l,m},n]],Subscript[H, Idx[{k,l,m},n]]}x[[k]]y[[l]]z[[m]]/.derivatives,{k,n},{l,n},{m,n}];*)
(* because of the bimolecularity, all derivatives of order 3 and higher vanish *)
CC[x_,y_,z_]:={0,0,0};
DD[x_,y_,z_,s_]:={0,0,0};
EE[x_,y_,z_,s_,t_]:={0,0,0};
(* the reason for the double symbols CC, DD, EE is that C, D, E are protected in Mathematica *)
{A,B,CC,DD,EE}
];
*)
End[];


EndPackage[];


$ContextPath=DeleteDuplicates[Append[$ContextPath,"model`Private`"]];
