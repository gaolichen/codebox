(* ::Package:: *)

BeginPackage["CycNumber`"]

InitCnBase::usage = "Prepare independent basis of cyclomotic number.";
SimplifyCN::usage = "Simplify calculation result of cyclomotic number.";

(*
Examples:

(*parepare independent basis of 7-rank cyclomotic number.*)
InitCnBase[7];

(* two cyclomotic numbers. *)
cn1=1+4/5et^2+et^3;
cn2=4-et^3+3*et^5;

(* calculate cn1/cn2. *)
SimplifyCN[cn1/cn2,et,7]

*)


Begin["Private`"]

(* initialize the cyclic number base. *)
ClearAll[vars,eqs];
ClearAll[CnRelation,CnFreeVarNumber];
CnRelation[n_,m_]:={};
CnFreeVarNumber[n_]:=0;

ClearAll[InitCnBase];
InitCnBase[n_]:=Module[{i,j,vars={}, eqs={},count=0,res,exp,relation},
	For[i=1,i<= n,i++,
		AppendTo[vars,Unique["cnbase"]]
	];

	For[i=n-1,i>= 1,i--,
		If[Mod[n,i]==0,
			For[j=0,j<i,j++,
				If[j==0 && count>0,Continue[]];
				AppendTo[eqs, Sum[vars[[i*k+j+1]],{k,0,n/i-1}]];
				count++;
			];
		];
	];

	(*Print["eqs=",MatrixForm[eqs]];*)
	Quiet[res=Solve[eqs==0, Take[vars,-count]],{Solve::svars}];
	If[Length[res]!= 1,
		Print["Failed to initialize cnbase: ", Length[res]," solutions found."];
		Throw[$Failed];
	];

	res=First[res];
	(*Print["res=", res];*)

	For[i=n-count,i<n,i++,
		relation=ConstantArray[0,n-count];
		exp=vars[[i+1]]/.res;
		(*Print["exp=",exp];*)
		For[j=1,j<=n-count,j++,
			relation[[j]]=Coefficient[exp,vars[[j]]];
		];
		CnRelation[n, i]= relation;
	];

	CnFreeVarNumber[n]=n-count;
	Return[CnFreeVarNumber[n]];
];

ClearAll[CnToList];
CnToList[cn_, var_,n_]:=Module[{i, e,ret,freeVarN},
	freeVarN=CnFreeVarNumber[n];
	ret = ConstantArray[0,freeVarN];
	e=Exponent[cn,var];
	For[i=e,i>=1,i--,
		If[Mod[i,n]>= freeVarN,
			ret += Coefficient[cn, var^i]*CnRelation[n, Mod[i,n]],
			ret[[Mod[i,n]+1]] += Coefficient[cn, var^i]
		];
	];

	ret[[1]]+= cn/.{var->0};
	Return[ret];
];

ClearAll[ListToCn];
ListToCn[clist_, var_]:=clist.Table[var^i,{i,0,Length[clist]-1}]

ClearAll[CnTimes];
CnTimes[clist1_, clist2_,n_]:=Module[
	{ret,i,j,freeVarN},
	freeVarN=CnFreeVarNumber[n];
	Assert[freeVarN==Length[clist1]];
	Assert[freeVarN==Length[clist2]];

	ret = ConstantArray[0,freeVarN];
	For[i=1,i<= Length[clist1],i++,
		For[j=1,j<= Length[clist2], j++,
			If[Mod[i+j-2,n]>= freeVarN,
				ret += Simplify[clist1[[i]]*clist2[[j]]*CnRelation[n,Mod[i+j-2,n] ]],
				ret[[Mod[i+j-2,n]+1]]+= clist1[[i]]*clist2[[j]]
			];
		];
	];

	Return[ret];
];

ClearAll[InverseCn];
InverseCn[clist_,n_]:=Module[{ret,eqs,i,j,root,freeVarN},
	freeVarN=CnFreeVarNumber[n];
	Assert[freeVarN==Length[clist]];
	ret = {};
	For[i=1,i<= freeVarN,i++,
		AppendTo[ret, Unique["CnInv"]];
	];

	eqs=CnTimes[clist, ret,n];
	eqs[[1]]-= 1;
	(*Print["eqs=",MatrixForm[eqs]];*)
	Quiet[root=Solve[eqs==0, ret], {Solve::svars}];
	If[Length[root] != 1,
		Print["InverseCn: Failed to solve equations, root=", root];
		Throw[$Failed];
	];

	(*Print["root=",root,", inverseCn ",clist, "=",ret/.First[root]];*)
	Return[Simplify[ret/.First[root]]];
];

ClearAll[ReducePowerCN];
SetAttributes[ReducePowerCN,Listable]
ReducePowerCN[cn_,var_,n_]:=Module[{list},
	list=CnToList[cn,var,n];
	Return[ListToCn[list,var]]
];

(*ClearAll[EtaToTrig]
SetAttributes[EtaToTrig,Listable];
EtaToTrig[expr_, et_, n_]:=Module[{ret},
	ret = expr/.{et->Exp[I*2Pi/n]};
	Return[ExpToTrig[ret]]
];*)

ClearAll[EtaToTrig]
SetAttributes[EtaToTrig,Listable];
EtaToTrig[expr_, et_, n_]:=Module[{ret=expr,ci,si,i},
	For[i = Floor[n/2],i >= 1, i--,
		ci = Subscript[c,i];
		si = Subscript[s,i];
		ret = ret /.{et^(n-i) -> ci - I*si};
		ret = ret /. {et^i -> ci + I*si};
	];

	Return[Simplify[ret]]
];

ClearAll[SimplifyCN];
(*Options[SimplifyCN]=Join[Options[InverseCN],{}];*)
SetAttributes[SimplifyCN,Listable]
SimplifyCN[cn_,var_,n_]:=Module[{num,denor,ret},
	num = CnToList[Numerator[cn],var,n];
	denor = CnToList[Denominator[cn],var,n];
	(*Print["num=",num, ", denor=",denor,"; ",Denominator[cn]];*)
	ret = Simplify[CnTimes[num, InverseCn[denor,n],n]];
	Return[ListToCn[ret, var]];
];

ClearAll[FullSimplifyCoef];
FullSimplifyCoef[poly_,var_]:=Module[{ret=0,i,e},
	e=Exponent[poly,var];
	ret = FullSimplify[poly/.{var->0}];
	For[i=1,i<= e,i++,
		ret += FullSimplify[Coefficient[poly,var^i]]*var^i;
	];

	Return[ret];
];

ClearAll[FullSimplifyCoefMat];
FullSimplifyCoefMat[mat_,var_]:=Table[FullSimplifyCoef[mat[[i,j]],var], {i,1,Length[mat]},{j,1,Length[mat[[i]]]}];

ClearAll[GaussianElimination];
GaussianElimination[mat_List, var_Symbol, n_Integer]:=Module[{i,j,k,nmat,res={},inv},
	nmat=mat;
	Print["GaussianElimination a"];
	For[i=1,i<= Length[nmat],i++,
		For[j=1,j<= Length[nmat[[i]]],j++,
			If[nmat[[i,j]]===0, Continue[], Break[]];
		];
		If[j>Length[nmat[[i]]],Continue[]];

		inv=FullSimplify[SimplifyCN[1/nmat[[i,j]],var,n]];
		nmat[[i]]=FullSimplify[SimplifyCN[nmat[[i]]*inv,var,n]];
		AppendTo[res,nmat[[i]]];
		Print["i=",i, ", mat[[i]]=",nmat[[i]]];

		For[k=i+1,k<= Length[nmat],k++,
			If[nmat[[k,j]]===0, Continue[]];
			nmat[[k]]-= nmat[[k,j]]*nmat[[i]];
			nmat[[k]]=SimplifyCN[nmat[[k]],var,n]
		];
	];

	Print["res=",res];
	For[i=Length[res],i>=1,i--,
		For[j=1,j<= Length[res[[i]]],j++,
			If[res[[i,j]]===0, Continue[],Break[]];
		];

		inv = SimplifyCN[1/nmat[[i,j]],var,n];
		For[k=i-1,k>=1,k--,
			If[res[[k,j]]=== 0, Continue[]];
			res[[k]]-= res[[i]]*res[[k,j]]*inv;
			res[[k]]=SimplifyCN[res[[k]],var,n];
		];

		res[[i]]=SimplifyCN[res[[i]]*inv,var,n];
	];

	Print["res=",res];
];

Eps=10^-10;
ClearAll[IndependentRows]
Options[IndependentRows]={Var2N->{}};
IndependentRows[mat_List,opt:OptionsPattern[]]:=Module[{res={},tmp,pos,nmat,ii,i,j,k,rep,freep={},solvedp,cnt},
	nmat=Chop[N[mat/.OptionValue[Var2N]],Eps];
	pos=Table[i,{i,1,Length[mat]}];
	For[j=1,j<= Length[nmat[[1]]],j++,
		For[i=j-Length[freep],i<= Length[nmat],i++,
			If[nmat[[pos[[i]],j]]== 0, Continue[],Break[]];
		];

		If[i>Length[nmat], AppendTo[freep,j]; Continue[]];
		AppendTo[res,mat[[pos[[i]]]]];

		If[i>j-Length[freep],
			tmp=pos[[i]];
			pos[[i]]=pos[[j-Length[freep]]];
			pos[[j-Length[freep]]]=tmp;
		];

		i=pos[[j-Length[freep]]];
		For[k=j-Length[freep]+1,k<= Length[nmat],k++,
			If[nmat[[pos[[k]],j]]==0, Continue[]];
			nmat[[pos[[k]]]]-= nmat[[pos[[k]],j]]/nmat[[i,j]]*nmat[[i]];
			nmat[[pos[[k]]]]=Chop[nmat[[pos[[k]]]],Eps];
		];
	];

	Return[{res, freep}];
];

ClearAll[ToConjugateCN];
SetAttributes[ToConjugateCN,Listable]
ToConjugateCN[ex_,var_Symbol,n_Integer]:=Module[{ret,i},
	ret=ComplexExpand[Conjugate[ex]];
	Return[ret/.Table[var^i->var^(n-i),{i,1,n-1}]]
];

ClearAll[DotProdCN]
DotProdCN[v1_List,v2_List,var_Symbol,n_Integer]:=ToConjugateCN[v1, var, n].v2;

(* find orghogonal basis *)
ClearAll[GramSchmid];
GramSchmid[vList_List, var_Symbol, n_Integer]:=Module[{ret={},i,j,vvl,inv,dot},
	If[Length[vList]==1,Return[vList]];
	vvl=vList;
	For[i=1,i<= Length[vvl],i++,
		If[vvl[[i]]=== ConstantArray[0,Length[vvl[[i]]]], Continue[]];
		AppendTo[ret,vvl[[i]]];
		inv=FullSimplify[SimplifyCN[1/DotProdCN[vvl[[i]],vvl[[i]],var,n], var,n]];
		For[j=i+1,j<= Length[vvl],j++,
			vvl[[j]] = SimplifyCN[vvl[[j]]-DotProdCN[vvl[[i]],vvl[[j]],var,n]*inv*vvl[[i]],var,n];
		];
	];

	Return[ret]
];

ClearAll[Eigenvector4F7];
Options[Eigenvector4F7]={AutoPickVar->False};
Eigenvector4F7[mat_List,val_,var_Symbol,n_Integer,opt:OptionsPattern[]]:=Module[{dim, vec={},i,j,eqs,eqsmat,root,ret={},res,pos,vec1},
	dim = Length[mat];
	For[i=1,i<= dim, i++,
		AppendTo[vec, Unique["x"]];
	];

	eqsmat=IndependentRows[mat-val*IdentityMatrix[dim],Var2N->{var-> Exp[I*2*Pi/n]}];
	(*Print["eqsmat=",eqsmat[[1]]];*)
	eqs = eqsmat[[1]].vec;
	(*Print["eqs=",MatrixForm[eqs]];*)
	If[OptionValue[AutoPickVar],
		root = Solve[eqs==0,vec],
		pos = Table[{eqsmat[[2,i]]}, {i,1,Length[eqsmat[[2]]]}];
		root = Solve[eqs==0,Delete[vec,pos]];
	];

	(*Print["root=",root];*)
	res=vec/.root[[1]];
	For[i=1,i<= dim,i++,
		vec1= res/.{vec[[i]]->1};
		vec1=Simplify[vec1/.Table[vec[[j]]->0, {j,1,dim}]];
		If[vec1=== ConstantArray[0,dim], Continue[]];
		AppendTo[ret, vec1];
	];
	(*Print["ret=",ret];*)
	(*Print["ret=",Chop[N[ret/.{var\[Rule] Exp[I*2*Pi/n]}]]];*)
	ret = SimplifyCnMat[ret,var,n];
	(*Print["ret=",ret];*)
	Return[GramSchmid[ret,var,n]]
];

InverseEigenMat[mat_,var_,n_]:=Module[{i,ret},
	ret=ToConjugateCN[mat,var,n];
	For[i=1,i<= Length[ret], i++,
		ret[[i]]=ret[[i]]/DotProdCN[ret[[i]],ret[[i]],var,n];
		ret[[i]]=SimplifyCN[ret[[i]],var,n]
	];
	Return[Transpose[ret]]
];

(* diagonalize the given matrix. Return {left, right} where left.mat.right = diagonal matrix with varList as diagonal elements.*)
ClearAll[DiagonalizeMatrixCN];
Options[DiagonalizeMatrixCN]=Join[{PhaseSymbol-> ""},Options[Eigenvector4F7]];
DiagonalizeMatrixCN[mat_List,valList_List,var_Symbol, n_Integer,opts:OptionsPattern[]]:=Module[{len,left,right,ph,phlist,i},
	len = Length[mat];
	ph=OptionValue[PhaseSymbol];
	If[ph=="", 
		phlist=ConstantArray[1,len],
		phlist=Table[ToExpression[ph<>ToString[i]],{i,1,len}];
		phlist[[1]]=1;
	];

	right={};
	For[i=1,i<= Length[valList],i++,
		right = Join[right, Eigenvector4F7[mat, valList[[i]], var, n,FilterRules[{opts},Options[Eigenvector4F7]]]];
	];
	(*Print["right=",right];*)
	left = InverseEigenMat[right,var,n];
	(*Print["left=",left];*)
	left = Transpose[left];
	For[i=1,i<= len,i++,
		left[[i]]=left[[i]]/phlist[[i]];
		right[[i]]=right[[i]]*phlist[[i]];
	];

	right=Transpose[right];
	Return[{left,right}]
];

End[]

EndPackage[]
