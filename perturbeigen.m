(* ::Package:: *)

ClearAll[GlobalFlags];
GlobalFlags["Debug"]=False;

ClearAll[DebugInfo,DebugOn,DebugOff,IsDebugOn]
DebugOn[]:=GlobalFlags["Debug"]=True;
DebugOff[]:=GlobalFlags["Debug"]=False;
IsDebugOn[]:=GlobalFlags["Debug"];
DebugInfo[x__]:=If[IsDebugOn[],Print[x]];

ClearAll[ExtractMatrix];
Options[ExtractMatrix]={Symmetric->False};
ExtractMatrix[poly_,x_,y_,opts:OptionsPattern[]]:=Module[{i,j,ret,arr,isSym},
	ret={};
	isSym=OptionValue[Symmetric];
	For[i=1,i<= Length[x],i++,
		arr={};
		For[j=1,j<= Length[y],j++,
			If[isSym && i!=j,
				AppendTo[arr,Coefficient[poly,x[[i]]*y[[j]]]/2],
				AppendTo[arr,Coefficient[poly,x[[i]]*y[[j]]]]
			];
		];
		AppendTo[ret,arr];
	];

	Return[ret]
];

ExtractMatrix[poly_,x_]:=ExtractMatrix[poly,x,x,Symmetric->True];

ClearAll[FindEigenvalues,EigenvaluesEx,LeadingTerm]

LeadingTerm[poly_,var_]:=Module[{ret,list,term,i},
	list=MonomialList[poly,var];
	For[i=Length[list],i>0,i--,
		term=Simplify[list[[i]]];
		If[SameQ[term,0]==False,Return[term]];
	];

	Return[0];
];

Options[FindEigenvalues]={Numerical-> False};
FindEigenvalues[mat_,var_,cur_,pow_,order_,opts:OptionsPattern[]]:= 
Module[{det,term=0,roots,res={},i,val,w,isNum},
	If[pow>order,Return[{cur}]];
	isNum=OptionValue[Numerical];

	det=Det[mat-(cur+w*var^pow)*IdentityMatrix[Length[mat]]];
	If[isNum,det=Chop[Simplify[N[det]]]];
	term=LeadingTerm[det,var];
	If[SameQ[term,0],Print["Unexpacted case. "];Return[cur]];

	If[isNum,roots=Chop[NSolve[term==0,w]],roots=Simplify[Solve[term==0,w]]];

	If[pow<order,roots=DeleteDuplicates[roots]];
	For[i=1,i<= Length[roots],i++,
		val=w/.roots[[i]];
		res=Join[res,FindEigenvalues[mat,var,cur+val*var^pow,pow+1,order,opts]]
	];

	Return[res]
];

ClearAll[FindEigenvalue];
FindEigenvalue[mat_,var_,cur_,pow_,opts:OptionsPattern[]]:=Module[{},
	Return[FindEigenvalues[mat, var, cur, pow, pow, opts]]
];

EigenvaluesEx[mat_,var_,order_,opts:OptionsPattern[]]:=Module[{},
	Return[FindEigenvalues[mat,var,0,0,order,opts]]
];

GenCMat[dim_,order_,pre_]:=Module[{i,j,ret={},row},
	For[i=1,i<= dim,i++,
		For[j=0;row={},j<= order,j++,
			AppendTo[row,ToExpression[pre<>ToString[j*(dim+order+1)+i]]]
		];
		AppendTo[ret,row]
	];

	Return[ret]
];

ClearAll[TruncatePoly,TruncateArray,TruncateMatrix];
Options[TruncatePoly]={KeepLeadingOrder->False};
TruncatePoly[poly_,var_,maxo_,opts:OptionsPattern[]]:=Module[{i,ret=0,npoly},
	npoly=Apart[poly,var];
	For[i=0,i<= maxo,i++,
		ret+=Simplify[Coefficient[npoly,var,i]]*var^i
	];

	If[SameQ[ret,0] && OptionValue[KeepLeadingOrder], 
		ret=LeadingTerm[npoly,var]
	];

	Return[ret]
];

TruncateArray[values_,var_,maxOrder_,opts:OptionsPattern[]]:=Module[{i,ret={}},
	For[i=1,i<= Length[values],i++,
		AppendTo[ret,TruncatePoly[values[[i]],var,maxOrder,FilterRules[{opts},Options[TruncatePoly]]]]
	];

	Return[ret]
];

TruncateMatrix[vecs_,var_,maxOrder_,opts:OptionsPattern[]]:=Module[{i,ret={}},
	For[i=1,i<= Length[vecs],i++,
		AppendTo[ret,TruncateArray[vecs[[i]],var,maxOrder,FilterRules[{opts},Options[TruncatePoly]]]]
	];

	Return[ret]
];

Clear[LeadingOrderArray,LeadingOrderMatrix];
LeadingOrderArray[arr_,var_]:=TruncateArray[arr,var,0,KeepLeadingOrder->True];
LeadingOrderMatrix[mat_,var_]:=TruncateMatrix[mat,var,0,KeepLeadingOrder->True];

SolveEquations[eqs_,unknowns_]:=Module[{roots={},i,j,equation,minVarOrder,e,varToSolve,res},
	For[i=1,i<= Length[eqs],i++,
		equation=Simplify[eqs[[i]]/.roots];
		If[SameQ[equation,0],Continue[]];
		varToSolve=-1;
		minVarOrder=10000;
		For[j=1,j<=Length[unknowns],j++,
			e=Exponent[equation,unknowns[[j]]];
			If[e>0 && e<minVarOrder,
				minVarOrder=e;
				varToSolve=j;
			]
		];

		If[varToSolve==-1,
			Print["Invalid equations: ", equation, "==0"];
			Return[{}]
		];

		Quiet[res=Solve[equation==0,unknowns[[varToSolve]]],{Solve::svars}];
		(*If[Length[res]>1,Print[equation,",",res]];*)
		If[Length[res]==0,Print["Cannot find solution: ",equation,";",unknowns[[varToSolve]]];Return[{}]];
		(*Print[res];*)
		roots=Simplify[roots/.Last[res]];
		roots=Join[roots,Last[res]];
	];

	Return[roots]
];

UnknownVars[vars_,roots_]:=Module[{v,i,ret={}},
	v=vars/.roots;
	For[i=1,i<= Length[v],i++,
		If[SameQ[v[[i]],vars[[i]]],
			AppendTo[ret,v[[i]]]
		]
	];

	Return[ret]
];

GetNorm[x_,y_]:=ComplexExpand[Conjugate[x].y];

NormalizeVector[vec_,var_,unknowns_,order_]:=Module[{i,ret,norm,roots,term,eqs={},unknownParams={},isLeading=True},
	norm=GetNorm[vec,vec];
	(*Print["norm: ",norm];*)
	For[i=0,i<= order,i++,
		term=Simplify[Coefficient[norm,var,i]];
		If[i==0,AppendTo[eqs,term-1], AppendTo[eqs,term]];
		(*If[isLeading && SameQ[term,0]\[Equal]False,
		isLeading=False;AppendTo[eqs,term-1], 
		AppendTo[eqs,term]
		]*)
	];

	roots=SolveEquations[eqs,unknowns];
	unknownParams=UnknownVars[unknowns,roots];
	ret=Simplify[vec/.roots];
	Return[{ret,unknownParams}]
];

ClearAll[EigenVectorEx];
Options[EigenVectorEx]={NamePrefix->"a",ReturnUnknowns->False,Normalized->True};
EigenVectorEx[mat_,eigenValue_,var_,order_,opts:OptionsPattern[]]:=Module[{i,j,n,cMat,varPowers={},
vec,ans,eqs={},unknowns,roots,res,returnUnknowns,normalized},
	normalized=OptionValue[Normalized];
	returnUnknowns=OptionValue[ReturnUnknowns];
	n=Length[mat];
	cMat=GenCMat[n,order,OptionValue[NamePrefix]];
	unknowns=Reverse[Flatten[Transpose[cMat]]];

	For[i=0,i<= order,i++,
		AppendTo[varPowers,var^i]
	];

	vec=cMat.varPowers;
	ans=(mat-eigenValue*IdentityMatrix[n]).vec;

	For[i=0,i<= order,i++,
		For[j=1,j<= n,j++,
			AppendTo[eqs,Simplify[Coefficient[ans[[j]],var,i]]]
		]
	];
	(*Quiet[roots=Solve[eqs\[Equal]0,unknowns],{Solve::svars}];
	unknowns=UnknownVars[unknowns,roots[[1]]];
	Print[roots[[1]]];
	vec=Simplify[vec/.roots[[1]]];*)
	roots=SolveEquations[eqs,unknowns];
	unknowns=UnknownVars[unknowns,roots];
	vec=Simplify[vec/.roots];

	If[normalized,
		res=NormalizeVector[vec,var,unknowns,order];
		vec=res[[1]];
		unknowns=res[[2]]
	];

	If[returnUnknowns,Return[{vec,unknowns}]];
	Return[Collect[vec,var]]
];

CommonOrder[val1_,val2_,var_,max_]:=Module[{i},
	For[i=0,i<= max,i++,
		If[SameQ[Coefficient[val1,var,i],Coefficient[val2,var,i]]==False,
		Return[i]]
	];

	Return[max]
];

ClearAll[EigensystemEx];
Options[EigensystemEx]={OutputDebug->False};
EigensystemEx[mat_,var_,order_,opts:OptionsPattern[]]:=Module[{dim,eigenv,maxPower,i,j,k,ch,vs={},comOrder,
roots,eqs={},prod,allUnknowns,vecs,zeroValue={},orderToCalc},
	dim=Length[mat];
	maxPower=2*order;
	If[OptionValue[OutputDebug],DebugOn[]];
	DebugInfo["Calculating eigen values..."];
	eigenv=EigenvaluesEx[mat,var,maxPower];

	(* Get the zero order eigenvalues. *)
	For[i=1,i<= dim,i++,
		AppendTo[zeroValue,Simplify[Coefficient[eigenv[[i]],var,0]]]
	];

	(* Calculate how many orders need to calculate for eigenvalues. *)
	orderToCalc=ConstantArray[order,dim];
	For[i=1,i<= dim,i++,
		For[j=i+1,j<= dim, j++,
			comOrder=CommonOrder[eigenv[[i]],eigenv[[j]],var,order];
			If[orderToCalc[[i]]<comOrder+order,orderToCalc[[i]]=comOrder+order];
			If[orderToCalc[[j]]<comOrder+order,orderToCalc[[j]]=comOrder+order];
		]
	];

	DebugInfo["Calculating eigenvectors..."];
	ch=ToCharacterCode["A"][[1]];
	For[i=1,i<= Length[eigenv],i++,
		DebugInfo["Find Eigenvector for ", eigenv[[i]]];
		AppendTo[vs,EigenVectorEx[mat,eigenv[[i]],var,orderToCalc[[i]],
						NamePrefix->"Var"<>FromCharacterCode[ch+i],ReturnUnknowns->True,Normalized->True]];
	];

	DebugInfo["Orthogonalizing eigenvectors..."];
	For[i=1,i<=dim,i++,
		For[j=i+1,j<=dim,j++,
			If[SameQ[zeroValue[[i]],zeroValue[[j]]],
				prod=GetNorm[vs[[i,1]],vs[[j,1]]];
				For[k=0,k<= Min[orderToCalc[[i]],orderToCalc[[j]]],k++,
					AppendTo[eqs,Simplify[Coefficient[prod,var,k]]]
				]
			]
		]
	];

	allUnknowns=Flatten[vs[[All,2]]];
	roots=SolveEquations[eqs,allUnknowns];
	vecs=TruncateMatrix[vs[[All,1]],var,order];
	vecs=Simplify[vecs/.roots];
	DebugInfo["Finished calculating eigenvectors."];
	DebugOff[];
	Return[{TruncateArray[eigenv,var,order],Collect[vecs,var]}]
];
