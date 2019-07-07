(* ::Package:: *)

correctAnswer[answer_, correct_]:=MatchQ[answer, correct]


turnOffEquivFrac[question_]:=StringMatchQ[question, {"*raction*implest form"}];
equivilentFraction[x_, y_, n_]:= n*x/y ;/turnOffEquivFrac==False;
isMatrix[answer_]:=MatchQ[answer, MatrixForm];
allpoints[question_]:=StringMatchQ[question, {"*all points*"}];
eitherPointfirst[a_, b_,c_, d_]:= {{"(",a, b, ")"},{"("c, d ")"}}-> {{"("c, d ")"},{"(",a, b, ")"}}
isPoint[answer_]:=StringMatchQ[answer, {"(*,*)"}];
commutative[a_,b_]:=a+b-> b+a;
distributive[a_,b_, c_]:=a*(b+c)-> a*b+a*c/; isMatrix==False;
commutativemulti[a_, b_]:=a*b-> b*a;/;isMatrix==False;
associative[a_, b_, c_]:=a+(b+c)-> (a+b)+c;
associativemulti[a_, b_,c_]:=a*(b*c)-> (a*b)*c;
sin2[x_]:=Sin[x]-> 2Sin[x/2]Cos[x/2];
cos2[x_]:=Cos[x]-> Power[Cos[x/2], 2]*2-1;
cos2alt1[x_]:=Cos[x]-> -1Power[Sin[x/2], 2]*2+1;
cos2alt2[x_]:=Cos[x]-> Power[Cos[x/2], 2]-Power[Sin[x/2], 2]
decForm[question_]:=StringMatchQ[question, "*ecimal form*"]
isCalc[question_]:=StringMatchQ[question, {"*erivative*", "*ifferniate*", "*ntegra*", "*aylor*xpand*", "*acLa*xpand*", "*imit*"}]
mixedNumber[question_]:=StringMatchQ[question, "*ixed number*"]
(*This is the wrong way to do it, patern matching is better here*)


canCommute[correct_]:=MatchQ[correct,"*+*"]|| MatchQ[correct, "*\times*"]


commuteProof[commuteanswer_, correct_]:=FindEquationalProof[commuteanswer==correct, a+b=b+a]


commutemultiProof[cmanswer_, correct_]:=FindEquationalProof[cmanswer==correct, {a*b=b*a, a+b=b+a}]


expandToSix[answer_, correct_, x_]:=If[Series[answer, {x, 0, 6}]==Series[correct, {x, 0, 6}], True, False]


calcCheck[answer_, correct_]:= Module[{x}, If[MatchQ[correct, RealDigits],  (*Trying to select what the variable is here*)


algebratheorems={ForAll[{a,b,c}, g[a, g[b,c]]==g[g[a, b], c]], 
				 ForAll[{a,b}, g[a, b]==g[b,a]], 
				 ForAll[{a,b}, f[a,b]==f[b,a]],
				 ForAll[{a,b,c}, f[a,f[b,c]]==f[f[a,b],c]],
				 ForAll[{a,b,c}, f[a, g[c,b]]==g[f[a,c], f[a,b]]],
				 ForAll[a, g[a,e]==a],
				 ForAll[a, f[a, e]==e],
				 ForAll[a, f[a, n]==a],
				 ForAll[a, g[a, inv[a]]==e],
				 ForAll[a, f[a, inv1[a]]==n]} (*This defines an abelian ring w/ distributive*)
				 


algebraandtrigtheorems={ForAll[{a,b,c}, g[a, g[b,c]]==g[g[a, b], c]], 
				 ForAll[{a,b}, g[a, b]==g[b,a]], 
				 ForAll[{a,b}, f[a,b]==f[b,a]],
				 ForAll[{a,b,c}, f[a,f[b,c]]==f[f[a,b],c]],
				 ForAll[{a,b,c}, f[a, g[c,b]]==g[f[a,c], f[a,b]]],
				 ForAll[a, g[a,e]==a],
				 ForAll[a, f[a, e]==e],
				 ForAll[a, f[a, n]==a],
				 ForAll[a, g[a, inv[a]]==e],
				 ForAll[a, f[a, inv1[a]]==n], 
				 ForAll[{a,b}, sin[g[a,b]]==g[f[sin[a],cos[b]], f[sin[b], cos[a]]]],
				 ForAll[ {a,b}, cos[g[a,b]]==g[f[cos[a],cos[b]], f[sin[inv[b]], sin[a]]]],
				 ForAll[a, sin[inv[a]]==inv[sin[a]]],
				 ForAll[a, cos[inv[a]]==cos[a]],
				 ForAll[a, g[f[sin[a],sin[a]], f[cos[a], cos[a]]]==n]}


theorems=<|"algebra 1"-> {algebratheorems}, "algebra 2"-> {algebraandtrigtheorems}, "calc"-> {algebraandtrigtheorems}|>;


equivalentAnswer[level_, tags_, answer_, correct_]:=If[correctAnswer[answer, correct], True, 
				If[tags==4, level="calc", level=level];
				Switch[tags, {0, 3, 4}, If[Simplify[Interpreter["MathExpression"][answer]- Interpreter["MathExpression"][correct]]==0, 
					If[UnsameQ[Head[Interpreter["MathExpression"][answer]], Failure], 
						tanswer=removeProperFormat[Interpreter["MathExpression"][answer]];
						tcorrectanswer=removeProperFormat[Interpreter["MathExpression"][correct]];
						proof:=TimeConstrained[FindEquationalProof[tanswer==tcorrectanswer , theorems[[level]]],1];
							If[proof["Logic"]=="EquationalLogic", 
								If[Complement[Query[Key[{"SubstitutionLemma", All}]]proof["ProofDataset"]["Statement"], theorems[[level]]]=={}, True, False],
								False],
						False],
					False],
				1, False, 
				2, False, 
				5, If[Complement[StringSplit[answer, "),("], StringSplit[correct, "),("]]=={}, True, False],  
				6, If[Complement[StringSplit[answer, "),("], StringSplit[correct, "),("]]=={}, True, False]
				]];


determinetags[question_]:=If[allpoints[question], If[turnOffEquivFrac[question], 5, If[decForm[question], 6, 3]], If[turnOffEquivFrac[question], 1, If[decForm[question], 2, If[isCalc[question], 4, 0]]]];  (*Want this to return an value for tag*)


(* ::Text:: *)
(*	Tags have the following values:*)
(*{*)
(* {Value, Meaning},*)
(* {0, No Context restrictions},*)
(* {1, Simplest Form Fraction},*)
(* {2, Decimal Representation},*)
(* {3, A set of points},*)
(* {4, Calculus},*)
(* {5 , A set of Points of simplest fractions},*)
(* {6, A set of points in decimal }*)
(*}*)


checkforEquivlentanswers[question_, answer_, correct_, level_]:=
Module[{},
			t=determinetags[question];
			equivalentAnswer[level, t, answer, correct]]	


removeSinCos[given_]:=given/.{Sin->sin, Cos->cos} 


removeSinCos[Sin[5]+Cos[x]]


replacePlus[given_]:=given/.{Plus-> g, Times[-1, amin_]->inv[amin]}


replacePlus[a-b]


replaceMulti[given_]:=given/.{Times-> f, Power[adiv_, -1]-> inv1[adiv]}


replaceTanSecCscCot[given_]:=given/.{Tan[atan_]-> f[sin[atan],inv1[cos[atan]]], Sec[asec_]-> inv1[cos[asec]], Csc[acsc_]-> inv1[sin[acsc]], Cot[acot_]-> f[inv1[sin[acot]],cos[acot]]}


replaceTanSecCscCot[Tan[y]+ Csc[x]]


removeProperFormat[given_]:=replacePlus[replaceMulti[removeSinCos[replaceTanSecCscCot[given]]]]
