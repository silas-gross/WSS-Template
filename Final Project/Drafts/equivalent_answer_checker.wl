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
isCalc[question_]:=StringMatchQ[question, {"*erivative*", "*ifferniate*", "*ntegra*", "*aylor*xpand*", "*acLa*xpand*"}]
(*This is the wrong way to do it, patern matching is better here*)


canCommute[correct_]:=MatchQ[correct,"*+*"]|| MatchQ[correct, "*\times*"]


commuteProof[commuteanswer_, correct_]:=FindEquationalProof[commuteanswer==correct, a+b=b+a]


commutemultiProof[cmanswer_, correct_]:=FindEquationalProof[cmanswer==correct, {a*b=b*a, a+b=b+a}]


expandToSix[answer_, correct_, x_]:=If[Series[answer, {x, 0, 6}]==Series[correct, {x, 0, 6}], True, False]


equivalentAnswer[level_, tags_, answer_, correct_]:=If[correctAnswer[answer, correct], True, (*some opporations go here, tags is an array of binary switches (context)*)]


determinetags[question_]:=If[allpoints[question], 3, If[turnOffEquivFrac[question], 1, If[decForm[question], 2, If[isCalc[question], 4, 0]]]];  (*Want this to return an value for tag*)


(* ::Text:: *)
(*Tags have the following values:*)
(*{*)
(* {Value, Meaning},*)
(* {0, No Context restrictions},*)
(* {1, Simplest Form Fraction},*)
(* {2, Decimal Representation},*)
(* {3, A set of points},*)
(* {4, Calculus}*)
(*}*)


(*Basic Idea: Patern match w/ context to pull which of the proof objects I need. Put the proof objects into an array that is multi level and can be accessed by way of the value of tags*)
(*expand to six will only be for calc, make tags a number*)
