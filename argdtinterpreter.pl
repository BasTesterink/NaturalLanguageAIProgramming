% This file contains the functionality of turning a defeasible theory into a decision tree such that the least amount of propositions are checked in order to determine whether a goal proposition (e.g., an action in case of KeeperRL) is supported by the system (game) state. 
% Author: Bas Testerink 

:- op(900, xfy, <<).
:- op(1200, xfy, <-).
:- op(1200, xfy, <=).
:- op(1200, xfy, ~).
:- op(200, fx, not).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% Finding valuations that support a proposition and reject all counter-arguments  %%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Obtain the proposition valuation (only non-defeasible propositions) that guarantees that no counterargument can be made against the given proposition
legal(Proposition, Valuation):-   
	goal(Proposition),
	support(Proposition, [], Valuation).  
	
% Aux. predicate to loop through a list of propositions which have to be supported. Accumulates the valuation.
supportList([], Acc, Acc).
supportList([Next|Rest], Acc, Valuation):-
	support(Next, Acc, TempValuation),
	supportList(Rest, TempValuation, Valuation).

% Support returns the propositions such that with those propositions an uncontested argument can be made for the conclusion. The accumulator accumulates the propositions to (not) hold so far and which cannot be changed.

% Case: Proposition is non-defeasible, i.e., there is no rule for it or its counter proposition.
support(Proposition, Acc, [Proposition|Acc]):-
	\+ (Proposition <= _),
	counterProposition(Proposition, CounterProposition),
	\+ (CounterProposition <= _),
	\+ member(Proposition, Acc),
	\+ member(CounterProposition, Acc).
support(Conclusion, Acc, Acc):-
	member(Conclusion, Acc).
	
% Case: Proposition is defeasible, i.e., there is at least one rule that supports it or its counter proposition. Hence, for at least one rule all premises have to be supported and all counter arguments for the counter proposition have to be defeated.
support(Proposition, Acc, Valuation):- 
	(Proposition <= Premises),
	rejectCounterProposition(Proposition, Acc, TempValuation),
	toList(Premises, PremisesList),
	supportList(PremisesList, TempValuation, Valuation).
	
% Grab all the rules that can be used to support the counter proposition and then reject each of them by having at least one proposition not true for that rule.
rejectCounterProposition(Proposition, Acc, Valuation):- 
	counterProposition(Proposition, CounterProposition),
	findall((CounterProposition <= Premises), (CounterProposition <= Premises), Rules),
	rejectRules(Rules, Acc, Valuation).
	
% You reject a rule by supporting a counter of one of its premises, or by recursively rejecting a rule that supports the counter
rejectRules([], Acc, Acc).
rejectRules([(_ <= Premises)|Rest], Acc, Valuation):-
	toList(Premises, PremisesList),
	member(Premise, PremisesList), 
	((	counterProposition(Premise, CounterPremise),
		support(CounterPremise, Acc, TempValuation)
	);( findall((Premise <= Premises2), (Premise <= Premises2), Rules),
		Rules \= [], 
		rejectRules(Rules, Acc, TempValuation)
	)), 
	rejectRules(Rest, TempValuation, Valuation).
	
% Get strip or add a 'not' in front of a proposition
counterProposition(not Proposition, Proposition).
counterProposition(Proposition, not Proposition):-
	Proposition \= (not _).

% Convert parenthesis tuple to list	
toList(X, [X]):- X \= (_,_).
toList((X, Y), [X|Result]):- toList(Y,Result).

% Get all the propositions that are not defeasible
getAllNonDefeasiblePropositions(Result):-
	findall(Proposition, isNonDefeasible(Proposition), List),
	sort(List, Result).

% Get a non defeasible proposition
isNonDefeasible(Proposition):-
	(_ <= Premises),
	toList(Premises, List),
	member(Premise, List),
	(Premise = (not X) -> Proposition = X ; Proposition = Premise),
	counterProposition(Proposition, CounterProposition),
	\+ (Proposition <= _), 
	\+ (CounterProposition <= _).
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%% Building a decision tree %%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% General algorithm of makeTree: Given a collection of available input propositions (non-defeasible propositions that can be asked at runtime), the list of goal propositions and the valuations that support them, build a tree of valuations where the leafs support the goal propositions.

% Case: No more supportable goals left, pick no move
makeTree(_, [], _, noMove).
% Case: Each supportable goal is fully supported by the current evaluation. So make a leaf.
makeTree(_, CandidateGoals, CurrentValuation, Goals):-
	fullySupportedList(CandidateGoals, CurrentValuation),
	findall(SupportedGoal, member(legal(SupportedGoal, _), CandidateGoals), TempSupportedGoals),
	sort(TempSupportedGoals, SupportedGoals),
	orderByPreference(SupportedGoals, Goals), !.
% Case: Not every goal is fully supported by the current evaluation. Therefore make a choice. Decide upon the proposition that can distinguish the most supported/unsupported goals if known.
makeTree(InputPropositions, CandidateGoals, CurrentValuation, choice(Proposition, TreePositive, TreeNegative)):-
	\+ fullySupportedList(CandidateGoals, CurrentValuation),
	getPropositionWithMaxGain(InputPropositions, CandidateGoals, _, (-1), Proposition),
	select(Proposition, InputPropositions, NewInputPropositions),
	counterProposition(Proposition, CounterProposition),
	findall(legal(Goal, Valuation), (member(legal(Goal, Valuation),CandidateGoals), \+ member(CounterProposition, Valuation)), LegalIfPositive),
	findall(legal(Goal, Valuation), (member(legal(Goal, Valuation),CandidateGoals), \+ member(Proposition, Valuation)), LegalIfNegative),
	makeTree(NewInputPropositions, LegalIfPositive, [Proposition|CurrentValuation], TreePositive),
	makeTree(NewInputPropositions, LegalIfNegative, [(not Proposition)|CurrentValuation], TreeNegative). 

% Get the proposition that obtains the maximum gain.
getPropositionWithMaxGain([], _, BestProposition, _, BestProposition).
getPropositionWithMaxGain([Next|Rest], Legal, TempBestProposition, TempBestGain, BestProposition):-
	gain(Legal, Next, Gain),
	((Gain > TempBestGain) -> 
		getPropositionWithMaxGain(Rest, Legal, Next, Gain, BestProposition) ;
		getPropositionWithMaxGain(Rest, Legal, TempBestProposition, TempBestGain, BestProposition)).

% The gain of a proposition is the amount of canditates that can be rejected if true plus the amount of candidates that can be rejected if false. 
gain([], _, 0). 
gain(CandidateGoals, Proposition, Gain):-
	CandidateGoals \= [], 
	counterProposition(Proposition, CounterProposition),
	findall(Action, (member(legal(Action, Valuation),CandidateGoals), member(Proposition, Valuation)), ActionsPos),
	findall(Action, (member(legal(Action, Valuation),CandidateGoals), member(CounterProposition, Valuation)), ActionsNeg),
	length(ActionsPos, NrRejectedIfNegative),
	length(ActionsNeg, NrRejectedIfPositive), 
	Gain is NrRejectedIfPositive + NrRejectedIfNegative.
	
% Check if each candidate goal is fully supported by a given valuation
fullySupportedList([], _).
fullySupportedList([legal(_,Conditions)|Rest], CurrentValuation):-
	findall(X, (member(X,Conditions), \+ member(X, CurrentValuation)), []),
	fullySupportedList(Rest, CurrentValuation).

% TODO: still has to be implemented
orderByPreference(Goals, goals(Goals)).
 
% Print the decision tree
printTree(choice(A, Pos, Neg), PrependSelf, PrependChildren):-
	write(PrependSelf), write(A), write('?'),nl,
	concat(PrependChildren, '|    ', PrependChildren2),
	concat(PrependChildren, '     ', PrependChildren3),
	concat(PrependChildren, '|-y->', PrependSelf2),
	concat(PrependChildren, 'L-n->', PrependSelf3),
	printTree(Pos, PrependSelf2, PrependChildren2),  
	printTree(Neg, PrependSelf3, PrependChildren3).
printTree(noMove, PrependSelf, _):-
	write(PrependSelf), write(noMove),nl.
printTree(goals(Goals), PrependSelf, _):-
	write(PrependSelf), write(Goals),nl.

% Simplify the tree. Currently only removes choices where all answers end with the same supported goals
simplifyTree(choice(_, X, X), SimpleX):- simplifyTree(X, SimpleX).
simplifyTree(noMove, noMove).
simplifyTree(goals(Goals), goals(Goals)).
simplifyTree(choice(A, X, Y), Simple):-
	X\=Y,
	simplifyTree(X, SimpleX),
	simplifyTree(Y, SimpleY),
	((SimpleX \= SimpleY) -> (Simple = choice(A, SimpleX, SimpleY)); (Simple = SimpleX)).
	
tree:-
	getAllNonDefeasiblePropositions(InputPropositions),
	findall(legal(Action, Conditions), legal(Action,Conditions), Legal),
	makeTree(InputPropositions, Legal, [], Tree),
	simplifyTree(Tree, Simplified),
	printTree(Simplified, '', '').