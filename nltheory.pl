% This file contains the patterns that can be used in the natural language description of an AI, and converts them to defeasible clauses. 
% Author: Bas Testerink 

:- op(1200, xfy, <=).
:- op(200, fx, not). 

% Match a String with a pattern, where variables are parsed to propositions
matches(_, []).
matches(String, [Head, Next |Rest]):-
	var(Head), 
	atom_string(Next, NextString),
	sub_string(String, Before, _, After, NextString),!,
	sub_string(String, 0, Before, _, HeadString),
	proposition_from_string(HeadString, Head),!,
	sub_string(String, _, After, 0, LeftOverString),
	matches(LeftOverString, Rest).
matches(String, [Head | Rest]):-
	\+ var(Head),
	atom_string(Head, HeadString),
	sub_string(String, _, _, After, HeadString),
	sub_string(String, _, After, 0, LeftOverString),
	matches(LeftOverString, Rest).
matches(String, [Head]):-
	var(Head), 
	proposition_from_string(String, Head).

% Turn a string in to a proposition
proposition_from_string(String, Result):-
	atom_string('not ', NotStr), 
	does_not_contain_any_of(String, [' and ', ' or ', 'If ']),
	move_not_forward(String, NewString),
	(sub_string(NewString, 0, _, After, NotStr)->
		(	sub_string(NewString, _, After, 0, PropositionStr), 
			atom_string(PropositionUpper, PropositionStr), 
			downcase_atom(PropositionUpper, Proposition),
			Result = not Proposition);
		(	sub_string(NewString, 0, _, 0, PropositionStr),
			atom_string(PropositionUpper, PropositionStr),
			downcase_atom(PropositionUpper, Result))
	).  

% Check whether a string not contains any of the elements in the list of strings
does_not_contain_any_of(_, []).	
does_not_contain_any_of(String, [ForbiddenAtom|T]):-
		atom_string(ForbiddenAtom, ForbiddenStr),
		\+ sub_string(String, _, _, _, ForbiddenStr),
		does_not_contain_any_of(String, T).	

% Grab 'not' from a string and place it in front, e.g.: 'you are not wounded' becomes 'not you are wounded'
move_not_forward(String, String):-
	does_not_contain_any_of(String, [' not ']).
move_not_forward(String, NewString):-
	atom_string('not ', NotStr), 
	sub_string(String, Before, _, After, NotStr),
    sub_string(String, 0, Before, _, BeforeNot), 
    sub_string(String, _, After, 0, AfterNot),
	string_concat(NotStr, BeforeNot, TempStr),
	string_concat(TempStr, AfterNot, NewString).

%%%% Various string patterns that can match
	
% E.g.: Heal is an action.
rule_from_string(String, goal(Action)):-
	matches(String, [Action, ' is an action.']).
	
% E.g.: If you can heal then you should.
rule_from_string(String, (Action <= CanPremise)):-
	matches(String, ['If you can ', Action, ' then you should.']),
	concat('you can ', Action, CanPremise).

% E.g.: You can heal if you have a potion or you have a healing spell
rule_from_string(String, (CanAction <= Conjunction)):-
	composition_pattern(CompositionPattern, Conjunctions, 0),
	append(['You can ', Action, ' if '|CompositionPattern], ['.'], Pattern),
	matches(String, Pattern),
	concat('you can ', Action, CanAction),!,
	get_conjunction(Conjunctions, Conjunction).

% E.g.: You are wounded if you are critically wounded or you are lightly wounded.
rule_from_string(String, (Proposition <= Conjunction)):-
	composition_pattern(CompositionPattern, Conjunctions, 0),
	append([Proposition, ' if '|CompositionPattern], ['.'], Pattern),
	matches(String, Pattern),!,
	get_conjunction(Conjunctions, Conjunction). 
	
% E.g.: If you are not wounded then you should not heal.
rule_from_string(String, (Action <= Conjunction)):-
	composition_pattern(CompositionPattern, Conjunctions, 0),
	append(['If '|CompositionPattern], [' then you should ', Action, '.'], Pattern),
	matches(String, Pattern),!,
	get_conjunction(Conjunctions, Conjunction).

% Grab a conjunction and turn it into a parenthesis tuple instead of list
get_conjunction(Conjunctions, Conjunction):-
	member(ConjList, Conjunctions),
	list_to_parenthesis(ConjList, Conjunction).

% From list to a parenthesis tuple
list_to_parenthesis([A], A).
list_to_parenthesis([A, B], (A, B)).
list_to_parenthesis([A, B, C | T], (A, D)):-
	list_to_parenthesis([B, C |T], D).

% Make a composition pattern	
composition_pattern([Proposition],[[Proposition]], _).
composition_pattern([Proposition, ' and '|Rest],[[Proposition|T]|T2], Counter):- 
	max_composition_length(Length),
	Counter < Length,
	NewCounter is Counter + 1,
	composition_pattern(Rest, [T|T2], NewCounter).
composition_pattern([Proposition, ' or '|Rest],[[Proposition]|[NewConj|T]], Counter):-  
	max_composition_length(Length),
	Counter < Length,
	NewCounter is Counter + 1,
	composition_pattern(Rest, [NewConj|T], NewCounter).
	
% Maximum size of a composition of a conjunction or disjunction
max_composition_length(8).

% Convert an atom to a clause
convertAtom(Atom, Clause):-
	atom_string(Atom, String),
	rule_from_string(String, Clause).