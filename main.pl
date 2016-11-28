% This file contains the main loop, which reads a natural language AI program from 'AI.txt', translates it in an defeasible theory (using argdtinterpreter.pl) and then translates the theory in an efficient decision tree (using nltheory.pl).  
% Author: Bas Testerink 

:- ensure_loaded(nltheory).
:- ensure_loaded(argdtinterpreter).
:- set_prolog_flag(verbose, silent).
:- op(1200, xfy, <=).
:- dynamic(goal/1).
:- dynamic('<='/2).

main(Theory):- 
	write('READING SPECIFICATION'), nl,
    open(Theory, read, Stream), 
    read_specification(Stream, Lines), 
    close(Stream), !,
	write('CONVERTING TO CLAUSES'), nl, 
	findall(
		Clause, 
		(member(Line, Lines), convertAtom(Line, Clause), write(Clause), nl), 
		Clauses
	),
	assertAll(Clauses),
	write('BUILDING DECISION TREE'), nl,
	tree,
	retractall('<='(_,_)),
	retractall(goal(_)), !. 
  
% Read the specification and put the lines separately in a list  
read_specification(Stream,[]):- 
    at_end_of_stream(Stream).  
read_specification(Stream, [Line|Rest]):- 
    \+ at_end_of_stream(Stream), 
    readLine(Stream, Line),
	write(Line), nl, 
    read_specification(Stream, Rest).

% Read a line from the stream
readLine(Stream, Line):- 
	get_code(Stream, Char), 
	checkCharAndReadRest(Char, Chars, Stream), 
	atom_codes(Line, Chars). 
 
% Read character
checkCharAndReadRest(10, [], _):-  !.  
checkCharAndReadRest(-1, [], _):-  !. 
checkCharAndReadRest(end_of_file, [], _):-  !. 
checkCharAndReadRest(Char, [Char|Chars], Stream):- 
	get_code(Stream, NextChar),  
	checkCharAndReadRest(NextChar, Chars, Stream).
	 
% Assert the elemetns in a list
assertAll([]).
assertAll([H|T]):- assertz(H), assertAll(T).
	
:- main('AI.txt').