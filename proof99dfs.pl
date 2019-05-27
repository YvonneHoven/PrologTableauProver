%% making functions dynamic to be able to use assert & discontiguous to be able to put all functions not necessarily side by side
:- dynamic prf(_,_).
:- dynamic assprove(_,_).
:- dynamic noPrint(_,_).
:- discontiguous proof/6.
:- discontiguous proof/4.
:- discontiguous prove/2.

%% all assertions of the premises
ass([]).
ass([not,not,not, H]):- wrt([not,not,not, H], '+'), assert(assprove([not,not,not,H],'+')).  
ass([not,not, H]):- wrt([not,not, H], '+'), assert(assprove([not,not,H],'+')).
ass([not, H]):-  wrt([atm(not,H)], '+'), assert(prf(atm(not,H),'+')).

%%simplify assert {A&B} {AVB}
ass(['{', not,not,not,A, B, not,not,not,C, '}'|T]):- wrt(['{', atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,atm(not,C))), '}'], '+'), ass([atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,atm(not,C)))|T]).
ass(['{', not,not,not,A, B, not,not,C, '}'|T]):- wrt(['{', atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,C)), '}'], '+'), ass([atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,C))|T]).
ass(['{', not,not,not,A, B, not,C, '}'|T]):- wrt(['{', atm(not,atm(not,atm(not,A))), B, atm(not,C), '}'], '+'), ass([atm(not,atm(not,atm(not,A))), B, atm(not,C)|T]).
ass(['{', not,not,not,A, B, C, '}'|T]):- wrt(['{', atm(not,atm(not,atm(not,A))), B, C, '}'], '+'), ass([atm(not,atm(not,atm(not,A))), B, C|T]).
ass(['{', not,not,A, B, not,not,not,C, '}'|T]):- wrt(['{', atm(not,atm(not,A)), B, atm(not,atm(not,atm(not,C))), '}'], '+'), ass([atm(not,atm(not,A)), B, atm(not,atm(not,atm(not,C)))|T]).
ass(['{', not,not,A, B, not,not,C, '}'|T]):- wrt(['{', atm(not,atm(not,A)), B, atm(not,atm(not,C)), '}'], '+'), ass([atm(not,atm(not,A)), B, atm(not,atm(not,C))|T]).
ass(['{', not,not,A, B, not,C, '}'|T]):- wrt(['{', atm(not,atm(not,A)), B, atm(not,C), '}'], '+'), ass([atm(not,atm(not,A)), B, atm(not,C)|T]).
ass(['{', not,not,A, B, C, '}'|T]):- wrt(['{', atm(not,atm(not,A)), B, C, '}'], '+'), ass([atm(not,atm(not,A)), B, C|T]).
ass(['{', not,A, B, not,not,not,C, '}'|T]):- wrt(['{', atm(not,A), B, atm(not,atm(not,atm(not,C))), '}'], '+'), ass([atm(not,A), B, atm(not,atm(not,atm(not,C)))|T]).
ass(['{', not,A, B, not,not,C, '}'|T]):- wrt(['{', atm(not,A), B, atm(not,atm(not,C)), '}'], '+'), ass([atm(not,A), B, atm(not,atm(not,C))|T]).
ass(['{', not,A, B, not,C, '}'|T]):- wrt(['{', atm(not,A), B, atm(not,C), '}'], '+'), ass([atm(not,A), B, atm(not,C)|T]).
ass(['{', not,A, B, C, '}'|T]):- wrt(['{', atm(not,A), B, C, '}'], '+'), ass([atm(not,A), B, C|T]).
ass(['{', A, B, not,not,not,C, '}'|T]):- wrt(['{', A, B, atm(not,atm(not,atm(not,C))), '}'], '+'), ass([A, B, atm(not,atm(not,atm(not,C)))|T]).
ass(['{', A, B, not,not,C, '}'|T]):- wrt(['{', A, B, atm(not,atm(not,C)), '}'], '+'), ass([A, B, atm(not,atm(not,C))|T]).
ass(['{', A, B, not,C, '}'|T]):- wrt(['{', A, B, atm(not,C), '}'], '+'), ass([A, B, atm(not,C)|T]).
ass(['{', A, B, C, '}'|T]):- wrt(['{', A, B, C, '}'], '+'), ass([A, B, C|T]).
%%simplify assert A&B AVB
ass([not,not,not,A, B, not,not,not,C|T]):- ass([atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,atm(not,C)))|T]).
ass([not,not,not,A, B, not,not,C|T]):- ass([atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,C))|T]).
ass([not,not,not,A, B, not,C|T]):- ass([atm(not,atm(not,atm(not,A))), B, atm(not,C)|T]).
ass([not,not,not,A, B, C|T]):- ass([atm(not,atm(not,atm(not,A))), B, C|T]).
ass([not,not,A, B, not,not,not,C|T]):- ass([atm(not,atm(not,A)), B, atm(not,atm(not,atm(not,C)))|T]).
ass([not,not,A, B, not,not,C|T]):- ass([atm(not,atm(not,A)), B, atm(not,atm(not,C))|T]).
ass([not,not,A, B, not,C|T]):- ass([atm(not,atm(not,A)), B, atm(not,C)|T]).
ass([not,not,A, B, C|T]):- ass([atm(not,atm(not,A)), B, C|T]).
ass([not,A, B, not,not,not,C|T]):- ass([atm(not,A), B, atm(not,atm(not,atm(not,C)))|T]).
ass([not,A, B, not,not,C|T]):- ass([atm(not,A), B, atm(not,atm(not,C))|T]).
ass([not,A, B, not,C|T]):- ass([atm(not,A), B, atm(not,C)|T]).
ass([not,A, B, C|T]):- ass([atm(not,A), B, C|T]).
ass([A, B, not,not,not,C|T]):- ass([A, B, atm(not,atm(not,atm(not,C)))|T]).
ass([A, B, not,not,C|T]):- ass([A, B, atm(not,atm(not,C))|T]).
ass([A, B, not,C|T]):- ass([A, B, atm(not,C)|T]).

%%assert A&B AVB
ass([A, '&', C|T]):- A\=not, C\=not,  wrt([A,'&',C], '+'), ass(T), assert(assprove([A, '&', C], '+')).
ass([A, 'V', C|T]):- A\=not, C\=not, wrt([A,'V',C], '+'), ass(T), assert(assprove([A, 'V', C], '+')).

%%simplify assert notnot{A&B} notnot{AVB}
ass([not,not, '{', not,not,H, AO, not,not,H2, '}'|T]):- wrt([not,not, '{', atm(not,atm(not,H)), AO, atm(not,atm(not,H2)), '}'], '+'), ass([atm(not,atm(not,H)), AO, atm(not,atm(not,H2))|T]).
ass([not,not, '{', not,not,H, AO, not,H2, '}'|T]):- wrt([not,not, '{', atm(not,atm(not,H)), AO, atm(not,H2), '}'], '+'), ass([atm(not,atm(not,H)), AO, atm(not,H2)|T]).
ass([not,not, '{', not,not,H, AO, H2, '}'|T]):- wrt([not,not, '{', atm(not,atm(not,H)), AO, H2, '}'], '+'), ass([atm(not,atm(not,H)), AO, H2|T]).
ass([not,not, '{', not,H, AO, not,not,H2, '}'|T]):- wrt([not,not, '{', atm(not,H), AO, atm(not,atm(not,H2)), '}'], '+'), ass([atm(not,H), AO, atm(not,atm(not,H2))|T]).
ass([not,not, '{', not,H, AO, not,H2, '}'|T]):- wrt([not,not, '{', atm(not,H), AO, atm(not,H2), '}'], '+'), ass([atm(not,H), AO, atm(not,H2)|T]).
ass([not,not, '{', not,H, AO, H2, '}'|T]):- wrt([not,not, '{', atm(not,H), AO, H2, '}'], '+'), ass([atm(not,H), AO, H2|T]).
ass([not,not, '{', H, AO, not,not,H2, '}'|T]):- wrt([not,not, '{', H, AO, atm(not,atm(not,H2)), '}'], '+'), ass([H, AO, atm(not,atm(not,H2))|T]).
ass([not,not, '{', H, AO, not,H2, '}'|T]):- wrt([not,not, '{', H, AO, atm(not,H2), '}'], '+'), ass([H, AO, atm(not,H2)|T]).
ass([not,not, '{', H, AO, H2, '}'|T]):- wrt([not,not, '{', H, AO, H2, '}'], '+'), ass([H, AO, H2|T]).
%%simplify assert not{A&B} not{AVB}
ass([not, '{', not,not,H, AO, not,not,H2, '}'|T]):- ass([not, '{', atm(not,atm(not,H)), AO, atm(not,atm(not,H2)), '}'|T]).
ass([not, '{', not,not,H, AO, not,H2, '}'|T]):- ass([not, '{', atm(not,atm(not,H)), AO, atm(not,H2), '}'|T]).
ass([not, '{', not,not,H, AO, H2, '}'|T]):- ass([not, '{', atm(not,atm(not,H)), AO, H2, '}'|T]).
ass([not, '{', not,H, AO, not,not,H2, '}'|T]):- ass([not, '{', atm(not,H), AO, atm(not,atm(not,H2)), '}'|T]).
ass([not, '{', not,H, AO, not,H2, '}'|T]):- ass([not, '{', atm(not,H), AO, atm(not,H2), '}'|T]).
ass([not, '{', not,H, AO, H2, '}'|T]):- ass([not, '{', atm(not,H), AO, H2, '}'|T]).
ass([not, '{', H, AO, not,not,H2, '}'|T]):- ass([not, '{', H, AO, atm(not,atm(not,H2)), '}'|T]).
ass([not, '{', H, AO, not,H2, '}'|T]):- ass([not, '{', H, AO, atm(not,H2), '}'|T]).

%%assert not{A&B} not{AVB}
ass([not, '{', H, '&', H2, '}'|T]):- wrt([not, '{', H, '&', H2, '}'], '+'), assert(assprove([not, '{', H, '&', H2, '}'], '+')), prove(T, '+').
ass([not, '{', H, 'V', H2, '}'|T]):- wrt([not, '{', H, 'V', H2, '}'], '+'), assert(assprove([not, '{', H, 'V', H2, '}'], '+')), prove(T, '+').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% the main code for the program
printList([], _) :- nl.
printList([atm(not,H)|T], S):- write("not "), write(H), write(", "), write(S),  write(' | '), printList(T, S).
printList([H|T], S) :- H\=atm(not,_), write(H), write(", "), write(S), write(' | '), printList(T, S).

prepareAnswer1(NP1,NP2):- NP1=[], NP2=[], nl, findall(Y, prf(Y, '+'), PL), findall(X, prf(X, '-'), NL), 
    	write('positive literals: '), nl, write("|"), printList(PL, '+'),
    	write('negative literals: '), nl, write("|"), printList(NL, '-').
prepareAnswer1([H1|T1],[H2|T2]):- prepareAnswer2([H1|T1], []), prepareAnswer2([], [H2|T2]).
prepareAnswer2([],[]).
prepareAnswer2([[H]|T],[]):- retract(noPrint(H, '+')), prepareAnswer2(T,[]).
prepareAnswer2([],[[H]|T]):- retract(noPrint(H, '-')), prepareAnswer2([],T).

wrt([],S):- write(","), writeln(S).
wrt([atm(not,atm(not,atm(not,A)))|T],S):- write("notnotnot"), write(A), wrt(T,S).
wrt([atm(not,atm(not,A))|T],S):- A\=atm(not,_), write("notnot"), write(A), wrt(T,S).
wrt([atm(not,A)|T],S):- A\=atm(not,_), write("not"), write(A), wrt(T,S).
wrt([H|T],S):- H\=atm(not,_), write(H), wrt(T,S).

prove(A, '|', C):- C\=[_], C\=[not,_], ass(A), wrt(C, '-'), nl, findall([Z], assprove(Z, '+'), AS), check(AS), writeln("inferences solving:"), prove(C, '-'), findall([Q1], noPrint(Q1, '+'), NP1), findall([Q2], noPrint(Q2, '-'), NP2), prepareAnswer1(NP1,NP2).
prove(A, '|', C):- C=[B], ass(A), wrt(C, '-'), assert(prf(B, '-')), nl, findall([Z], assprove(Z, '+'), AS), check(AS), findall([Q1], noPrint(Q1,'+'), NP1), findall([Q2], noPrint(Q2,'-'), NP2), prepareAnswer1(NP1,NP2).
prove(A, '|', C):- C=[not,B], ass(A), wrt(C, '-'), assert(prf(atm(not,B), '-')), nl, findall([Z], assprove(Z, '+'), AS), check(AS), findall([Q1], noPrint(Q1,'+'), NP1), findall([Q2], noPrint(Q2,'-'), NP2), prepareAnswer1(NP1,NP2).

check([]).
check([[H]|T]):- H\=[[]], writeln("premises solving:"), prsolve([[H]|T]), nl.
prsolve([]).
prsolve([[H]|T]):- prove(H, '+'), prsolve(T).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%the real logic behind the code

prove([atm(not,atm(not,(atm(not,A))))|T],S):- wrt([not,not,not,A],S), wrt([not,A],S), prove(T,S).
prove([atm(not,(atm(not,A)))|T],S):- T\=['&'|_], T\=['V'|_], wrt([not,not,A],S), wrt([A],S), prove(T,S).
prove([not,not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,not,H], S), wrt([not,H],S), prove(T, S).
prove([not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,H], S), wrt([H],S), prove(T, S).
prove([not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,H], S), prove(T, S).

prove([H|[]], S):- H\=[_], H\=not, H\=atm(not,_), wrt([H], S), assert(prf(H, S)).
prove([], _).

%%proof(A&B+) proof(A&B&C+)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '+'):- wrt([atm(not,atm(not,A))], '+'), wrt([not,not,B], '+'), wrt([A], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')).
proof(atm(not,atm(not,A)), '&', B, '+'):- B\=atm(not,atm(not,_)), wrt([not,not,A], '+'), wrt([B], '+'), wrt([A], '+'), assert(prf(A,'+')), assert(prf(B,'+')).
proof(A, '&', atm(not,atm(not,B)), '+'):- A\=atm(not,atm(not,_)), wrt([A], '+'), wrt([not,not,B], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')).
proof(A, '&', B, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')).
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '+'):- wrt([not,not,A], '+'), wrt([not,not,B], '+'), wrt([not,not,C], '+'), wrt([A], '+'), wrt([B], '+'), wrt([C], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C, '+'):- C\=atm(not,atm(not,_)), wrt([not,not,A], '+'), wrt([not,not,B], '+'), wrt([C], '+'), wrt([A], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).
proof(atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C)), '+'):- B\=atm(not,atm(not,_)), wrt([not,not,A], '+'), wrt([B], '+'), wrt([not,not,C], '+'), wrt([A], '+'), wrt([C], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).
proof(A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), wrt([A], '+'), wrt([not,not,B], '+'), wrt([C], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).
proof(atm(not,atm(not,A)), '&', B, '&', C, '+'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([not,not,A], '+'), wrt([B], '+'), wrt([C], '+'), wrt([A], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).
proof(A, '&', atm(not,atm(not,B)), '&', C, '+'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A], '+'), wrt([not,not,B], '+'), wrt([C], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).
proof(A, '&', B, '&', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A], '+'), wrt([B], '+'), wrt([not,not,C], '+'), wrt([C], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).
proof(A, '&', B, '&', C, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A], '+'), wrt([C], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')), assert(prf(C,'+')).

%%proof(AVB-) proof(AVBVC-)
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), '-'):- wrt([not,not,A], '-'), wrt([B], '-'), wrt([A], '-'), assert(prf(A,'-')), assert(prf(B,'-')).
proof(atm(not,atm(not,A)), 'V', B, '-'):- B\=atm(not,atm(not,_)), wrt([not,not,A], '-'), wrt([B], '-'), wrt([A], '-'), assert(prf(A,'-')), assert(prf(B,'-')).
proof(A, 'V', atm(not,atm(not,B)), '-'):- A\=atm(not,atm(not,_)), wrt([A], '-'), wrt([not,not,B], '-'), wrt([B], '-'), assert(prf(A,'-')), assert(prf(B,'-')).
proof(A, 'V', B, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A], '-'), wrt([B], '-'), assert(prf(A,'-')), assert(prf(B,'-')).
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '-'):- wrt([not,not,A], '-'), wrt([not,not,B], '-'), wrt([not,not,C], '-'), wrt([A], '-'), wrt([B], '-'), wrt([C], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C, '-'):- C\=atm(not,atm(not,_)), wrt([not,not,A], '-'), wrt([not,not,B], '-'), wrt([C], '-'), wrt([A], '-'), wrt([B], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).
proof(atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C)), '-'):- B\=atm(not,atm(not,_)), wrt([not,not,A], '-'), wrt([B], '-'), wrt([not,not,C], '-'), wrt([A], '-'), wrt([C], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).
proof(A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), wrt([A], '-'), wrt([not,not,B], '-'), wrt([not,not,C], '-'), wrt([B], '-'), wrt([C], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).
proof(atm(not,atm(not,A)), 'V', B, 'V', C, '-'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([not,not,A], '-'), wrt([B], '-'), wrt([C], '-'), wrt([A], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).
proof(A, 'V', atm(not,atm(not,B)), 'V', C, '-'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A], '-'), wrt([not,not,B], '-'), wrt([C], '-'), wrt([B], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).
proof(A, 'V', B, 'V', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A], '-'), wrt([B], '-'), wrt([not,not,C], '-'), wrt([C], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).
proof(A, 'V', B, 'V', C, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A], '-'), wrt([B], '-'), wrt([C], '-'), assert(prf(A,'-')), assert(prf(B,'-')), assert(prf(C,'-')).


%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%
%%proof(AVB+) 
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), '+'):- ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), wrt([not,not,B], '+'), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).
proof(atm(not,atm(not,A)), 'V', B, '+'):- B\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).
proof(A, 'V', atm(not,atm(not,B)), '+'):- A\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), wrt([not,not,B], '+'), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).
proof(A, 'V', B, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).

%%proof(AVBVC+)
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C, '+'):- C\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C)), '+'):- B\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), 'V', B, 'V', C, '+'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(A, 'V', atm(not,atm(not,B)), 'V', C, '+'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(A, 'V', B, 'V', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(A, 'V', B, 'V', C, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).

%%proof(A&B-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '-'):- ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), wrt([not,not,B], '-'), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).
proof(atm(not,atm(not,A)), '&', B, '-'):- B\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).
proof(A, '&', atm(not,atm(not,B)), '-'):- A\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), wrt([not,not,B], '-'), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).
proof(A, '&', B, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).

%%proof(A&B&C-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), wrt([not,not,C], '-'), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C, '-'):- C\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C)), '-'):- B\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), wrt([not,not,C], '-'), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), wrt([not,not,C], '-'), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), '&', B, '&', C, '-'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', atm(not,atm(not,B)), '&', C, '-'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', B, '&', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), wrt([not,not,C], '-'), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', B, '&', C, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%simplify prove{A&B+/-} prove{AVB+/-}
prove(['{', not,not,not, A, B, not,not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,atm(not,C))), S), prove(T, S).
prove(['{', not,not,not, A, B, not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not,not,not, A, B, not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,atm(not,A))), B, atm(not,C), S), prove(T, S).
prove(['{', not,not,not, A, B, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_),  proof(atm(not,atm(not,atm(not,A))), B, C, S), prove(T, S).
prove(['{', not,not, A, B, not,not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,A)), B, atm(not,atm(not,atm(not,C))), S), prove(T, S).
prove(['{', not,not, A, B, not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,A)), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not,not, A, B, not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,A)), B, atm(not,C), S), prove(T, S).
prove(['{', not,not, A, B, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_),  proof(atm(not,atm(not,A)), B, C, S), prove(T, S).
prove(['{', not, A, B, not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,A), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not, A, B, not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,A), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not, A, B, not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,A), B, atm(not,C), S), prove(T, S).
prove(['{', not, A, B, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_),  proof(atm(not,A), B, C, S), prove(T, S).
prove(['{', A, B, not,not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(A, B, atm(not,atm(not,atm(not,C))), S), prove(T, S).
prove(['{', A, B, not,not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(A, B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', A, B, not, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(A, B, atm(not,C), S), prove(T, S).
prove(['{', A, B, C, '}'|T], S):- A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), B\=not, B\=atm(not,_), proof(A, B, C, S), prove(T, S).
%%simplify prove{A&{B&C}+/-} prove{A&{BVC}+/-} prove{AV{B&C}+/-} prove{AV{BVC}+/-}
prove([not,not,H, S1, '{', not,H2, S2, not,H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', atm(not,H2), S2, atm(not,H3), '}'], S3), wrt([H], S3), prove(T,S3).
prove([not,not,H, S1, '{', not,H2, S2, H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', atm(not,H2), S2, H3, '}'], S3), wrt([H], S3), prove(T,S3).
prove([not,not,H, S1, '{', H2, S2, not,H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', H2, S2, atm(not,H3), '}'], S3), wrt([H], S3), prove(T,S3).
prove([not,not,H, S1, '{', H2, S2, H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', H2, S2, H3, '}'], S3), wrt([H], S3), prove(T,S3).
prove([not,H, S1, '{', not,H2, S2, not,H3, '}'|T], S3):- prove([atm(not,H), S1, '{', atm(not,H2), S2, atm(not,H3), '}'|T], S3).
prove([not,H, S1, '{', not,H2, S2, H3, '}'|T], S3):- prove([atm(not,H), S1, '{', atm(not,H2), S2, H3, '}'|T], S3).
prove([not,H, S1, '{', H2, S2, not,H3, '}'|T], S3):- prove([atm(not,H), S1, '{', H2, S2, atm(not,H3), '}'|T], S3).
prove([not,H, S1, '{', H2, S2, H3, '}'|T], S3):- prove([atm(not,H), S1, '{', H2, S2, H3, '}'|T], S3).
prove([H, S1, '{', not,H2, S2, not,H3, '}'|T], S3):- prove([H, S1, '{', atm(not,H2), S2, atm(not,H3), '}'|T], S3).
prove([H, S1, '{', not,H2, S2, H3, '}'|T], S3):- prove([H, S1, '{', atm(not,H2), S2, H3, '}'|T], S3).
prove([H, S1, '{', H2, S2, not,H3, '}'|T], S3):- prove([H, S1, '{', H2, S2, atm(not,H3), '}'|T], S3).

prove([H, '&', '{', H2, '&', H3, '}'|T], '+'):- wrt([H],'+'), wrt(['{', H2, '&', H3, '}'], '+'), wrt([H2], '+'), wrt([H3], '+'), prove(T, '+').

prove([H, '&', '{', H2, 'V', H3, '}'|T], '+'):- wrt([H], '+'), wrt([H2,'V',H3], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), prove(T, '+').

prove([H, 'V', '{', H2, '&', H3, '}'|T], '-'):- wrt([H], '-'), wrt([H2,'&',H3], '-'), write("  /\\"), proof(H2, '&', H3, '-'), prove(T, '+').

prove([H, 'V', '{', H2, 'V', H3, '}'|T], '-'):- wrt([H], '-'), wrt(['{', H2, 'V', H3, '}'], '-'), wrt([H2], '-'), wrt([H3], '-'), prove(T, '-'). 


%%%%%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
prove([H, 'V', '{', H2, 'V', H3, '}'|T], '+'):- ( write("  /\\"), assert(prf(H, '+')), wrt([H], '+'), prove(T, '+') ) ; ( retract(prf(H, '+')), writeln("\\"), wrt([H2, 'V', H3], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), prove(T, '+') ).

%prove([H, '&', '{', H2, 'V', H3, '}'|T], '-'):- ( write("  /\\"), assert(prf(H, '-')), wrt([H], '-'), prove(T, '-') ) ; ( retract(prf(H, '-')), writeln("\\"), wrt([H2, 'V', H3], '-'), proof(H2, 'V', H3, '-'), prove(T, '-') ).

%prove([H, 'V', '{', H2, '&', H3, '}'|T], '+'):- ( write("  /\\"), assert(prf(H, '+')), wrt([H], '+'), prove(T, '+') ) ; ( retract(prf(H, '+')), writeln("\\"), wrt([H2, '&', H3], '+'), proof(H2, '&', H3, '+'), prove(T, '+') ).

prove([H, '&', '{', H2, '&', H3, '}'|T], '-'):- ( write("  /\\"), assert(prf(H, '-')), wrt([H], '-'), prove(T, '-') ) ; ( retract(prf(H, '-')), writeln("\\"), wrt([H2, '&', H3], '-'), write("  /\\"), proof(H2, '&', H3, '-'), prove(T, '-') ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%simplify prove{A&B+} prove{A&B-} prove{AVB+} prove{AVB-}
prove([not,not,not, H, S1, not,not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([not,not,not, H, S1, not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, atm(not,atm(not,H3))|T], S2).
prove([not,not,not, H, S1, not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, atm(not,H3)|T], S2).
prove([not,not,not, H, S1, H3|T], S2):- H3\='{', H3\=not,  T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, H3|T], S2).
prove([not,not, H, S1, not,not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([not,not, H, S1, not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H3))|T], S2).
prove([not,not, H, S1, not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, atm(not,H3)|T], S2).
prove([not,not, H, S1, H3|T], S2):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, H3|T], S2).
prove([not, H, S1 ,not,not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([not, H, S1 ,not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, atm(not,atm(not,H3))|T], S2).
prove([not, H, S1,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, atm(not,H3)|T], S2).
prove([not, H, S1 , H3|T], S2):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, H3|T], S2).
prove([H, S1, not,not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([H, S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([H, S1, not,not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([H, S1, atm(not,atm(not,H3))|T], S2).
prove([H, S1, not, H3|T], S2):- H3\=not, T\=['&'|_], T\=['V'|_], prove([H, S1, atm(not,H3)|T], S2).

%%prove(A&B+)
prove([H,'&',H3|T], '+'):- H3\='{', T\=['&'|_], T\=['V'|_],  wrt([H, '&', H3], '+'), proof(H, '&', H3, '+'), prove(T, '+').
%%prove(AVB+)
prove([H,'V',H3|T], '+'):- H3\='{', T\=['&'|_], T\=['V'|_], wrt([H,'V',H3|T], '+'), write("  /\\"), proof(H, 'V', H3, '+'), prove(T, '+').
%%prove(A&B-)
prove([H,'&',H3|T], '-'):- H3\='{', T\=['&'|_], T\=['V'|_], wrt([H,'&',H3|T], '-'), write("  /\\"), proof(H, '&', H3, '-'), prove(T, '-').
%%prove(AVB-)
prove([H,'V',H3|T], '-'):- H3\='{', T\=['&'|_], T\=['V'|_],  wrt([H, 'V', H3], '-'), proof(H, 'V', H3, '-'), prove(T, '-').

%%simplify prove{A&B&C+} prove{A&B&C-} prove{AVBVC+} prove{AVBVC-}
prove([not,not, H, S1, not,not, H2, S2, not,not, H3|T], S3):- H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H2)), S2, atm(not,atm(not,H3))|T], S3).
prove([not,not, H, S1, not,not, H2, S2, not, H3|T], S3):- H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H2)), S2, atm(not,H3)|T], S3).
prove([not,not, H, S1, not,not, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H2)), S2, H3|T], S3).
prove([not,not, H, S1, not, H2, S2, not,not, H3|T], S3):- H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,H2), S2, atm(not,atm(not,H3))|T], S3).
prove([not,not, H, S1, not, H2, S2, not, H3|T], S3):- H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,H2), S2, atm(not,H3)|T], S3).
prove([not,not, H, S1, not, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([atm(not,atm(not,H)), S1, atm(not,H2), S2, H3|T], S3).
prove([not,not, H, S1, H2, S2, not,not, H3|T], S3):- H3\=not, prove([atm(not,atm(not,H)), S1, H2, S2, atm(not,atm(not,H3))|T], S3).
prove([not,not, H, S1, H2, S2, not, H3|T], S3):- H3\=not, prove([atm(not,atm(not,H)), S1, H2, S2, atm(not,H3)|T], S3).
prove([not,not, H, S1, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([atm(not,atm(not,H)), S1, H2, S2, H3|T], S3).
prove([not, H, S1, not,not, H2, S2, not,not, H3|T], S3):- H3\=not, prove([atm(not,H), S1, atm(not,atm(not,H2)), S2, atm(not,atm(not,H3))|T], S3).
prove([not, H, S1, not,not, H2, S2, not, H3|T], S3):- H3\=not, prove([atm(not,H), S1, atm(not,atm(not,H2)), S2, atm(not,H3)|T], S3).
prove([not, H, S1, not,not, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([atm(not,H), S1, atm(not,atm(not,H2)), S2, H3|T], S3).
prove([not, H, S1, not, H2, S2, not,not, H3|T], S3):- H3\=not, prove([atm(not,H), S1, atm(not,H2), S2, atm(not,atm(not,H3))|T], S3).
prove([not, H, S1, not, H2, S2, not, H3|T], S3):- H3\=not, prove([atm(not,H), S1, atm(not,H2), S2, atm(not,H3)|T], S3).
prove([not, H, S1, not, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([atm(not,H), S1, atm(not,H2), S2, H3|T], S3).
prove([not, H, S1, H2, S2, not,not, H3|T], S3):- H3\=not, prove([atm(not,H), S1, H2, S2, atm(not,atm(not,H3))|T], S3).
prove([not, H, S1, H2, S2, not, H3|T], S3):- H3\=not, prove([atm(not,H), S1, H2, S2, atm(not,H3)|T], S3).
prove([not, H, S1, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([atm(not,H), S1, H2, S2, H3|T], S3).
prove([H, S1, not,not, H2, S2, not,not, H3|T], S3):- H3\=not, prove([H, S1, atm(not,atm(not,H2)), S2, atm(not,atm(not,H3))|T], S3).
prove([H, S1, not,not, H2, S2, not, H3|T], S3):- H3\=not, prove([H, S1, atm(not,atm(not,H2)), S2, atm(not,H3)|T], S3).
prove([H, S1, not,not, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([H, S1, atm(not,atm(not,H2)), S2, H3|T], S3).
prove([H, S1, not, H2, S2, not,not, H3|T], S3):- H3\=not, prove([H, S1, atm(not,H2), S2, atm(not,atm(not,H3))|T], S3).
prove([H, S1, not, H2, S2, not, H3|T], S3):- H3\=not, prove([H, S1, atm(not,H2), S2, atm(not,H3)|T], S3).
prove([H, S1, not, H2, S2, H3|T], S3):- H3\=not, H3\='V', H3\='&', prove([H, S1, atm(not,H2), S2, H3|T], S3).
prove([H, S1, H2, S2, not,not, H3|T], S3):- H3\=not, prove([H, S1, H2, S2, atm(not,atm(not,H3))|T], S3).
prove([H, S1, H2, S2, not, H3|T], S3):- H3\=not, prove([H, S1, H2, S2, atm(not,H3)|T], S3).

%%prove(A&B&C+)
prove([H,'&',H2,'&',H3|T], '+'):- H3\='{', wrt([H,'&',H2,'&',H3], '+'), proof(H, '&', H2, '&', H3, '+'), prove(T, '+').
%%prove(AVBVC+)
prove([H,'V',H2,'V',H3|T], '+'):- H3\='{', wrt([H,'V',H2,'V',H3], '+'), write("  /\\"), proof(H, 'V', H2, 'V', H3, '+'), prove(T, '+').
%%prove(A&B&C-)
prove([H,'&',H2,'&',H3|T], '-'):- H3\='{', wrt([H,'&',H2,'&',H3], '-'), write("  /\\"), proof(H, '&', H2, '&', H3, '-'), prove(T, '-').
%%prove(AVBVC-)
prove([H,'V',H2,'V',H3|T], '-'):- H3\='{', wrt([H,'V',H2,'V',H3], '-'), proof(H, 'V', H2, 'V', H3, '-'), prove(T, '-').

prove(['{', H, '&', H2, '}', '&', H3|T], S):- wrt(['{', H, '&', H2, '}', '&', H3], S), prove([H, '&', H2, '&', H3|T], S).
prove(['{', H, 'V', H2, '}', 'V', H3|T], S):- wrt(['{', H, 'V', H2, '}', 'V', H3], S), prove([H, 'V', H2, 'V', H3|T], S).
prove(['{', H, '&', H2, '}', 'V', H3|T], '+'):- wrt(['{', H, '&', H2, '}', 'V', H3], '+'), prove([H3, 'V', '{', H, '&', H2, '}'|T], '+').  
prove(['{', H, 'V', H2, '}', '&', H3|T], '+'):- wrt(['{', H, 'V', H2, '}', '&', H3], '+'), prove([H3, '&', '{', H, 'V', H2, '}'|T], '+').
prove(['{', H, '&', H2, '}', 'V', H3|T], '-'):- wrt(['{', H, '&', H2, '}', 'V', H3], '-'), prove([H3, 'V', '{', H, '&', H2, '}'|T], '-').
prove(['{', H, 'V', H2, '}', '&', H3|T], '-'):- wrt(['{', H, 'V', H2, '}', '&', H3], '-'), prove([H3, '&', '{', H, 'V', H2, '}'|T], '-').

%%simplify notnot{A&B+/-} notnot{AVB+/-}
prove([not,not, '{', not,not,H, AO, not,not,H2, '}'|T], S):- prove([not,not, '{', atm(not,atm(not,H)), AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not,not, '{', not,not,H, AO, not,H2, '}'|T], S):- prove([not,not, '{', atm(not,atm(not,H)), AO, atm(not,H2), '}'|T], S).
prove([not,not, '{', not,not,H, AO, H2, '}'|T], S):- prove([not,not, '{', atm(not,atm(not,H)), AO, H2, '}'|T], S).
prove([not,not, '{', not,H, AO, not,not,H2, '}'|T], S):- prove([not,not, '{', atm(not,H), AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not,not, '{', not,H, AO, not,H2, '}'|T], S):- prove([not,not, '{', atm(not,H), AO, atm(not,H2), '}'|T], S).
prove([not,not, '{', not,H, AO, H2, '}'|T], S):- prove([not,not, '{', atm(not,H), AO, H2, '}'|T], S).
prove([not,not, '{', H, AO, not,not,H2, '}'|T], S):- prove([not,not, '{', H, AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not,not, '{', H, AO, not,H2, '}'|T], S):- prove([not,not, '{', H, AO, atm(not,H2), '}'|T], S).
%%simplify not{A&B+/-} not{AVB+/-}
prove([not, '{', not,not,H, AO, not,not,H2, '}'|T], S):- prove([not, '{', atm(not,atm(not,H)), AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not, '{', not,not,H, AO, not,H2, '}'|T], S):- prove([not, '{', atm(not,atm(not,H)), AO, atm(not,H2), '}'|T], S).
prove([not, '{', not,not,H, AO, H2, '}'|T], S):- prove([not, '{', atm(not,atm(not,H)), AO, H2, '}'|T], S).
prove([not, '{', not,H, AO, not,not,H2, '}'|T], S):- prove([not, '{', atm(not,H), AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not, '{', not,H, AO, not,H2, '}'|T], S):- prove([not, '{', atm(not,H), AO, atm(not,H2), '}'|T], S).
prove([not, '{', not,H, AO, H2, '}'|T], S):- prove([not, '{', atm(not,H), AO, H2, '}'|T], S).
prove([not, '{', H, AO, not,not,H2, '}'|T], S):- prove([not, '{', H, AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not, '{', H, AO, not,H2, '}'|T], S):- prove([not, '{', H, AO, atm(not,H2), '}'|T], S).

prove([not,not, '{', H, '&', H2, '}'|T], '+'):- wrt([not,not, '{', H, '&', H2, '}'], '+'), wrt([H,'&',H2],'+'), proof(H, '&', H2, '+'), prove(T, '+').
prove([not, '{', H, '&', H2, '}'|T], '+'):- wrt([not, '{', H, '&', H2, '}'], '+'), wrt([not,H,'V',not,H2], '+'), write("  /\\"), proof(atm(not, H), 'V', atm(not, H2), '+'), prove(T, '+').

prove([not,not, '{', H, 'V', H2, '}'|T], '+'):- wrt([not,not, '{', H, 'V', H2, '}'], '+'), wrt([H,'V',H2], '+'), proof(H, 'V', H2, '+'), prove(T, '+').
prove([not, '{', H, 'V', H2, '}'|T], '+'):- wrt([not, '{', H, 'V', H2, '}'], '+'), wrt([atm(not,H),'&',atm(not,H2)], '+'), proof(atm(not, H), '&', atm(not, H2), '+'), prove(T, '+').

prove([not,not, '{', H, '&', H2, '}'|T], '-'):- wrt([not,not, '{', H, '&', H2, '}'], '-'), wrt([H,'&',H2], '-'), proof(H, '&', H2, '-'), prove(T, '-').
prove([not, '{', H, '&', H2, '}'|T], '-'):- wrt([not, '{', H, '&', H2, '}'], '-'), wrt([atm(not,H),'V',atm(not,H2)], '-'), proof(atm(not, H), 'V', atm(not, H2), '-'), prove(T, '-').

prove([not,not, '{', H, 'V', H2, '}'|T], '-'):- wrt([not,not, '{', H, 'V', H2, '}'], '-'), wrt([H,'V',H2], '-'), proof(H, 'V', H2, '-'), prove(T, '-').
prove([not, '{', H, 'V', H2, '}'|T], '-'):- wrt([not, '{', H, 'V', H2, '}'], '-'), wrt([atm(not,H),'&',atm(not,H2)], '-'), write("  /\\"), proof(atm(not, H), '&', atm(not, H2), '-'), prove(T, '-').

