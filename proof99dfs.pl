:- dynamic prf(_,_).
:- discontiguous proof/6.
:- discontiguous proof/4.
:- discontiguous toprove/2.
:- discontiguous prove/2.
:- discontiguous finprove/2.
:- dynamic toprove/2.

ass([]).
ass([not, not, H|T]):- wrt([not, not, H|T], '+'), ass([H|T]).
ass([not, H|T]):- H\=not, T\=['V'|_], T\=['&'|_], assert(prf(atm(not,H),'+')), write("not"), write(H), writeln(",+"), ass(T).

ass(['{', not, A, '&', not, C, '}'|T]):- wrt(['{',atm(not,A),'&',atm(not,C),'}'], '+'), ass(T), prove([atm(not,A), '&', atm(not,C)], '+').
ass(['{', atm(not,A), '&', C, '}'|T]):- C\=not, wrt(['{',atm(not,A),'&',C,'}'], '+'), ass(T), prove([atm(not,A), '&', C], '+').
ass(['{', A, '&', atm(not,C), '}'|T]):- wrt(['{',A,'&',atm(not,C),'}'], '+'), ass(T), prove([A, '&', atm(not,C)], '+').
ass(['{', A, '&', C, '}'|T]):- C\=not, wrt(['{',A,'&',C,'}'], '+'), ass(T), prove([A, '&', C], '+').


ass(['{', not, A, 'V', not, C, '}'|T]):- wrt(['{',atm(not,A),'V',atm(not,C),'}'], '+'), ass(T), assert(toprove([atm(not,A), 'V', atm(not,C)], '+')).
ass(['{', not, A, 'V', C, '}'|T]):- C\=not, wrt(['{',atm(not,A),'V',C,'}'], '+'), ass(T), assert(toprove([atm(not,A), 'V', C], '+')).
ass(['{', A, 'V', not, C, '}'|T]):- C\=not, wrt(['{',A,'V',atm(not,C),'}'], '+'), ass(T), assert(toprove([A, 'V', atm(not,C)], '+')).
ass(['{', A, 'V', C, '}'|T]):- C\=not, wrt(['{',A,'V',C,'}'], '+'), ass(T), prove([A, 'V', C], '+').


ass([not, A, '&', not, C|T]):- wrt([atm(not,A),'&',atm(not,C)], '+'), ass(T), prove([atm(not,A), '&', atm(not,C)], '+').
ass([not, A, '&', C|T]):- C\=not, wrt([atm(not,A),'&',C], '+'), ass(T), prove([atm(not,A), '&', C], '+').
ass([A, '&', not, C|T]):- C\=not, wrt([A,'&',atm(not,C)], '+'), ass(T), prove([A, '&', atm(not,C)], '+').
ass([A, '&', C|T]):- C\=not, wrt([A,'&',C], '+'), ass(T), prove([A, '&', C], '+').


%%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%
%ass([not, A, 'V', not, not, not, C|T]):-
%ass([not, A, 'V', not, not, C|T]):-
%ass([not, A, 'V', not, C|T]):-
%ass([not, A, 'V', C|T]):- 
%ass([A, 'V', not, C|T]):- 
%ass([A, 'V', C|T]):- 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



ass([H|T]):- H\=not, T\=['V'|_], T\=['&'|_], assert(prf(H, '+')), write(H), writeln(",+"), ass(T).

printList([], _) :- nl.
printList([H|T], '+') :- write(H), write(',+'), write(' | '), printList(T, '+').
printList([H|T], '-') :- write(H), write(',-'), write(' | '), printList(T, '-').

prepareAnswer:- findall(Y, prf(Y, '+'), PL), findall(X, prf(X, '-'), NL), 
    	write('positive literals: '), nl, write("|"), printList(PL, '+'), 
    	write('negative literals: '), nl, write("|"), printList(NL, '-').

wrt([],S):- write(","), writeln(S).
wrt([atm(not,A)|T],S):- write("not"), write(A), wrt(T,S).
wrt([H|T],S):- H\=atm(not,_), write(H), wrt(T,S).

prove(A, '|', C):- ass(A), C\=[_], C\=[not,_], wrt(C, '-'), nl, prove(C, '-'), findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP),  check(TP, FP).
prove(A, '|', C):- ass(A), C=[_], wrt(C, '-'), nl, findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP),  check(TP, FP).
prove(A, '|', C):- ass(A), C=[not,_], wrt(C, '-'), nl, findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP),  check(TP, FP).

check(TP, FP):- TP\=[], FP\=[], write("//"), finprove(TP, '+'), finprove(FP, '-'), retractall(toprove(_,_)).% prepareAnswer.
check(TP, []):- TP\=[], write("//"), finprove(TP, '+'), retractall(toprove(_,_)).% prepareAnswer.
check([], FP):- FP\=[], write("//"), finprove(FP, '-'), retractall(toprove(_,_)).% prepareAnswer.
check([], []).% prepareAnswer.

finprove([], _).


proof(A, '&', B, '+'):- prf(A, '+'), nl, prf(B, '+'), nl.
proof(A, '&', B, '&', C, '+'):- prf(A, '+'), nl, prf(B, '+'), nl, prf(C, '+'), nl.
proof(A, 'V', B, '-'):- prf(A, '-'), nl, prf(B, '-'), nl.
proof(A, 'V', B, 'V', C, '-'):- prf(A, '-'), nl, prf(B, '-'), nl, prf(C, '-'), nl.

proof(atm(not, A), '+'):- prf(atm(not,A), '+').

proof(atm(not, A), '-'):- prf(atm(not,A), '-').


%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%
proof(A, 'V', B, '+'):- ( prf(A, '+'), write(A), writeln(",+") ); retract(prf(A, '+')), writeln("\\"), prf(B, '+'), write(B), writeln(",+").
proof(A, '&', B, '-'):- ( prf(A, '-'), write(A), writeln(",-") ); retract(prf(A, '-')), writeln("\\"), prf(B, '-'), write(B), writeln(",-").

%proof(A, 'V', B, '+'):- .
%proof(A, 'V', B, 'V', C, '+'):- .
%proof(A, '&', B, '-'):- .
%proof(A, '&', B, '&', C, '-'):- .
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


finprove([[H]|[]], S):- finprove(H, S).
prove([H|[]], S):- H\=[_], prf([H], S).
prove([], _).
prove(['{', not, A, B, not, C, '}'|T], S):- proof([atm(not,A), B, atm(not,C)], S), prove(T, S).
prove(['{', not, A, B, C, '}'|T], S):- C\=not, proof([atm(not,A), B, C], S), prove(T, S).
prove(['{', A, B, not, C, '}'|T], S):- proof([A, B, atm(not,C)], S), prove(T, S).
prove(['{', A, B, C, '}'|T], S):- B\=not, proof(A, B, C, S), prove(T, S).


prove([H, '&', '{', H2, '&', H3, '}'|T], '+'):- prf(H,'+'), nl, prf(H2, '+'), nl, prf(H3, '+'), nl, prove(T, '+').

prove([H, '&', '{', H2, 'V', H3, '}'|T], '+'):- prf(H, '+'), nl, write(H2), write("V"), write(H3), write(", +"), nl, proof(H2, 'V', H3, '+'), nl, prove(T, '+').

prove([H, 'V', '{', H2, '&', H3, '}'|T], '-'):- prf(H, '-'), nl, write(H2), write("&"), write(H3), write(", -"), nl, proof(H2, '&', H3, '-'), nl, prove(T, '+').

prove([H, 'V', '{', H2, 'V', H3, '}'|T], '-'):- prf(H, '-'), nl, prf(H2, '-'), nl, prf(H3, '-'), nl, prove(T, '-'). 


%%%%%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%prove([H, 'V', '{', H2, 'V', H3, '}'|T], '+'):-.
%prove([H, '&', '{', H2, 'V', H3, '}'|T], '-'):-.
%prove([H, 'V', '{', H2, '&', H3, '}'|T], '+'):-.
%prove([H, '&', '{', H2, '&', H3, '}'|T], '-'):-.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


prove([not,H,'&',not,not,not,H3|T], '+'):- wrt([atm(not,H), '&', atm(not,atm(not,atm(not,H3)))|T], '+'), proof(atm(not,H), '&', atm(not,atm(not,atm(not,H3))), '+'), prove(T, '+').
prove([not,H,'&',not,not,H3|T], '+'):- H3\=not, wrt([atm(not,H), '&', atm(not,atm(not,H3))|T], '+'), proof(atm(not,H), '&', atm(not,atm(not,H3)), '+'), prove(T, '+').
prove([not,H,'&',not,H3|T], '+'):-H3\=not, proof(atm(not,H), '&', atm(not,H3), '+'), prove(T, '+').
prove([not,H,'&',H3|T], '+'):- H3\=not, proof(atm(not,H), '&', H3, '+'), prove(T, '+').
prove([H,'&',not, not, not, H3|T], '+'):- wrt([H, '&', atm(not,atm(not,atm(not,H3)))|T], '+'), proof(H, '&', atm(not,atm(not,atm(not,H3)), '+'), prove(T, '+').
prove([H,'&',not, not, H3|T], '+'):- H3\=not, wrt([H, '&', atm(not,atm(not,H3))|T], '+'), proof(H, '&', atm(not,atm(not,H3)), '+'), prove(T, '+').
prove([H,'&',not, H3|T], '+'):- H3\=not, proof(H, '&', atm(not,H3), '+'), prove(T, '+').
prove([H,'&',H3|T], '+'):- H3\=not, proof(H, '&', H3, '+'), prove(T, '+').


%%%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%prove([not, H,'V', not,not,not, H3|T], '+'):- 
%prove([not, H,'V', not,not, H3|T], '+'):- 
%prove([not, H,'V', not, H3|T], '+'):- 
%prove([not, H,'V',H3|T], '+'):- 
%prove([H,'V', not, not, not, H3|T], '+'):- 
%prove([H,'V', not, not, H3|T], '+'):- 
%prove([H,'V', not, H3|T], '+'):- 
%prove([H,'V',H3|T], '+'):- 

%prove([not, H,'&', not,not,not, H3|T], '-'):- 
%prove([not, H,'&', not,not, H3|T], '-'):- 
%prove([not, H,'&', not, H3|T], '-'):- 
%prove([not, H,'&',H3|T], '-'):- 
%prove([H,'&', not, not, not, H3|T], '-'):- 
%prove([H,'&', not, not, H3|T], '-'):- 
%prove([H,'&', not, H3|T], '-'):- 
%prove([H,'&',H3|T], '-'):-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


prove([not, H,'V', not,not,not, H3|T], '-'):- wrt([atm(not,H), 'V', atm(not,atm(not,atm(not,H3)))|T], '-'), proof(atm(not,H), 'V', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').
prove([not, H,'V', not,not, H3|T], '-'):- H3\=not, wrt([not, H, 'V', atm(not,atm(not,H3))|T], '-'), proof(atm(not,H), 'V', atm(not,atm(not,H3)), '-'), prove(T, '-').
prove([not, H,'V', not, H3|T], '-'):- H3\=not, proof(atm(not,H), 'V', atm(not,H3), '-'), prove(T, '-').
prove([not, H,'V',H3|T], '-'):- H3\=not, proof(atm(not,H), 'V', H3, '-'), prove(T, '-').
prove([H,'V', not,not,not, H3|T], '-'):- wrt([H, 'V', atm(not,atm(not,atm(not,H3)))|T], '-'), proof(H, 'V', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').
prove([H,'V', not,not, H3|T], '-'):- H3\=not, wrt([H, 'V', atm(not,atm(not,H3))|T], '-'), proof(H, 'V', atm(not,atm(not,H3)), '-'), prove(T, '-').
prove([H,'V', not, H3|T], '-'):- H3\=not, proof(H, 'V', atm(not,H3), '-'), prove(T, '-').
prove([H,'V', H3|T], '-'):- H3\=not, proof(H, 'V', H3, '-'), prove(T, '-').

%%%%%%%%%%%%%%%%%%%%%%?????????????????%%%%%%%%%%%%%%%%%%%%
prove(['{', H, '&', H2, '}', '&', H3|T], S):- prove([H, '&', '{', H2, '&', H3, '}'|T], S).
prove(['{', H, 'V', H2, '}', 'V', H3|T], S):- prove([H, 'V', '{', H2, 'V', H3, '}'|T], S).
prove(['{', H, '&', H2, '}', 'V', H3|T], '+'):- prove([H, '&', H2|T], '+'), write("     OR   "), prf(H3, '+'), prove(T, '+').  
%prove(['{', H, 'V', H2, '}', '&', H3|T], '+'):-.
%prove(['{', H, '&', H2, '}', 'V', H3|T], '-'):-.
%prove(['{', H, 'V', H2, '}', '&', H3|T], '-'):-.
%prove([not, H|T], '+'):-proof(atm(not,H), '+'), prove(T, '+').
%prove([not, H|T], '-'):-proof(atm(not,H), '-'), prove(T, '-').


prove([not, '{', H, '&', H2, '}'|T], '+'):- write("not"), write(H), write(" V not"), write(H2), writeln(", +"), proof(atm(not, H), 'V', atm(not, H2), '+'), prove(T, '+').

prove([not, '{', H, 'V', H2, '}'|T], '+'):- write("not"), write(H), write(" & not"), write(H2), writeln(", +"), 
proof(atm(not, H), '&', atm(not, H2), '+'), prove(T, '+').

prove([not, '{', H, '&', H2, '}'|T], '-'):- write("not"), write(H), write(" V not"), write(H2), writeln(", -"), proof(atm(not, H), 'V', atm(not, H2), '-'), prove(T, '-').

prove([not, '{', H, 'V', H2, '}'|T], '-'):- write("not"), 
write(H), write(" & not"), write(H2), writeln(", -"), proof(atm(not, H), '&', atm(not, H2), '-'), prove(T, '-').


prove([not, not, not, A], S):- wrt([not,A],S).
prove([not, not, A], S):- wrt(A,S). 
prove([not, A], S):- wrt(A,S).
prove([atm(not,(atm(not,A)))],S):-prove(A,S).

prove([not, H|T], S):- H\=not, T\=['&'|_], T\=['V'|_], proof(atm(not, H), S), prove(T, S).


prf(atm(not,A), S):- write("not"), write(A), write(","), write(S). 
prf([],S):- write(","), writeln(S).
prf([atm(not,A)|T], S):- write("not"), write(A), prf(T, S). 
prf([H|T], S):- H\=atm(not,_), H\=[], H\=[_], write(H), prf(T, S).%%_
prf(A,S):- A\=[], A\=[_], A\= atm(not,_), A\=[_|_], write(A), write(","), write(S).%%_


%hoe zinnen (antecedents) uit te breiden A&B&C (A&B)VC......
%hoe met 1 atom als inference, dan printie 2x
%hoe met inferences uit te breiden

