:- dynamic prf(_,_).
:- dynamic assprove(_,_).
:- dynamic toprove/2.
:- discontiguous proof/6.
:- discontiguous proof/4.
:- discontiguous toprove/2.
:- discontiguous prove/2.
:- discontiguous finprove/2.


%%%%%%%%-als-prf-(notnot-iets-notnot)-dan-nog-niet-2e-lijn-indent-van-de-notnot-weggehaald------en-A\=atm(not...)
%%%%%%%%-prf-functie-nakijken-op-atm(not,atm(not-----en-nl
%%%%%%%%-na-topove_assert-ook-retract-en-opnieuw
%%%%%%%%-bij-alle-begin_assert(toprove())-nog-wrt()-vooraan
%%%%%%%%-kijken-of-alle-toprove()-wel-een-daadwerkelijke-oplossing-maken-of-weer-terug-naar-assert(toprove)
%%%%%%%%-wrt(not)VSwrt(atm(not,)
%%%%%%%%-assprove(notnot...?




ass([]).
ass([not, not, not, H]):- wrt([not, not, not, H], '+'), assert(assprove([not,not,not,H],'+')).  
ass([not, not, H]):- wrt([not, not, H], '+'), assert(assprove([not,not,H],'+')).
ass([not, H]):- wrt([atm(not,H)], '+'), assert(prf(atm(not,H),'+')).

%%ass{A&B}
ass(['{', not, not, A, '&', not, not, C, '}'|T]):- wrt(['{',atm(not,atm(not,A)),'&',atm(not,atm(not,C)),'}'], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), '&', atm(not,atm(not,C))], '+')).
ass(['{', not, not, A, '&', not, C, '}'|T]):- wrt(['{',atm(not,atm(not,A)),'&',atm(not,C),'}'], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), '&', atm(not,C)], '+')).
ass(['{', not, not, A, '&', C, '}'|T]):- wrt(['{',atm(not,atm(not,A)),'&',C,'}'], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), '&', C], '+')).
ass(['{', not, A, '&', not, not, C, '}'|T]):- wrt(['{',atm(not,A),'&',atm(not,atm(not,C)),'}'], '+'), ass(T), assert(assprove([atm(not,A), '&', atm(not,atm(not,C))], '+')).
ass(['{', not, A, '&', not, C, '}'|T]):- wrt(['{',atm(not,A),'&',atm(not,C),'}'], '+'), ass(T), assert(assprove([atm(not,A), '&', atm(not,C)], '+')).
ass(['{', not, A, '&', C, '}'|T]):- wrt(['{',atm(not,A),'&',C,'}'], '+'), ass(T), assert(assprove([atm(not,A), '&', C], '+')).
ass(['{', A, '&', not, not, C, '}'|T]):- wrt(['{',A,'&',atm(not,atm(not,C)),'}'], '+'), ass(T), assert(assprove([A, '&', atm(not,atm(not,C))], '+')).
ass(['{', A, '&', not, C, '}'|T]):- wrt(['{',A,'&',atm(not,C),'}'], '+'), ass(T), assert(assprove([A, '&', atm(not,C)], '+')).
ass(['{', A, '&', C, '}'|T]):- C\=not, wrt(['{',A,'&',C,'}'], '+'), ass(T), assert(assprove([A, '&', C], '+')).

%%assA&B
ass([not,not, A, '&', not,not, C|T]):- wrt([atm(not,atm(not,A)),'&',atm(not,atm(not,C))], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), '&', atm(not,atm(not,C))], '+')).
ass([not,not, A, '&', not, C|T]):- wrt([atm(not,atm(not,A)),'&',atm(not,C)], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), '&', atm(not,C)], '+')).
ass([not,not, A, '&', C|T]):- C\=not, wrt([atm(not,atm(not,A)),'&',C], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), '&', C], '+')).
ass([not, A, '&', not,not, C|T]):- wrt([atm(not,A),'&',atm(not,atm(not,C))], '+'), ass(T), assert(assprove([atm(not,A), '&', atm(not,atm(not,C))], '+')).
ass([not, A, '&', not, C|T]):- wrt([atm(not,A),'&',atm(not,C)], '+'), ass(T), assert(assprove([atm(not,A), '&', atm(not,C)], '+')).
ass([not, A, '&', C|T]):- C\=not, wrt([atm(not,A),'&',C], '+'), ass(T), assert(assprove([atm(not,A), '&', C], '+')).
ass([A, '&', not,not, C|T]):- C\=not, wrt([A,'&',atm(not,atm(not,C))], '+'), ass(T), assert(assprove([A, '&', atm(not,atm(not,C))], '+')).
ass([A, '&', not, C|T]):- C\=not, wrt([A,'&',atm(not,C)], '+'), ass(T), assert(assprove([A, '&', atm(not,C)], '+')).
ass([A, '&', C|T]):- C\=not, wrt([A,'&',C], '+'), ass(T), assert(assprove([A, '&', C], '+')).

%%ass{AVB}
ass(['{', not,not, A, 'V', not,not, C, '}'|T]):- wrt(['{',atm(not,atm(not,A)),'V',atm(not,atm(not,C)),'}'], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,C))], '+')).
ass(['{', not,not, A, 'V', not, C, '}'|T]):- wrt(['{',atm(not,atm(not,A)),'V',atm(not,C),'}'], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), 'V', atm(not,C)], '+')).
ass(['{', not,not, A, 'V', C, '}'|T]):- C\=not, wrt(['{',atm(not,atm(not,A)),'V',C,'}'], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), 'V', C], '+')).
ass(['{', not, A, 'V', not,not, C, '}'|T]):- wrt(['{',atm(not,A),'V',atm(not,atm(not,C)),'}'], '+'), ass(T), assert(assprove([atm(not,A), 'V', atm(not,atm(not,C))], '+')).
ass(['{', not, A, 'V', not, C, '}'|T]):- wrt(['{',atm(not,A),'V',atm(not,C),'}'], '+'), ass(T), assert(assprove([atm(not,A), 'V', atm(not,C)], '+')).
ass(['{', not, A, 'V', C, '}'|T]):- C\=not, wrt(['{',atm(not,A),'V',C,'}'], '+'), ass(T), assert(assprove([atm(not,A), 'V', C], '+')).
ass(['{', A, 'V', not,not, C, '}'|T]):- C\=not, wrt(['{',A,'V',atm(not,atm(not,C)),'}'], '+'), ass(T), assert(assprove([A, 'V', atm(not,atm(not,C))], '+')).
ass(['{', A, 'V', not, C, '}'|T]):- C\=not, wrt(['{',A,'V',atm(not,C),'}'], '+'), ass(T), assert(assprove([A, 'V', atm(not,C)], '+')).
ass(['{', A, 'V', C, '}'|T]):- C\=not, wrt(['{',A,'V',C,'}'], '+'), ass(T), assert(assprove([A, 'V', C], '+')).

%%assertAVB
ass([not,not, A, 'V', not, not, not, C|T]):- wrt([atm(not,atm(not,A)),'V',atm(not,atm(not,atm(not,C)))], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,atm(not,C)))], '+')).
ass([not,not, A, 'V', not, not, C|T]):- C\=not, wrt([atm(not,atm(not,A)),'V',atm(not,atm(not,C))], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,C))], '+')).
ass([not,not, A, 'V', not, C|T]):- C\=not, wrt([atm(not,atm(not,A)),'V',atm(not,C)], '+'), ass(T), assert(assprove([atm(not,atm(not,A)), 'V', atm(not,C)], '+')).
ass([not, A, 'V', not, not, not, C|T]):- wrt([atm(not,A),'V',atm(not,atm(not,atm(not,C)))], '+'), ass(T), assert(assprove([atm(not,A), 'V', atm(not,atm(not,atm(not,C)))], '+')).
ass([not, A, 'V', not, not, C|T]):- C\=not, wrt([atm(not,A),'V',atm(not,atm(not,C))], '+'), ass(T), assert(assprove([atm(not,A), 'V', atm(not,atm(not,C))], '+')).
ass([not, A, 'V', not, C|T]):- C\=not, wrt([atm(not,A),'V',atm(not,C)], '+'), ass(T), assert(assprove([atm(not,A), 'V', atm(not,C)], '+')).
ass([not, A, 'V', C|T]):- C\=not, wrt([atm(not,A),'V',C], '+'), ass(T), assert(assprove([A, 'V', C], '+')).
ass([A, 'V', not,not,not, C|T]):- C\=not, wrt([A,'V',atm(not,atm(not,atm(not,C)))], '+'), ass(T), assert(assprove([A, 'V', atm(not,atm(not,atm(not,C)))], '+')).
ass([A, 'V', not,not, C|T]):- C\=not, wrt([A,'V',atm(not,atm(not,C))], '+'), ass(T), assert(assprove([A, 'V', atm(not,atm(not,C))], '+')).
ass([A, 'V', not, C|T]):- C\=not, wrt([A,'V',atm(not,C)], '+'), ass(T), assert(assprove([A, 'V', atm(not,C)], '+')).
ass([A, 'V', C|T]):- C\=not, wrt([A,'V',C], '+'), ass(T), assert(assprove([A, 'V', C], '+')).



printList([], _) :- nl.
printList([H|T], '+') :- write(H), write(',+'), write(' | '), printList(T, '+').
printList([H|T], '-') :- write(H), write(',-'), write(' | '), printList(T, '-').

prepareAnswer:- findall(Y, prf(Y, '+'), PL), findall(X, prf(X, '-'), NL), 
    	write('positive literals: '), nl, write("|"), printList(PL, '+'), 
    	write('negative literals: '), nl, write("|"), printList(NL, '-').

wrt([],S):- write(","), writeln(S).
wrt([atm(not,atm(not,atm(not,A)))|T],S):- write("notnotnot"), write(A), wrt(T,S).
wrt([atm(not,atm(not,A))|T],S):- A\=atm(not,_), write("notnot"), write(A), wrt(T,S).
wrt([atm(not,A)|T],S):- write("not"), write(A), wrt(T,S).
wrt([H|T],S):- H\=atm(not,_), write(H), wrt(T,S).


prove(A, '|', C):- C\=[_], C\=[not,_], ass(A), wrt(C, '-'), nl, findall([Z], assprove(Z, '+'), AS), check(AS), writeln("inferences solving:"), prove(C, '-'), findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP),  check(TP, FP).
prove(A, '|', C):- C=[_], ass(A), wrt(C, '-'), nl, findall([Z], assprove(Z, '+'), AS), check(AS), findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP),  check(TP, FP).
prove(A, '|', C):- C=[not,_], ass(A), wrt(C, '-'), nl, findall([Z], assprove(Z, '+'), AS), check(AS), findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP),  check(TP, FP).

check(TP, FP):- TP\=[], FP\=[], write("//"), finprove(TP, '+'), finprove(FP, '-'), retractall(toprove(_,_)).% prepareAnswer.
check(TP, []):- TP\=[], write("//"), finprove(TP, '+'), retractall(toprove(_,_)).% prepareAnswer.
check([], FP):- FP\=[], write("//"), finprove(FP, '-'), retractall(toprove(_,_)).% prepareAnswer.
check([], []).% prepareAnswer.

check([]).
check([[H]|T]):- H\=[[]], writeln("premises solving:"), prsolve([[H]|T]), nl.
prsolve([]).
prsolve([[H]|T]):- prove(H, '+'), prsolve(T).


%%proof(A&B+) proof(A&B&C+)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '+'):- wrt([not,not,A], '+'), wrt([not,not,B], '+'), wrt([A], '+'), wrt([B], '+').
proof(atm(not,atm(not,A)), '&', B, '+'):- wrt([not,not,B], '+'), wrt([B], '+'), wrt([A], '+'),.
proof(A, '&', atm(not,atm(not,B)), '+'):- wrt([A], '+'), wrt([not,not,B], '+'), wrt([B], '+').
proof(A, '&', B, '+'):- wrt([A], '+'), wrt([B], '+').
proof(atm(not,atm(not,A), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '+'):- wrt([not,not,A], '+'), wrt([not,not,B], '+'), wrt([not,not,C], '+')wrt([A], '+'), wrt([B], '+'), wrt([C], '+').
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C, '+'):- wrt([not,not,A], '+'), wrt([not,not,B], '+'), wrt([C], '+'), wrt([A], '+'), wrt([B], '+').
proof(atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C)), '+'):- wrt([not,not,A], '+'), wrt([B], '+'), wrt([not,not,C], '+'), wrt([A], '+'), wrt([C], '+').
proof(A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '+'):- wrt([A], '+'), wrt([not,not,B], '+'), wrt([C], '+'), wrt([B], '+').
proof(atm(not,atm(not,A)), '&', B, '&', C, '+'):- wrt([not,not,A], '+'), wrt([B], '+'), wrt([C], '+'), wrt([A], '+').
proof(A, '&', atm(not,atm(not,B)), '&', C, '+'):- wrt([A], '+'), wrt([not,not,B], '+'), wrt([C], '+'), wrt([B], '+').
proof(A, '&', B, '&', atm(not,atm(not,C)), '+'):- wrt([A], '+'), wrt([B], '+'), wrt([not,not,C], '+'), wrt([C], '+').
proof(A, '&', B, '&', C, '+'):- wrt([A], '+'), wrt([C], '+'), wrt([B], '+').

%%proof(AVB-) proof(AVBVC-)
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), '-'):- wrt([not,not,A], '-'), wrt([B], '-'), wrt([A], '-').
proof(atm(not,atm(not,A)), 'V', B, '-'):- wrt([not,not,A], '-'), wrt([B], '-'), wrt([A], '-').
proof(A, 'V', atm(not,atm(not,B)), '-'):- wrt([A], '-'), wrt([not,not,B], '-'), wrt([B], '-').
proof(A, 'V', B, '-'):- wrt([A], '-'), wrt([B], '-').
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '-'):- wrt([not,not,A], '-'), wrt([not,not,B], '-'), wrt([not,not,C], '-'), wrt([A], '-'), wrt([B], '-'), wrt([C], '-').
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C, '-'):- wrt([not,not,A], '-'), wrt([not,not,B], '-'), wrt([C], '-'), wrt([A], '-'), wrt([B], '-').
proof(atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C)), '-'):- wrt([not,not,A], '-'), wrt([B], '-'), wrt([not,not,C], '-'), wrt([A], '-'), wrt([C], '-').
proof(A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '-'):- wrt([A], '-'), wrt([not,not,B], '-'), wrt([not,not,C], '-'), wrt([B], '-'), wrt([C], '-').
proof(atm(not,atm(not,A)), 'V', B, 'V', C, '-'):- wrt([not,not,A], '-'), wrt([B], '-'), wrt([C], '-'), wrt([A], '-').
proof(A, 'V', atm(not,atm(not,B)), 'V', C, '-'):- wrt([A], '-'), wrt([not,not,B], '-'), wrt([C], '-'), wrt([B], '-').
proof(A, 'V', B, 'V', atm(not,atm(not,C)), '-'):- wrt([A], '-'), wrt([B], '-'), wrt([not,not,C], '-'), wrt([C], '-').
proof(A, 'V', B, 'V', C, '-'):- wrt([A], '-'), wrt([B], '-'), wrt([C], '-').

%%proof(AVB+) 
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), '+'):- wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B))], '+'), assert(toprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B))], '+')).
proof(atm(not,atm(not,A)), 'V', B, '+'):- wrt([atm(not,atm(not,A)), 'V', B], '+'), assert(toprove([atm(not,atm(not,A)), 'V', B], '+')).
proof(A, 'V', atm(not,atm(not,B)), '+'):- wrt([A, 'V', atm(not,atm(not,B))], '+'), assert(toprove([A, 'V', atm(not,atm(not,B))], '+')).
proof(A, 'V', B, '+'):- wrt([A, 'V', B], '+'), assert(toprove([A, 'V', B], '+')).
finprove([A, 'V', B], '+'):- prf(atm(not,atm(not,A)), '+'), write("   OR   "), prf(atm(not,atm(not,B)), '+'), nl.
finprove([A, 'V', B], '+'):- prf(atm(not,atm(not,A)), '+'), write("   OR   "), prf(B, '+'), nl.
finprove([A, 'V', B], '+'):- prf(A, '+'), write("   OR   "), prf(atm(not,atm(not,B)), '+'), nl.
finprove([A, 'V', B], '+'):- prf(A, '+'), write("   OR   "), prf(B, '+'), nl.

%%proof(AVBVC+)
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'), assert(toprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+')).
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C, '+'):- wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C], '+'), assert(toprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C], '+')).
proof(atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C)), '+'):- wrt([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))], '+'), assert(toprove([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))], '+')).
proof(A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- wrt([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'), assert(toprove([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+')).
proof(atm(not,atm(not,A)), 'V', B, 'V', C, '+'):- wrt([atm(not,atm(not,A)), 'V', B, 'V', C], '+'), assert(toprove([atm(not,atm(not,A)), 'V', B, 'V', C], '+')).
proof(A, 'V', atm(not,atm(not,B)), 'V', C, '+'):- wrt([A, 'V', atm(not,atm(not,B)), 'V', C], '+'), assert(toprove([A, 'V', atm(not,atm(not,B)), 'V', C], '+')).
proof(A, 'V', B, 'V', atm(not,atm(not,C)), '+'):- wrt([A, 'V', B, 'V', atm(not,atm(not,C))], '+'), assert(toprove([A, 'V', B, 'V', atm(not,atm(not,C))], '+')).
proof(A, 'V', B, 'V', C, '+'):- wrt([A, 'V', B, 'V', C], '+'), assert(toprove([A, 'V', B, 'V', C], '+')).
finprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'):- prf(atm(not,atm(not,A)), '+'), write("   OR   "), prf(atm(not,atm(not,B)), '+'), write("   OR   "), prf(atm(not,atm(not,C)), '+'), nl.
finprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C], '+'):- prf(atm(not,atm(not,A)), '+'), write("   OR   "), prf(atm(not,atm(not,B)), '+'), write("   OR   "), prf(C, '+'), nl.
finprove([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))], '+'):- prf(atm(not,atm(not,A)), '+'), write("   OR   "), prf(B, '+'), write("   OR   "), prf(atm(not,atm(not,C)), '+'), nl.
finprove([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'):- prf(A, '+'), write("   OR   "), prf(atm(not,atm(not,B)), '+'), write("   OR   "), prf(atm(not,atm(not,C)), '+'), nl.
finprove([atm(not,atm(not,A)), 'V', B, 'V', C], '+'):- prf(atm(not,atm(not,A)), '+'), write("   OR   "), prf(B, '+'), write("   OR   "), prf(C, '+'), nl.
finprove([A, 'V', atm(not,atm(not,B)), 'V', C], '+'):- prf(A, '+'), write("   OR   "), prf(atm(not,atm(not,B)), '+'), write("   OR   "), prf(C, '+'), nl.
finprove([A, 'V', B, 'V', atm(not,atm(not,C))], '+'):- prf(A, '+'), write("   OR   "), prf(B, '+'), write("   OR   "), prf(atm(not,atm(not,C)), '+'), nl.
finprove([A, 'V', B, 'V', C], '+'):- prf(A, '+'), write("   OR   "), prf(B, '+'), write("   OR   "), prf(C, '+'), nl.

%%proof(A&B-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '-'):- wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B))], '-'), assert(toprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B))], '-')).
proof(atm(not,atm(not,A)), '&', B, '-'):- wrt([atm(not,atm(not,A)), '&', B], '-'), assert(toprove([atm(not,atm(not,A)), '&', B], '-')).
proof(A, '&', atm(not,atm(not,B)), '-'):- wrt([A, '&', atm(not,atm(not,B))], '-'), assert(toprove([A, '&', atm(not,atm(not,B))], '-')).
proof(A, '&', B, '-'):- wrt([A, '&', B], '-'), assert(toprove([A, '&', B], '-')).
finprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B))], '-'):- prf(atm(not,atm(not,A)), '-'), write("   OR   "), prf(atm(not,atm(not,B)), '-'), nl.
finprove([atm(not,atm(not,A)), '&', B], '-'):- prf(atm(not,atm(not,A)), '-'), write("   OR   "), prf(B, '-'), nl.
finprove([A, '&', atm(not,atm(not,B))], '-'):- prf(A, '-'), write("   OR   "), prf(atm(not,atm(not,B)), '-'), nl.
finprove([A, '&', B], '-'):- prf(A, '-'), write("   OR   "), prf(B, '-'), nl.

%%proof(A&B&C-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'), assert(toprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-')).
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C, '-'):- wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C], '-'), assert(toprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C], '-')).
proof(atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C)), '-'):- wrt([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))], '-'), assert(toprove([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))], '-')).
proof(A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- wrt([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'), assert(toprove([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-')).
proof(atm(not,atm(not,A)), '&', B, '&', C, '-'):- wrt([atm(not,atm(not,A)), '&', B, '&', C], '-'), assert(toprove([atm(not,atm(not,A)), '&', B, '&', C], '-')).
proof(A, '&', atm(not,atm(not,B)), '&', C, '-'):- wrt([A, '&', atm(not,atm(not,B)), '&', C], '-'), assert(toprove([A, '&', atm(not,atm(not,B)), '&', C], '-')).
proof(A, '&', B, '&', atm(not,atm(not,C)), '-'):- wrt([A, '&', B, '&', atm(not,atm(not,C))], '-'), assert(toprove([A, '&', B, '&', atm(not,atm(not,C))], '-')).
proof(A, '&', B, '&', C, '-'):- wrt([A, '&', B, '&', C], '-'), assert(toprove([A, '&', B, '&', C], '-')).
finprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'):- prf(atm(not,atm(not,A)), '-'), write("   OR   "), prf(atm(not,atm(not,B)), '-'), write("   OR   "), prf(atm(not,atm(not,C)), '-'), nl.
finprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C], '-'):- prf(atm(not,atm(not,A)), '-'), write("   OR   "), prf(atm(not,atm(not,B)), '-'), write("   OR   "), prf(C, '-'), nl.
finprove([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))], '-'):- prf(atm(not,atm(not,A)), '-'), write("   OR   "), prf(B, '-'), write("   OR   "), prf(atm(not,atm(not,C)), '-'), nl.
finprove([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'):- prf(A, '-'), write("   OR   "), prf(atm(not,atm(not,B)), '-'), write("   OR   "), prf(atm(not,atm(not,C), '-'), nl.
finprove([atm(not,atm(not,A)), '&', B, '&', C], '-'):- prf(atm(not,atm(not,A)), '-'), write("   OR   "), prf(B, '-'), write("   OR   "), prf(C, '-'), nl.
finprove([A, '&', atm(not,atm(not,B)), '&', C], '-'):- prf(A, '-'), write("   OR   "), prf(atm(not,atm(not,B)), '-'), write("   OR   "), prf(C, '-'), nl.
finprove([A, '&', B, '&', atm(not,atm(not,C))], '-'):- prf(A, '-'), write("   OR   "), prf(B, '-'), write("   OR   "), prf(atm(not,atm(not,C)), '-'), nl.
finprove([A, '&', B, '&', C], '-'):- prf(A, '-'), write("   OR   "), prf(B, '-'), write("   OR   "), prf(C, '-'), nl.



finprove([[H]|[]], S):- finprove(H, S).
prove([H|[]], S):- H\=[_], H\=not, H\=atm(not,_), wrt([H], S).
prove([], _).
prove(['{', not,not, A, B, not,not, C, '}'|T], S):- proof(atm(not,atm(not,A)), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not,not, A, B, not, C, '}'|T], S):- proof(atm(not,atm(not,A)), B, atm(not,C), S), prove(T, S).
prove(['{', not,not, A, B, C, '}'|T], S):- C\=not, proof(atm(not,atm(not,A)), B, C, S), prove(T, S).
prove(['{', not, A, B, not,not, C, '}'|T], S):- proof(atm(not,A), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not, A, B, not, C, '}'|T], S):- proof(atm(not,A), B, atm(not,C), S), prove(T, S).
prove(['{', not, A, B, C, '}'|T], S):- C\=not, proof(atm(not,A), B, C, S), prove(T, S).
prove(['{', A, B, not,not, C, '}'|T], S):- proof(A, B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', A, B, not, C, '}'|T], S):- proof(A, B, atm(not,C), S), prove(T, S).
prove(['{', A, B, C, '}'|T], S):- B\=not, proof(A, B, C, S), prove(T, S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%hele-ding-printen??-----hoe-asserttoprove-moeilijke
prove([H, '&', '{', H2, '&', H3, '}'|T], '+'):- wrt([H, '&', '{', H2, '&', H3, '}'], '+'), wrt([H],'+'), nl, wrt([H2], '+'), nl, wrt([H3], '+'), nl, prove(T, '+').

prove([H, '&', '{', H2, 'V', H3, '}'|T], '+'):- wrt([H, '&', '{', H2, 'V', H3, '}'], '+'), wrt([H], '+'), nl, write(H2), write("V"), write(H3), write(", +"), nl, assert(toprove([H2, 'V', H3], '+'), prove(T, '+').

prove([H, 'V', '{', H2, '&', H3, '}'|T], '-'):- wrt([H, 'V', '{', H2, '&', H3, '}'], '-'), wrt([H], '-'), nl, write(H2), write("&"), write(H3), write(", -"), nl, assert(toprove([H2, '&', H3], '-'), prove(T, '+').

prove([H, 'V', '{', H2, 'V', H3, '}'|T], '-'):- wrt([H, 'V', '{', H2, 'V', H3, '}'|T], '-'), prf(H, '-'), nl, prf(H2, '-'), nl, prf(H3, '-'), nl, prove(T, '-').


%%%%%%%%%%%%%%%%%verschilmetDFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
prove([H, 'V', '{', H2, 'V', H3, '}'|T], '+'):- wrt(H, 'V', '{', H2, 'V', H3, '}'], '+'), assert(toprove([H, 'V', '{', H2, 'V', H3, '}'], '+')), prove(T, '+').
finprove([H, 'V', '{', H2, 'V', H3, '}'], '+'):- wrt([H, 'V', '{', H2, 'V', H3, '}'], '+'), proof(H, 'V', H2, 'V', H3, '+'), nl.

prove([H, '&', '{', H2, 'V', H3, '}'|T], '-'):- wrt([H, '&', '{', H2, 'V', H3, '}'], '-'), assert(toprove([H, '&', '{', H2, 'V', H3, '}'|T], '-')).

prove([H, 'V', '{', H2, '&', H3, '}'|T], '+'):- wrt([H, 'V', '{', H2, '&', H3, '}'], '+'), assert(toprove([H, 'V', '{', H2, '&', H3, '}'|T], '+')).

prove([H, '&', '{', H2, '&', H3, '}'|T], '-'):- wrt([H, '&', '{', H2, '&', H3, '}'], '-'), proof(H, '&', H2, '&', H3, '-'), nl, prove(T, '-').
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%prove(A&B+)
prove([not,not,H,'&',not,not,not,H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)), '&', atm(not,atm(not,atm(not,H3)))|T], '+'), proof(atm(not,atm(not,H)), '&', atm(not,atm(not,atm(not,H3))), '+'), prove(T, '+').
prove([not,not,H,'&',not,not,H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)), '&', atm(not,atm(not,H3))|T], '+'), proof(atm(not,atm(not,H)), '&', atm(not,atm(not,H3)), '+'), prove(T, '+').
prove([not,not,H,'&',not,H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)), '&', atm(not,H3)], '+'), proof(atm(not,atm(not,H)), '&', atm(not,H3), '+'), prove(T, '+').
prove([not,not,H,'&',H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)), '&', H3], '+'), proof(atm(not,atm(not,H)), '&', H3, '+'), prove(T, '+').
prove([not,H,'&',not,not,not,H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H), '&', atm(not,atm(not,atm(not,H3)))|T], '+'), proof(atm(not,H), '&', atm(not,atm(not,atm(not,H3))), '+'), prove(T, '+').
prove([not,H,'&',not,not,H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H), '&', atm(not,atm(not,H3))|T], '+'), proof(atm(not,H), '&', atm(not,atm(not,H3)), '+'), prove(T, '+').
prove([not,H,'&',not,H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H), '&', atm(not,H3)], '+'), proof(atm(not,H), '&', atm(not,H3), '+'), prove(T, '+').
prove([not,H,'&',H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H), '&', H3], '+'), proof(atm(not,H), '&', H3, '+'), prove(T, '+').
prove([H,'&',not, not, not, H3|T], '+'):- H3\='{', wrt([H, '&', atm(not,atm(not,atm(not,H3)))|T], '+'), proof(H, '&', atm(not,atm(not,atm(not,H3))), '+'), prove(T, '+').
prove([H,'&',not, not, H3|T], '+'):- H3\='{', H3\=not, wrt([H, '&', atm(not,atm(not,H3))|T], '+'), proof(H, '&', atm(not,atm(not,H3)), '+'), prove(T, '+').
prove([H,'&',not, H3|T], '+'):- H3\='{', H3\=not, wrt([H, '&', atm(not,H3)], '+'), proof(H, '&', atm(not,H3), '+'), prove(T, '+').
prove([H,'&',H3|T], '+'):- H3\='{', H3\=not, wrt([H, '&', H3], '+'), proof(H, '&', H3, '+'), prove(T, '+').


%%%%%%%%%%%%%%%%%verschilmetDFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%prove(AVB+)
prove([not,not, H,'V', not,not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',atm(not,atm(not,atm(not,H3)))|T], '+'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), 'V', atm(not,atm(not,atm(not,H3)))], '+')), prove(T, '+').  
prove([not,not, H,'V', not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',atm(not,atm(not,H3))|T], '+'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), 'V', atm(not,atm(not,H3))], '+')), prove(T, '+'). 
prove([not,not, H,'V', not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',atm(not,H3)|T], '+'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), 'V', atm(not,H3)], '+')), prove(T, '+'). 
prove([not,not, H,'V',H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',H3|T], '+'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), 'V', H3], '+')), prove(T, '+'). 
prove([not, H,'V', not,not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',atm(not,atm(not,atm(not,H3)))|T], '+'), write("  /\\"), assert(toprove([atm(not,H), 'V', atm(not,atm(not,atm(not,H3)))], '+')), prove(T, '+').  
prove([not, H,'V', not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',atm(not,atm(not,H3))|T], '+'), write("  /\\"), assert(toprove([atm(not,H), 'V', atm(not,atm(not,H3))], '+')), prove(T, '+'). 
prove([not, H,'V', not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',atm(not,H3)|T], '+'), write("  /\\"), assert(toprove([atm(not,H), 'V', atm(not,H3)], '+')), prove(T, '+'). 
prove([not, H,'V',H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',H3|T], '+'), write("  /\\"), assert(toprove([atm(not,H), 'V', H3], '+')), prove(T, '+'). 
prove([H,'V', not, not, not, H3|T], '+'):- H3\='{', wrt([H,'V',atm(not,atm(not,atm(not,H3)))|T], '+'), write("  /\\"), assert(toprove([H, 'V', atm(not,atm(not,atm(not,H3)))], '+')), prove(T, '+'). 
prove([H,'V', not, not, H3|T], '+'):- H3\='{', H3\=not, wrt([H,'V',atm(not,atm(not,H3))|T], '+'), write("  /\\"), assert(toprove([H, 'V', atm(not,atm(not,H3))], '+')), prove(T, '+'). 
prove([H,'V', not, H3|T], '+'):- H3\='{', H3\=not, wrt([H,'V',atm(not,H3)|T], '+'), write("  /\\"), assert(toprove([H, 'V', atm(not,H3)], '+')), prove(T, '+'). 
prove([H,'V',H3|T], '+'):- H3\='{', H3\=not, wrt([H,'V',H3|T], '+'), write("  /\\"), assert(prove([H, 'V', H3], '+')), prove(T, '+').

%%prove(A&B-)
prove([not,not, H,'&', not,not,not, H3|T], '-'):-  H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',atm(not,atm(not,atm(not,H3)))|T], '-'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), '&', atm(not,atm(not,atm(not,H3)))], '-')), prove(T, '-').   
prove([not,not, H,'&', not,not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',atm(not,atm(not,H3))|T], '-'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), '&', atm(not,atm(not,H3))], '-')), prove(T, '-').   
prove([not,not, H,'&', not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',atm(not,H3)|T], '-'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), '&', atm(not,H3)], '-')), prove(T, '-').  
prove([not,not, H,'&',H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',H3|T], '-'), write("  /\\"), assert(toprove([atm(not,atm(not,H)), '&', H3], '-')), prove(T, '-'). 
prove([not, H,'&', not,not,not, H3|T], '-'):-  H3\='{', H3\=not, wrt([atm(not,H),'&',atm(not,atm(not,atm(not,H3)))|T], '-'), write("  /\\"), assert(toprove([atm(not,H), '&', atm(not,atm(not,atm(not,H3)))], '-')), prove(T, '-').   
prove([not, H,'&', not,not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H),'&',atm(not,atm(not,H3))|T], '-'), write("  /\\"), assert(toprove([atm(not,H), '&', atm(not,atm(not,H3))], '-')), prove(T, '-').   
prove([not, H,'&', not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H),'&',atm(not,H3)|T], '-'), write("  /\\"), assert(toprove([atm(not,H), '&', atm(not,H3)], '-')), prove(T, '-').  
prove([not, H,'&',H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H),'&',H3|T], '-'), write("  /\\"), assert(toprove([atm(not,H), '&', H3], '-')), prove(T, '-'). 
prove([H,'&', not, not, not, H3|T], '-'):- H3\='{', wrt([H,'&',atm(not,atm(not,atm(not,H3)))|T], '-'), write("  /\\"), assert(toprove([H, '&', atm(not,atm(not,atm(not,H3)))], '-')), prove(T, '-').   
prove([H,'&', not, not, H3|T], '-'):- H3\='{', H3\=not, wrt([H,'&',atm(not,atm(not,H3))|T], '-'), write("  /\\"), assert(toprove([H, '&', atm(not,atm(not,H3))], '-')), prove(T, '-').  
prove([H,'&', not, H3|T], '-'):- H3\='{', H3\=not, wrt([H,'&',atm(not,H3)|T], '-'), write("  /\\"), assert(toprove([H, '&', atm(not,H3)], '-')), prove(T, '-'). 
prove([H,'&',H3|T], '-'):- H3\='{', H3\=not, wrt([H,'&',H3|T], '-'), write("  /\\"), assert(toprove([H, '&', H3], '-')), prove(T, '-').
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%prove(AVB-)
prove([not,not, H,'V', not,not,not, H3|T], '-'):- H3\='{', wrt([atm(not,atm(not,H)), 'V', atm(not,atm(not,atm(not,H3)))|T], '-'), proof(atm(not,atm(not,H)), 'V', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').
prove([not,not, H,'V', not,not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)), 'V', atm(not,atm(not,H3))|T], '-'), proof(atm(not,atm(not,H)), 'V', atm(not,atm(not,H3)), '-'), prove(T, '-').
prove([not,not, H,'V', not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)), 'V', atm(not,H3)], '-'), proof(atm(not,atm(not,H)), 'V', atm(not,H3), '-'), prove(T, '-').
prove([not,not, H,'V',H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)), 'V', H3], '-'), proof(atm(not,atm(not,H)), 'V', H3, '-'), prove(T, '-').
prove([not, H,'V', not,not,not, H3|T], '-'):- H3\='{', wrt([atm(not,H), 'V', atm(not,atm(not,atm(not,H3)))|T], '-'), proof(atm(not,H), 'V', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').
prove([not, H,'V', not,not, H3|T], '-'):- H3\='{', H3\=not, wrt([not, H, 'V', atm(not,atm(not,H3))|T], '-'), proof(atm(not,H), 'V', atm(not,atm(not,H3)), '-'), prove(T, '-').
prove([not, H,'V', not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H), 'V', atm(not,H3)], '-'), proof(atm(not,H), 'V', atm(not,H3), '-'), prove(T, '-').
prove([not, H,'V',H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H), 'V', H3], '-'), proof(atm(not,H), 'V', H3, '-'), prove(T, '-').
prove([H,'V', not,not,not, H3|T], '-'):- H3\='{', wrt([H, 'V', atm(not,atm(not,atm(not,H3)))|T], '-'), proof(H, 'V', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').
prove([H,'V', not,not, H3|T], '-'):- H3\='{', H3\=not, wrt([H, 'V', atm(not,atm(not,H3))|T], '-'), proof(H, 'V', atm(not,atm(not,H3)), '-'), prove(T, '-').
prove([H,'V', not, H3|T], '-'):- H3\='{', H3\=not, wrt([H, 'V', atm(not,H3)], '-'), proof(H, 'V', atm(not,H3), '-'), prove(T, '-').
prove([H,'V', H3|T], '-'):- H3\='{', H3\=not, wrt([H, 'V', H3], '-'), proof(H, 'V', H3, '-'), prove(T, '-').


%%%%%%%%%%%%%%%%%???????????????????????????????
prove(['{', H, '&', H2, '}', '&', H3|T], S):- proof(H, '&', H2, '&', H3], S), prove(T,S).
prove(['{', H, 'V', H2, '}', 'V', H3|T], S):- proof(H, 'V', H2, 'V', H3], S), prove(T,S).
prove(['{', H, '&', H2, '}', 'V', H3|T], '+'):- wrt(['{', H, '&', H2, '}', 'V', H3|T], '+'), assert(toprove(['{', H, '&', H2, '}', 'V', H3|T], '+')), prove(T, '+').  
prove(['{', H, 'V', H2, '}', '&', H3|T], '+'):- wrt(['{', H, 'V', H2, '}', '&', H3|T], '+'), assert(toprove(['{', H, 'V', H2, '}', '&', H3|T], '+')), prove(T, '+').
prove(['{', H, '&', H2, '}', 'V', H3|T], '-'):- wrt(['{', H, '&', H2, '}', 'V', H3|T], '-'), assert(toprove(['{', H, '&', H2, '}', 'V', H3|T], '-')), prove(T, '-').
prove(['{', H, 'V', H2, '}', '&', H3|T], '-'):- wrt(['{', H, 'V', H2, '}', '&', H3|T], '-'), assert(toprove(['{', H, 'V', H2, '}', '&', H3|T], '-')), prove(T, '-').


prove([not, '{', H, '&', H2, '}'|T], '+'):- write("not"), write(H), write(" V not"), write(H2), writeln(", +"), proof(atm(not, H), 'V', atm(not, H2), '+'), nl, prove(T, '+').

prove([not, '{', H, 'V', H2, '}'|T], '+'):- write("not"), write(H), write(" & not"), write(H2), writeln(", +"), proof(atm(not, H), '&', atm(not, H2), '+'), nl, prove(T, '+').

prove([not, '{', H, '&', H2, '}'|T], '-'):- write("not"), write(H), write(" V not"), write(H2), writeln(", -"), proof(atm(not, H), 'V', atm(not, H2), '-'), nl, prove(T, '-').

prove([not, '{', H, 'V', H2, '}'|T], '-'):- write("not"), write(H), write(" & not"), write(H2), writeln(", -"), proof(atm(not, H), '&', atm(not, H2), '-'), nl, prove(T, '-').

prove([atm(not,atm(not,(atm(not,A))))|T],S):- wrt([not,not,not,A],S), wrt([not,A],S), prove(T,S).
prove([atm(not,(atm(not,A)))|T],S):- wrt([not,not,A],S), wrt([A],S), prove(T,S).
prove([not,not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,not,H], S), wrt([not,H],S), prove(T, S).
prove([not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,H], S), wrt([H],S), prove(T, S).
prove([not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,H], S), prove(T, S). 

prf(atm(not,A), S):- write("not"), write(A), write(","), write(S). 
prf([],S):- write(","), writeln(S).
prf([atm(not,A)|T], S):- write("not"), write(A), prf(T, S). 
prf([H|T], S):- H\=atm(not,_), H\=[], H\=[_], write(H), prf(T, S).
%%_
prf(A,S):- A\=[], A\=[_], A\= atm(not,_), A\=[_|_], write(A), write(","), write(S).
%%_


%hoe met 1 atom als inference, dan printie 2x
%voor bfs: eenn lijst bijhouden met atoms per branch
