:- dynamic prf(_,_).
:- dynamic assprove(_,_).
:- dynamic toprove/2.
:- discontiguous proof/6.
:- discontiguous proof/4.
:- discontiguous toprove/2.
:- discontiguous prove/2.
:- discontiguous finprove/2.


ass([]).
ass([not, not, not, H]):- wrt([not, not, not, H], '+'), assert(assprove([not,not,not,H],'+')).  %%%%%wrt(atmnot??
ass([not, not, H]):- wrt([not, not, H], '+'), assert(assprove([not,not,H],'+')).
ass([not, H]):- assert(prf(atm(not,H),'+')), wrt([H], '+').

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
wrt([atm(not,A)|T],S):- A\=atm(not,_), write("not"), write(A), wrt(T,S).
wrt([H|T],S):- H\=atm(not,_), write(H), wrt(T,S).

prove(A, '|', C):- C\=[_], C\=[not,_], ass(A), wrt(C, '-'), nl, findall([Z], assprove(Z, '+'), AS), check(AS), prove(C, '-').
prove(A, '|', C):- C=[_], ass(A), wrt(C, '-'), nl, findall([Z], assprove(Z, '+'), AS), check(AS).
prove(A, '|', C):- C=[not,_], ass(A), wrt(C, '-'), nl, findall([Z], assprove(Z, '+'), AS), check(AS).

check([]).
check([[H]|T]):- H\=[[]], writeln("premises solving:"), prsolve([[H]|T]), nl, writeln("inferences solving:").
prsolve([]).
prsolve([[H]|T]):- prove(H, '+'), prsolve(T).





proof(A, '&', B, '+'):- wrt([A], '+'), wrt([B], '+').
proof(A, '&', B, '&', C, '+'):- wrt([A], '+'), wrt([B], '+'), wrt([C], '+').
proof(A, 'V', B, '-'):- wrt([A], '-'), wrt([B], '-').
proof(A, 'V', B, 'V', C, '-'):- wrt([A], '-'), wrt([B], '-'), wrt([C], '-').


%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%
proof(A, 'V', B, '+'):- ( assert(prf(A, '+')), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), wrt([B], '+') ).
proof(A, 'V', B, 'V', C, '+'):- ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(A, '+')), retract(prf(B, '+')), writeln("\\"), wrt([C], '+') ).
proof(A, '&', B, '-'):- ( assert(prf(A, '-')), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), wrt([B], '-') ).
proof(A, '&', B, '&', C, '-'):- ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(A, '-')), retract(prf(B, '-')), writeln("\\"), wrt([C], '-') ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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


prove([H, '&', '{', H2, '&', H3, '}'|T], '+'):- wrt([H],'+'), wrt([H2], '+'), wrt([H3], '+'), prove(T, '+').

prove([H, '&', '{', H2, 'V', H3, '}'|T], '+'):- wrt([H], '+'), wrt([H2,'V',H3], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), nl, prove(T, '+').

prove([H, 'V', '{', H2, '&', H3, '}'|T], '-'):- wrt([H], '-'), wrt([H2,'&',H3], '-'), write("  /\\"), proof(H2, '&', H3, '-'), nl, prove(T, '+').

prove([H, 'V', '{', H2, 'V', H3, '}'|T], '-'):- wrt([H], '-'), wrt([H2], '-'), wrt([H3], '-'), prove(T, '-'). 


%%%%%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%write("  /\\")%%%%%%%
prove([H, 'V', '{', H2, 'V', H3, '}'|T], '+'):- ( write("  /\\"), assert(prf(H, '+')), wrt([H], '+'), prove(T, '+') ) ; ( retract(prf(H, '+')), writeln("\\"), wrt([H2, 'V', H3], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), prove(T, '+') ).
prove([H, '&', '{', H2, 'V', H3, '}'|T], '-'):- ( write("  /\\"), assert(prf(H, '-')), wrt([H], '-'), prove(T, '-') ) ; ( retract(prf(H, '-')), writeln("\\"), wrt([H2, 'V', H3], '-'), proof(H2, 'V', H3, '-'), prove(T, '-') ).
prove([H, 'V', '{', H2, '&', H3, '}'|T], '+'):- ( write("  /\\"), assert(prf(H, '+')), wrt([H], '+'), prove(T, '+') ) ; ( retract(prf(H, '+')), writeln("\\"), wrt([H2, '&', H3], '+'), proof(H2, '&', H3, '+'), prove(T, '+') ).
prove([H, '&', '{', H2, '&', H3, '}'|T], '-'):- ( write("  /\\"), assert(prf(H, '-')), wrt([H], '-'), prove(T, '-') ) ; ( retract(prf(H, '-')), writeln("\\"), wrt([H2, '&', H3], '-'), write("  /\\"), proof(H2, '&', H3, '-'), prove(T, '-') ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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


%%%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
prove([not,not, H,'V', not,not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',atm(not,atm(not,atm(not,H3)))|T], '+'), write("  /\\"), proof(atm(not,atm(not,H)), 'V', atm(not,atm(not,atm(not,H3))), '+'), prove(T, '+').  
prove([not,not, H,'V', not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',atm(not,atm(not,H3))|T], '+'), write("  /\\"), proof(atm(not,atm(not,H)), 'V', atm(not,atm(not,H3)), '+'), prove(T, '+'). 
prove([not,not, H,'V', not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',atm(not,H3)|T], '+'), write("  /\\"), proof(atm(not,atm(not,H)), 'V', atm(not,H3), '+'), prove(T, '+'). 
prove([not,not, H,'V',H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'V',H3|T], '+'), write("  /\\"), proof(atm(not,atm(not,H)), 'V', H3, '+'), prove(T, '+'). 
prove([not, H,'V', not,not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',atm(not,atm(not,atm(not,H3)))|T], '+'), write("  /\\"), proof(atm(not,H), 'V', atm(not,atm(not,atm(not,H3))), '+'), prove(T, '+').  
prove([not, H,'V', not,not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',atm(not,atm(not,H3))|T], '+'), write("  /\\"), proof(atm(not,H), 'V', atm(not,atm(not,H3)), '+'), prove(T, '+'). 
prove([not, H,'V', not, H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',atm(not,H3)|T], '+'), write("  /\\"), proof(atm(not,H), 'V', atm(not,H3), '+'), prove(T, '+'). 
prove([not, H,'V',H3|T], '+'):- H3\='{', H3\=not, wrt([atm(not,H),'V',H3|T], '+'), write("  /\\"), proof(atm(not,H), 'V', H3, '+'), prove(T, '+'). 
prove([H,'V', not, not, not, H3|T], '+'):- H3\='{', wrt([H,'V',atm(not,atm(not,atm(not,H3)))|T], '+'), write("  /\\"), proof(H, 'V', atm(not,atm(not,atm(not,H3))), '+'), prove(T, '+'). 
prove([H,'V', not, not, H3|T], '+'):- H3\='{', H3\=not, wrt([H,'V',atm(not,atm(not,H3))|T], '+'), write("  /\\"), proof(H, 'V', atm(not,atm(not,H3)), '+'), prove(T, '+'). 
prove([H,'V', not, H3|T], '+'):- H3\='{', H3\=not, wrt([H,'V',atm(not,H3)|T], '+'), write("  /\\"), proof(H, 'V', atm(not,H3), '+'), prove(T, '+'). 
prove([H,'V',H3|T], '+'):- H3\='{', H3\=not, wrt([H,'V',H3|T], '+'), write("  /\\"), proof(H, 'V', H3, '+'), prove(T, '+').

prove([not,not, H,'&', not,not,not, H3|T], '-'):-  H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',atm(not,atm(not,atm(not,H3)))|T], '-'), write("  /\\"), proof(atm(not,atm(not,H)), '&', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').   
prove([not,not, H,'&', not,not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',atm(not,atm(not,H3))|T], '-'), write("  /\\"), proof(atm(not,atm(not,H)), '&', atm(not,atm(not,H3)), '-'), prove(T, '-').   
prove([not,not, H,'&', not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',atm(not,H3)|T], '-'), write("  /\\"), proof(atm(not,atm(not,H)), '&', atm(not,H3), '-'), prove(T, '-').  
prove([not,not, H,'&',H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,atm(not,H)),'&',H3|T], '-'), write("  /\\"), proof(atm(not,atm(not,H)), '&', H3, '-'), prove(T, '-'). 
prove([not, H,'&', not,not,not, H3|T], '-'):-  H3\='{', H3\=not, wrt([atm(not,H),'&',atm(not,atm(not,atm(not,H3)))|T], '-'), write("  /\\"), proof(atm(not,H), '&', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').   
prove([not, H,'&', not,not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H),'&',atm(not,atm(not,H3))|T], '-'), write("  /\\"), proof(atm(not,H), '&', atm(not,atm(not,H3)), '-'), prove(T, '-').   
prove([not, H,'&', not, H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H),'&',atm(not,H3)|T], '-'), write("  /\\"), proof(atm(not,H), '&', atm(not,H3), '-'), prove(T, '-').  
prove([not, H,'&',H3|T], '-'):- H3\='{', H3\=not, wrt([atm(not,H),'&',H3|T], '-'), write("  /\\"), proof(atm(not,H), '&', H3, '-'), prove(T, '-'). 
prove([H,'&', not, not, not, H3|T], '-'):- H3\='{', wrt([H,'&',atm(not,atm(not,atm(not,H3)))|T], '-'), write("  /\\"), proof(H, '&', atm(not,atm(not,atm(not,H3))), '-'), prove(T, '-').   
prove([H,'&', not, not, H3|T], '-'):- H3\='{', H3\=not, wrt([H,'&',atm(not,atm(not,H3))|T], '-'), write("  /\\"), proof(H, '&', atm(not,atm(not,H3)), '-'), prove(T, '-').  
prove([H,'&', not, H3|T], '-'):- H3\='{', H3\=not, wrt([H,'&',atm(not,H3)|T], '-'), write("  /\\"), proof(H, '&', atm(not,H3), '-'), prove(T, '-'). 
prove([H,'&',H3|T], '-'):- H3\='{', H3\=not, wrt([H,'&',H3|T], '-'), write("  /\\"), proof(H, '&', H3, '-'), prove(T, '-').
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

%%%%%%%%%%%%%%%%%%%%%%?????????????????%%%%%%%%%%%%%%%%%%%%
prove(['{', H, '&', H2, '}', '&', H3|T], S):- proof(H, '&', H2, '&', H3, S), prove(T,S).
prove(['{', H, 'V', H2, '}', 'V', H3|T], S):- proof(H, 'V', H2, 'V', H3, S), prove(T,S).
prove(['{', H, 'V', H2, '}', '&', H3|T], '+'):- wrt(H3, '+'), wrt([H, 'V', H2], '+'), prove([H, 'V', H2], '+'), prove(T, '+').
prove(['{', H, '&', H2, '}', 'V', H3|T], '-'):- wrt(H3, '+'), wrt([H, '&', H2], '-'), prove([H, '&', H2], '-'), prove(T, '-').
prove(['{', H, '&', H2, '}', 'V', H3|T], '+'):- prove([H, '&', H2|T], '+'), write("     OR   "), wrt(H3, '+'), prove(T, '+').      %%%%%
prove(['{', H, 'V', H2, '}', '&', H3|T], '-'):- wrt(H3, '-'), write("     OR   "), prove([H, 'V', H2|T], '-'), prove(T, '-').     %%%%
%prove([not, H|T], '+'):-proof(atm(not,H), '+'), prove(T, '+').
%prove([not, H|T], '-'):-proof(atm(not,H), '-'), prove(T, '-').


prove([not, '{', H, '&', H2, '}'|T], '+'):- wrt([not, '{', H, '&', H2, '}'], '+'), wrt([atm(not,H), 'V', atm(not,H2)], '+'), proof(atm(not, H), 'V', atm(not, H2), '+'), prove(T, '+').

prove([not, '{', H, 'V', H2, '}'|T], '+'):- wrt([not, '{', H, 'V', H2, '}'], '+'), wrt([atm(not,H), '&', atm(not,H2)], '+'), write("  /\\"), proof(atm(not, H), '&', atm(not, H2), '+'), prove(T, '+').

prove([not, '{', H, '&', H2, '}'|T], '-'):- wrt([not, '{', H, '&', H2, '}'], '-'), wrt([atm(not,H), 'V', atm(not,H2)], '-'), proof(atm(not, H), 'V', atm(not, H2), '-'), prove(T, '-').

prove([not, '{', H, 'V', H2, '}'|T], '-'):- wrt([not, '{', H, 'V', H2, '}'], '-'), wrt([atm(not,H), '&', atm(not,H2)], '-'), write("  /\\"), proof(atm(not, H), '&', atm(not, H2), '-'), prove(T, '-').


prove([atm(not,atm(not,(atm(not,A))))|T],S):- wrt([not,not,not,A],S), wrt([not,A],S), prove(T,S).
prove([atm(not,(atm(not,A)))|T],S):- wrt([not,not,A],S), wrt([A],S), prove(T,S).
prove([not,not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,not,H], S), wrt([not,H],S), prove(T, S).
prove([not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,H], S), wrt([H],S), prove(T, S).
prove([not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,H], S), prove(T, S).

%prf(atm(not,A), S):- write("not"), write(A), write(","), write(S). 
%prf([],S):- write(","), writeln(S).
%prf([atm(not,A)|T], S):- write("not"), write(A), prf(T, S). 
%prf([H|T], S):- H\=atm(not,_), H\=[], H\=[_], write(H), prf(T, S).%%_
%prf(A,S):- A\=[], A\=[_], A\= atm(not,_), A\=[_|_], write(A), write(","), write(S).%%_

%hoe met 1 atom als inference, dan printie 2x
