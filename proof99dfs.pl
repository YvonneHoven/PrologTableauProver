%% making functions dynamic to be able to use assert & discontiguous to be able to put all functions not necessarily side by side
:- dynamic prf(_,_).
:- dynamic assprove(_).
:- dynamic noPrint(_,_).
:- dynamic list(_).
:- discontiguous proof/6.
:- discontiguous proof/4.
:- discontiguous prove/2.
:- discontiguous prove/4.
:- discontiguous membr/3.


%% all assertions of the premises
ass([]).
ass([not,not,not, H]):- wrt([not,not,not, H], '+'), assert(assprove([not,not,not,H])).  
ass([not,not, H]):- wrt([not,not, H], '+'), assert(assprove([not,not,H])).
ass([not, H]):-  wrt([atm(not,H)], '+'), assert(prf(atm(not,H),'+')).
ass([H]):- wrt([H], '+'), assert(prf(H, '+')).

%%simplify assert {A&B} 
ass(['{', not,not,not,A, '&', not,not,not,C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,atm(not,A))), '&', atm(not,atm(not,atm(not,C))), '}'], '+'), ass([atm(not,atm(not,atm(not,A))), '&', atm(not,atm(not,atm(not,C)))|T]).
ass(['{', not,not,not,A, '&', not,not,C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,atm(not,A))), '&', atm(not,atm(not,C)), '}'], '+'), ass([atm(not,atm(not,atm(not,A))), '&', atm(not,atm(not,C))|T]).
ass(['{', not,not,not,A, '&', not,C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,atm(not,A))), '&', atm(not,C), '}'], '+'), ass([atm(not,atm(not,atm(not,A))), '&', atm(not,C)|T]).
ass(['{', not,not,not,A, '&', C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,atm(not,A))), '&', C, '}'], '+'), ass([atm(not,atm(not,atm(not,A))), '&', C|T]).
ass(['{', not,not,A, '&', not,not,not,C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,A)), '&', atm(not,atm(not,atm(not,C))), '}'], '+'), ass([atm(not,atm(not,A)), '&', atm(not,atm(not,atm(not,C)))|T]).
ass(['{', not,not,A, '&', not,not,C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,A)), '&', atm(not,atm(not,C)), '}'], '+'), ass([atm(not,atm(not,A)), '&', atm(not,atm(not,C))|T]).
ass(['{', not,not,A, '&', not,C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,A)), '&', atm(not,C), '}'], '+'), ass([atm(not,atm(not,A)), '&', atm(not,C)|T]).
ass(['{', not,not,A, '&', C, '}'|T]):- C\=not, wrt(['{', atm(not,atm(not,A)), '&', C, '}'], '+'), ass([atm(not,atm(not,A)), '&', C|T]).
ass(['{', not,A, '&', not,not,not,C, '}'|T]):- C\=not, wrt(['{', atm(not,A), '&', atm(not,atm(not,atm(not,C))), '}'], '+'), ass([atm(not,A), '&', atm(not,atm(not,atm(not,C)))|T]).
ass(['{', not,A, '&', not,not,C, '}'|T]):- C\=not, wrt(['{', atm(not,A), '&', atm(not,atm(not,C)), '}'], '+'), ass([atm(not,A), '&', atm(not,atm(not,C))|T]).
ass(['{', not,A, '&', not,C, '}'|T]):- C\=not, wrt(['{', atm(not,A), '&', atm(not,C), '}'], '+'), ass([atm(not,A), '&', atm(not,C)|T]).
ass(['{', not,A, '&', C, '}'|T]):- C\=not, wrt(['{', atm(not,A), '&', C, '}'], '+'), ass([atm(not,A), '&', C|T]).
ass(['{', A, '&', not,not,not,C, '}'|T]):- C\=not, wrt(['{', A, '&', atm(not,atm(not,atm(not,C))), '}'], '+'), ass([A, '&', atm(not,atm(not,atm(not,C)))|T]).
ass(['{', A, '&', not,not,C, '}'|T]):- C\=not, wrt(['{', A, '&', atm(not,atm(not,C)), '}'], '+'), ass([A, '&', atm(not,atm(not,C))|T]).
ass(['{', A, '&', not,C, '}'|T]):- C\=not, wrt(['{', A, '&', atm(not,C), '}'], '+'), ass([A, '&', atm(not,C)|T]).
ass(['{', A, '&', C, '}'|T]):- C\=not, wrt(['{', A, '&', C, '}'], '+'), ass([A, '&', C|T]).
%%simplify assert A&B
ass([not,not,not,A, '&', not,not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,atm(not,A))), '&', atm(not,atm(not,atm(not,C)))|T]).
ass([not,not,not,A, '&', not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,atm(not,A))), '&', atm(not,atm(not,C))|T]).
ass([not,not,not,A, '&', not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,atm(not,A))), '&', atm(not,C)|T]).
ass([not,not,not,A, '&', C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,atm(not,A))), '&', C|T]).
ass([not,not,A, '&', not,not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,A)), '&', atm(not,atm(not,atm(not,C)))|T]).
ass([not,not,A, '&', not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,A)), '&', atm(not,atm(not,C))|T]).
ass([not,not,A, '&', not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,A)), '&', atm(not,C)|T]).
ass([not,not,A, '&', C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,atm(not,A)), '&', C|T]).
ass([not,A, '&', not,not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,A), '&', atm(not,atm(not,atm(not,C)))|T]).
ass([not,A, '&', not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,A), '&', atm(not,atm(not,C))|T]).
ass([not,A, '&', not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,A), '&', atm(not,C)|T]).
ass([not,A, '&', C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([atm(not,A), '&', C|T]).
ass([A, '&', not,not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([A, '&', atm(not,atm(not,atm(not,C)))|T]).
ass([A, '&', not,not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([A, '&', atm(not,atm(not,C))|T]).
ass([A, '&', not,C|T]):- C\=not, C\='{', T\=['&'|_], T\=['V'|_], ass([A, '&', atm(not,C)|T]).

%%assert A&B 
ass([A, '&', C|T]):- A\=not, C\=not, C\='{', wrt([A,'&',C], '+'), ass(T), assert(assprove([A, '&', C])).

%%simplify assert notnot{A&B} 
ass([not,not, '{', not,not,H, '&', not,not,H2, '}'|T]):- wrt([not,not, '{', atm(not,atm(not,H)), '&', atm(not,atm(not,H2)), '}'], '+'), ass([atm(not,atm(not,H)), '&', atm(not,atm(not,H2))|T]).
ass([not,not, '{', not,not,H, '&', not,H2, '}'|T]):- wrt([not,not, '{', atm(not,atm(not,H)), '&', atm(not,H2), '}'], '+'), ass([atm(not,atm(not,H)), '&', atm(not,H2)|T]).
ass([not,not, '{', not,not,H, '&', H2, '}'|T]):- wrt([not,not, '{', atm(not,atm(not,H)), '&', H2, '}'], '+'), ass([atm(not,atm(not,H)), '&', H2|T]).
ass([not,not, '{', not,H, '&', not,not,H2, '}'|T]):- wrt([not,not, '{', atm(not,H), '&', atm(not,atm(not,H2)), '}'], '+'), ass([atm(not,H), '&', atm(not,atm(not,H2))|T]).
ass([not,not, '{', not,H, '&', not,H2, '}'|T]):- wrt([not,not, '{', atm(not,H), '&', atm(not,H2), '}'], '+'), ass([atm(not,H), '&', atm(not,H2)|T]).
ass([not,not, '{', not,H, '&', H2, '}'|T]):- wrt([not,not, '{', atm(not,H), '&', H2, '}'], '+'), ass([atm(not,H), '&', H2|T]).
ass([not,not, '{', H, '&', not,not,H2, '}'|T]):- wrt([not,not, '{', H, '&', atm(not,atm(not,H2)), '}'], '+'), ass([H, '&', atm(not,atm(not,H2))|T]).
ass([not,not, '{', H, '&', not,H2, '}'|T]):- wrt([not,not, '{', H, '&', atm(not,H2), '}'], '+'), ass([H, '&', atm(not,H2)|T]).
ass([not,not, '{', H, '&', H2, '}'|T]):- wrt([not,not, '{', H, '&', H2, '}'], '+'), ass([H, '&', H2|T]).
%%simplify assert not{AVB}
ass([not, '{', not,not,H, 'V', not,not,H2, '}'|T]):- ass([not, '{', atm(not,atm(not,H)), 'V', atm(not,atm(not,H2)), '}'|T]).
ass([not, '{', not,not,H, 'V', not,H2, '}'|T]):- ass([not, '{', atm(not,atm(not,H)), 'V', atm(not,H2), '}'|T]).
ass([not, '{', not,not,H, 'V', H2, '}'|T]):- ass([not, '{', atm(not,atm(not,H)), 'V', H2, '}'|T]).
ass([not, '{', not,H, 'V', not,not,H2, '}'|T]):- ass([not, '{', atm(not,H), 'V', atm(not,atm(not,H2)), '}'|T]).
ass([not, '{', not,H, 'V', not,H2, '}'|T]):- ass([not, '{', atm(not,H), 'V', atm(not,H2), '}'|T]).
ass([not, '{', not,H, 'V', H2, '}'|T]):- ass([not, '{', atm(not,H), 'V', H2, '}'|T]).
ass([not, '{', H, 'V', not,not,H2, '}'|T]):- ass([not, '{', H, 'V', atm(not,atm(not,H2)), '}'|T]).
ass([not, '{', H, 'V', not,H2, '}'|T]):- ass([not, '{', H, 'V', atm(not,H2), '}'|T]).
%%simplify assert A&{B&C}
ass([not,H, '&', '{', not,H2, '&', not,H3, '}'|T]):- ass([atm(not,H), '&', '{', atm(not,H2), '&', atm(not,H3), '}'|T]).
ass([not,H, '&', '{', not,H2, '&', H3, '}'|T]):- ass([atm(not,H), '&', '{', atm(not,H2), '&', H3, '}'|T]).
ass([not,H, '&', '{', H2, '&', not,H3, '}'|T]):- ass([atm(not,H), '&', '{', H2, '&', atm(not,H3), '}'|T]).
ass([not,H, '&', '{', H2, '&', H3, '}'|T]):- ass([atm(not,H), '&', '{', H2, '&', H3, '}'|T]).
ass([H, '&', '{', not,H2, '&', not,H3, '}'|T]):- ass([H, '&', '{', atm(not,H2), '&', atm(not,H3), '}'|T]).
ass([H, '&', '{', not,H2, '&', H3, '}'|T]):- ass([H, '&', '{', atm(not,H2), '&', H3, '}'|T]).
ass([H, '&', '{', H2, '&', not,H3, '}'|T]):- ass([H, '&', '{', H2, '&', H3, '}'|T]).

%%assert not{AVB} 
ass([not, '{', H, 'V', H2, '}'|T]):- wrt([not, '{', H, 'V', H2, '}'], '+'), assert(assprove([not, '{', H, 'V', H2, '}'])), ass(T).
%%assert A&{B&C}
ass([H, '&', '{', H2, '&', H3, '}'|T]):- wrt([H, '&', '{', H2, '&', H3, '}'], '+'), assert(assprove([H, '&', '{', H2, '&', H3, '}'])), ass(T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% the main code for the program
asst(A):- ass(A) ; ( retractall(prf(_,_)), retractall(list(_)), retractall(assprove(_)), retract(noPrint(_,_)), fail ).

printList([], _) :- nl.
printList([atm(not,H)|T], S):- write("not "), write(H), write(", "), write(S),  write(' | '), printList(T, S).
printList([H|T], S) :- H\=atm(not,_), write(H), write(", "), write(S), write(' | '), printList(T, S).

prepareAnswer(L):- findall([Q3], noPrint(Q3, '+'), NP3), findall([Q4], noPrint(Q4, '-'), NP4), prepareAnswer1(L, NP3,NP4).
prepareAnswer1(L, [],[]):- nl, findall(Y, prf(Y, '+'), PL), findall(X, prf(X, '-'), NL), 
    	write('positive literals: '), nl, write("|"), printList(PL, '+'),
    	write('negative literals: '), nl, write("|"), printList(NL, '-'), showCounters(L, PL, NL).
prepareAnswer1(_, [H1|T1],[H2|T2]):- prepareAnswer2([H1|T1], []), prepareAnswer2([], [H2|T2]).
prepareAnswer1(_, [H1|T1],[]):- prepareAnswer2([H1|T1], []).
prepareAnswer1(_, [],[H2|T2]):- prepareAnswer2([], [H2|T2]).
prepareAnswer2([],[]):- fail.
prepareAnswer2([[H]|T],[]):- retract(noPrint(H, '+')), prepareAnswer2(T,[]).
prepareAnswer2([],[[H]|T]):- retract(noPrint(H, '-')), prepareAnswer2([],T).

showCounters(fde, PosL, NegL):- counter(fde,PosL,NegL), findall(Z, list(Z), ZZ), printCounter(fde,ZZ,PosL,NegL), retractall(list(_)). 
showCounters(k3, PosL, NegL):- counter(k3,PosL,NegL), findall(Z, list(Z), ZZ), printCounter(k3,ZZ,PosL,NegL), retractall(list(_)).
showCounters(lp, PosL, NegL):- counter(lp,PosL,NegL), findall(Z, list(Z), ZZ), printCounter(lp,ZZ,PosL,NegL), retractall(list(_)).

counter(fde,PosL,NegL):- membr(fde,PosL,NegL).
counter(k3,PosL,NegL):- membr(fde,PosL,NegL), membr(k3,PosL,PosL).
counter(lp,PosL,NegL):- membr(fde,PosL,NegL), membr(lp,NegL,NegL).
membr(_,[],[]).
membr(_,[],_).
membr(_,_,[]).
membr(fde,[X1|T1],T2):- T2\=[], mbr(X1,T2), membr(fde,T1,T2).
mbr([],[]).
mbr([],_).
mbr(_,[]).
mbr(X,[X|_]):- assert(list([X,+,-])).
mbr(X,[B|T]):- B\=X, mbr(X,T).

membr(k3,[X1|T1],T2):- mbr(k3,X1,T2), membr(k3,T1,T2).
membr(lp,[X1|T1],T2):- mbr(lp,X1,T2), membr(lp,T1,T2).
mbr(_,[],[]).
mbr(_,[],_).
mbr(_,_,[]).
mbr(k3,atm(not,X),[X|_]):- assert(list([atm(not,X),+])).
mbr(k3,X,[atm(not,X)|_]):- assert(list([atm(not,X),+])).
mbr(k3,X,[B|T]):- B\=atm(not,X), X\=atm(not,B), mbr(k3,X,T).
mbr(lp,atm(not,X),[X|_]):- assert(list([atm(not,X),-])).
mbr(lp,X,[atm(not,X)|_]):- assert(list([atm(not,X)],-)).
mbr(lp,X,[B|T]):- B\=atm(not,X), X\=atm(not,B), mbr(lp,X,T).

wr(atm(not,A)):- write("not"), write(A).
wr(A):- A\=atm(not,_), write(A).

printCounter(Logic,[],PL,NL):- write("all branches are open, counter-examples found "), write(Logic), writeln(": "), print(PL, NL).
printCounter(Logic,List,_,_):- List\=[], write("Closed branch "), write(Logic), writeln(": "), printCounter2(List).
printCounter2([]).
printCounter2([[X,+,-]|T]):- write("closed branch has "), wr(X), write(",+ and "), wr(X), writeln(",-"), printCounter2(T).
printCounter2([[atm(not,X),+]|T]):- write("closed branch has not"), wr(X), write(",+ and "), wr(X), writeln(",+"), printCounter2(T).
printCounter2([[atm(not,X),-]|T]):- write("closed branch has not"), wr(X), write(",- and "), wr(X), writeln(",-"), printCounter2(T).

print(PL, NL) :- PL\=[], NL\=[], print(PL,[]), write(" "), print([],NL).
print([],[]).
print([atm(not,H)|T], []):- write("not"), write(H), write(",+ "), print(T, []).
print([H|T], []):- H\=atm(not,_), write(H), write(",+ "), print(T, []).
print([], [atm(not,H)|T]):- write("not"), write(H), write(",- "), print([], T).
print([], [H|T]):- H\=atm(not,_), write(H), write(",- "), print([], T).

wrt([],S):- write(","), writeln(S).
wrt([atm(not,atm(not,atm(not,A)))|T],S):- write("notnotnot"), write(A), wrt(T,S).
wrt([atm(not,atm(not,A))|T],S):- A\=atm(not,_), write("notnot"), write(A), wrt(T,S).
wrt([atm(not,A)|T],S):- A\=atm(not,_), write("not"), write(A), wrt(T,S).
wrt([H|T],S):- H\=atm(not,_), write(H), wrt(T,S).

writeinf:- findall([Q1], noPrint(Q1,'+'), NP1), findall([Q2], noPrint(Q2,'-'), NP2), writeinf(NP1,NP2).
writeinf([],[]):- writeln("inferences solving:").
writeinf([_|_],[]):- fail.
writeinf([],[_|_]):- fail. 
writeinf([_|_],[_|_]):- fail. 

%%prove([premises], '|fde', [inferences]), prove([premises], '|k3', [inferences]), prove([premises], '|lp', [inferences]) 
prove(A, '|',L, C):- C\=[_], C\=[not,_], asst(A), wrt(C, '-'), findall([Z], assprove(Z), AS), check(AS), writeinf, provee(C, '-'), prepareAnswer(L).
prove(A, '|',L, C):- C=[B], ass(A), wrt(C, '-'), assert(prf(B, '-')), findall([Z], assprove(Z), AS), check(AS), prepareAnswer(L).
prove(A, '|',L, C):- C=[not,B], ass(A), wrt(C, '-'), assert(prf(atm(not,B), '-')), findall([Z], assprove(Z), AS), check(AS), prepareAnswer(L).

check(AS):- findall([Q1], noPrint(Q1,'+'), NP1), findall([Q2], noPrint(Q2,'-'), NP2), check(NP1,NP2,AS). 
check([],[],[]):- nl.
check(NP1,NP2,_):- NP1\=[], NP2\=[], fail.
check(NP1,[],_):- NP1\=[], fail.
check([],NP2,_):- NP2\=[], fail.
check([],[],[[H]|T]):- nl, H\=[[]], writeln("premises solving:"), prsolve([[H]|T]), nl.
prsolve([]).
prsolve([[H]|T]):- prove(H, '+'), prsolve(T).

provee(C,'-'):- findall([Q1], noPrint(Q1,'+'), NP1), findall([Q2], noPrint(Q2,'-'), NP2), prove(C,'-',NP1,NP2). 
prove(C,'-',[],[]):- prove(C, '-').
prove(_,'-',[_|_],[]):- fail.
prove(_,'-',[],[_|_]):- fail.
prove(_,'-',[_|_],[_|_]):- fail.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%the real logic behind the code

prove([atm(not,atm(not,(atm(not,H))))|T],S):- T\=['&'|_], T\=['V'|_], wrt([not,not,not,H],S), wrt([not,H],S), assert(prf(atm(not,H),S)), prove(T,S).
prove([atm(not,(atm(not,H)))|T],S):- T\=['&'|_], T\=['V'|_], wrt([not,not,H],S), wrt([H],S), assert(prf(H,S)), prove(T,S).
prove([not,not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,not,H], S), wrt([not,H],S), assert(prf(atm(not,H),S)), prove(T, S).
prove([not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,H], S), wrt([H],S), assert(prf(H,S)), prove(T, S).
prove([not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,H], S), assert(prf(atm(not,H),S)), prove(T, S).

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
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), '+'):- wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B))],'+'), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), wrt([not,not,B], '+'), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).
proof(atm(not,atm(not,A)), 'V', B, '+'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B],'+'), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).
proof(A, 'V', atm(not,atm(not,B)), '+'):- A\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B))],'+'), ( assert(prf(A, '+')), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), wrt([not,not,B], '+'), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).
proof(A, 'V', B, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, 'V', B],'+'), ( assert(prf(A, '+')), wrt([A], '+') ); ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; (retract(prf(B, '+')), assert(noPrint(B,'+')) ).

%%proof(AVBVC+)
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))],'+'), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C, '+'):- C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C],'+'), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C)), '+'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))],'+'), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))],'+'), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), 'V', B, 'V', C, '+'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B, 'V', C],'+'), ( assert(prf(A, '+')), wrt([not,not,A], '+'), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(A, 'V', atm(not,atm(not,B)), 'V', C, '+'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B)), 'V', C],'+'), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([not,not,B], '+'), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(A, 'V', B, 'V', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, 'V', B, 'V', atm(not,atm(not,C))],'+'), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), wrt([not,not,C], '+'), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).
proof(A, 'V', B, 'V', C, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, 'V', B, 'V', C],'+'), ( assert(prf(A, '+')), wrt([A], '+') ) ; ( retract(prf(A, '+')), writeln("\\"), assert(prf(B, '+')), wrt([B], '+') ) ; ( retract(prf(B, '+')), writeln("\\"), assert(prf(C, '+')), wrt([C], '+') ) ; ( retract(prf(C, '+')), assert(noPrint(C,'+')) ).

%%proof(A&B-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '-'):- wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B))],'-'), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), wrt([not,not,B], '-'), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).
proof(atm(not,atm(not,A)), '&', B, '-'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B],'-'), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).
proof(A, '&', atm(not,atm(not,B)), '-'):- A\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B))],'-'), ( assert(prf(A, '-')), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), wrt([not,not,B], '-'), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).
proof(A, '&', B, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, '&', B],'-'), ( assert(prf(A, '-')), wrt([A], '-') ); ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; (retract(prf(B, '-')), assert(noPrint(B,'-')) ).

%%proof(A&B&C-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))],'-'), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), wrt([not,not,C], '-'), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C, '-'):- C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C],'-'), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C)), '-'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))],'-'), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), wrt([not,not,C], '-'), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))],'-'), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), wrt([not,not,C], '-'), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(atm(not,atm(not,A)), '&', B, '&', C, '-'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B, '&', C],'-'), ( assert(prf(A, '-')), wrt([not,not,A], '-'), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', atm(not,atm(not,B)), '&', C, '-'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B)), '&', C],'-'), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([not,not,B], '-'), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', B, '&', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, '&', B, '&', atm(not,atm(not,C))],'-'), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), wrt([not,not,C], '-'), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
proof(A, '&', B, '&', C, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, '&', B, '&', C],'-'), ( assert(prf(A, '-')), wrt([A], '-') ) ; ( retract(prf(A, '-')), writeln("\\"), assert(prf(B, '-')), wrt([B], '-') ) ; ( retract(prf(B, '-')), writeln("\\"), assert(prf(C, '-')), wrt([C], '-') ) ; ( retract(prf(C, '-')), assert(noPrint(C,'-')) ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%simplify prove{A&B}+/- prove{AVB}+/-
prove(['{', not,not,not, A, B, not,not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,atm(not,C))), S), prove(T, S).
prove(['{', not,not,not, A, B, not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,atm(not,A))), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not,not,not, A, B, not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,atm(not,A))), B, atm(not,C), S), prove(T, S).
prove(['{', not,not,not, A, B, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_),  proof(atm(not,atm(not,atm(not,A))), B, C, S), prove(T, S).
prove(['{', not,not, A, B, not,not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,A)), B, atm(not,atm(not,atm(not,C))), S), prove(T, S).
prove(['{', not,not, A, B, not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,A)), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not,not, A, B, not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,atm(not,A)), B, atm(not,C), S), prove(T, S).
prove(['{', not,not, A, B, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_),  proof(atm(not,atm(not,A)), B, C, S), prove(T, S).
prove(['{', not, A, B, not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,A), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not, A, B, not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,A), B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', not, A, B, not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(atm(not,A), B, atm(not,C), S), prove(T, S).
prove(['{', not, A, B, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_),  proof(atm(not,A), B, C, S), prove(T, S).
prove(['{', A, B, not,not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(A, B, atm(not,atm(not,atm(not,C))), S), prove(T, S).
prove(['{', A, B, not,not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(A, B, atm(not,atm(not,C)), S), prove(T, S).
prove(['{', A, B, not, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), proof(A, B, atm(not,C), S), prove(T, S).
prove(['{', A, B, C, '}'|T], S):- T\=['V'|_], T\=['&'|_], A\=not, C\=not, A\=atm(not,_), C\=atm(not,_), B\=not, B\=atm(not,_), proof(A, B, C, S), prove(T, S).
%%simplify prove(A&{B&C})+/- prove(A&{BVC})+/- prove(AV{B&C})+/- prove(AV{BVC})+/-
prove([not,not,H, S1, '{', not,H2, S2, not,H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', atm(not,H2), S2, atm(not,H3), '}'], S3), prove(T,S3).
prove([not,not,H, S1, '{', not,H2, S2, H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', atm(not,H2), S2, H3, '}'], S3), prove(T,S3).
prove([not,not,H, S1, '{', H2, S2, not,H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', H2, S2, atm(not,H3), '}'], S3), prove(T,S3).
prove([not,not,H, S1, '{', H2, S2, H3, '}'|T], S3):- prove([atm(not,atm(not,H)), S1, '{', H2, S2, H3, '}'], S3), prove(T,S3).
prove([not,H, S1, '{', not,H2, S2, not,H3, '}'|T], S3):- H\=not, S1\=not, prove([atm(not,H), S1, '{', atm(not,H2), S2, atm(not,H3), '}'|T], S3).
prove([not,H, S1, '{', not,H2, S2, H3, '}'|T], S3):- H\=not, S1\=not, prove([atm(not,H), S1, '{', atm(not,H2), S2, H3, '}'|T], S3).
prove([not,H, S1, '{', H2, S2, not,H3, '}'|T], S3):- H\=not, S1\=not, prove([atm(not,H), S1, '{', H2, S2, atm(not,H3), '}'|T], S3).
prove([not,H, S1, '{', H2, S2, H3, '}'|T], S3):- H\=not, S1\=not, prove([atm(not,H), S1, '{', H2, S2, H3, '}'|T], S3).
prove([H, S1, '{', not,H2, S2, not,H3, '}'|T], S3):- H\=not, S1\=not, prove([H, S1, '{', atm(not,H2), S2, atm(not,H3), '}'|T], S3).
prove([H, S1, '{', not,H2, S2, H3, '}'|T], S3):- H\=not, S1\=not, prove([H, S1, '{', atm(not,H2), S2, H3, '}'|T], S3).
prove([H, S1, '{', H2, S2, not,H3, '}'|T], S3):- H\=not, S1\=not, prove([H, S1, '{', H2, S2, atm(not,H3), '}'|T], S3).

prove([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'|T], '+'):- wrt([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'|T], '+'), wrt([atm(not,atm(not,H))],'+'), wrt([H],'+'), assert(prf(H, '+')), wrt(['{', H2, '&', H3, '}'], '+'), wrt([H2], '+'), assert(prf(H2, '+')), wrt([H3], '+'), assert(prf(H3, '+')), prove(T, '+').
prove([H, '&', '{', H2, '&', H3, '}'|T], '+'):- H\=atm(not,atm(not,_)), wrt([H, '&', '{', H2, '&', H3, '}'|T], '+'), wrt([H],'+'), assert(prf(H, '+')), wrt(['{', H2, '&', H3, '}'], '+'), wrt([H2], '+'), assert(prf(H2, '+')), wrt([H3], '+'), assert(prf(H3, '+')), prove(T, '+').

prove([atm(not,atm(not,H)), '&', '{', H2, 'V', H3, '}'|T], '+'):- wrt([atm(not,atm(not,H)), '&', '{', H2, 'V', H3, '}'|T], '+'), wrt([atm(not,atm(not,H))], '+'), wrt([H],'+'), assert(prf(H, '+')), wrt([H2,'V',H3], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), prove(T, '+').
prove([H, '&', '{', H2, 'V', H3, '}'|T], '+'):- H\=atm(not,atm(not,_)), wrt([H, '&', '{', H2, 'V', H3, '}'|T], '+'), wrt([H], '+'), assert(prf(H, '+')), wrt([H2,'V',H3], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), prove(T, '+').

prove([atm(not,atm(not,H)), 'V', '{', H2, '&', H3, '}'|T], '-'):- wrt([atm(not,atm(not,H)), 'V', '{', H2, '&', H3, '}'|T], '-'), wrt([atm(not,atm(not,H))], '-'), wrt([H],'-'), assert(prf(H, '-')), wrt([H2,'&',H3], '-'), write("  /\\"), proof(H2, '&', H3, '-'), prove(T, '+').
prove([H, 'V', '{', H2, '&', H3, '}'|T], '-'):- H\=atm(not,atm(not,_)), wrt([H, 'V', '{', H2, '&', H3, '}'|T], '-'), wrt([H], '-'), assert(prf(H, '-')), wrt([H2,'&',H3], '-'), write("  /\\"), proof(H2, '&', H3, '-'), prove(T, '+').

prove([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'|T], '-'):- wrt([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'|T], '-'), wrt([atm(not,atm(not,H))], '-'), wrt([H],'-'), assert(prf(H, '-')), wrt(['{', H2, 'V', H3, '}'], '-'), wrt([H2], '-'), assert(prf(H2, '-')), wrt([H3], '-'), assert(prf(H3, '-')), prove(T, '-'). 
prove([H, 'V', '{', H2, 'V', H3, '}'|T], '-'):- H\=atm(not,atm(not,_)), wrt([H, 'V', '{', H2, 'V', H3, '}'|T], '-'), wrt([H], '-'), assert(prf(H, '-')), wrt(['{', H2, 'V', H3, '}'], '-'), wrt([H2], '-'), assert(prf(H2, '-')), wrt([H3], '-'), assert(prf(H3, '-')), prove(T, '-'). 


%%%%%%%%%%%%%%%%%%%verschilmetBFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
prove([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'|T], '+'):- wrt([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'|T], '+'), ( write("  /\\"), assert(prf(H, '+')), wrt([atm(not,atm(not,H))], '+'), wrt([H], '+'), prove(T, '+') ) ; ( retract(prf(H, '+')), writeln("\\"), wrt(['{',H2, 'V', H3,'}'], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), prove(T, '+') ).
prove([H, 'V', '{', H2, 'V', H3, '}'|T], '+'):- H\=atm(not,atm(not,_)), wrt([H, 'V', '{', H2, 'V', H3, '}'|T], '+'), ( write("  /\\"), assert(prf(H, '+')), wrt([H], '+'), prove(T, '+') ) ; ( retract(prf(H, '+')), writeln("\\"), wrt(['{',H2, 'V', H3,'}'], '+'), write("  /\\"), proof(H2, 'V', H3, '+'), prove(T, '+') ).

%prove([H, '&', '{', H2, 'V', H3, '}'|T], '-'):- ( write("  /\\"), assert(prf(H, '-')), wrt([H], '-'), prove(T, '-') ) ; ( retract(prf(H, '-')), writeln("\\"), wrt([H2, 'V', H3], '-'), proof(H2, 'V', H3, '-'), prove(T, '-') ).
%prove([H, 'V', '{', H2, '&', H3, '}'|T], '+'):- ( write("  /\\"), assert(prf(H, '+')), wrt([H], '+'), prove(T, '+') ) ; ( retract(prf(H, '+')), writeln("\\"), wrt([H2, '&', H3], '+'), proof(H2, '&', H3, '+'), prove(T, '+') ).

prove([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'|T], '-'):- wrt([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'|T], '-'), ( write("  /\\"), assert(prf(H, '-')), wrt([atm(not,atm(not,H))], '-'), wrt([H], '-'), prove(T, '-') ) ; ( retract(prf(H, '-')), writeln("\\"), wrt(['{',H2, '&', H3,'}'], '-'), write("  /\\"), proof(H2, '&', H3, '-'), prove(T, '-') ).
prove([H, '&', '{', H2, '&', H3, '}'|T], '-'):- H\=atm(not,atm(not,_)), wrt([H, '&', '{', H2, '&', H3, '}'|T], '-'), ( write("  /\\"), assert(prf(H, '-')), wrt([H], '-'), prove(T, '-') ) ; ( retract(prf(H, '-')), writeln("\\"), wrt(['{',H2, '&', H3,'}'], '-'), write("  /\\"), proof(H2, '&', H3, '-'), prove(T, '-') ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%simplify prove(A&B)+/- prove(AVB)+/- 
prove([not,not,not, H, S1, not,not,not, H3|T], S2):- S1\='{', S1\=not, H\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([not,not,not, H, S1, not,not, H3|T], S2):- S1\='{', S1\=not, H\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, atm(not,atm(not,H3))|T], S2).
prove([not,not,not, H, S1, not, H3|T], S2):- S1\='{', S1\=not, H3\='{', H\=not, H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, atm(not,H3)|T], S2).
prove([not,not,not, H, S1, H3|T], S2):- S1\='{', S1\=not, H3\='{', H\=not, H\='{', H\=not, H3\='{', H3\=not,  T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,atm(not,H))), S1, H3|T], S2).
prove([not,not, H, S1, not,not,not, H3|T], S2):- S1\='{', S1\=not, H\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([not,not, H, S1, not,not, H3|T], S2):- S1\='{', S1\=not, H\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H3))|T], S2).
prove([not,not, H, S1, not, H3|T], S2):- S1\='{', S1\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, atm(not,H3)|T], S2).
prove([not,not, H, S1, H3|T], S2):- S1\='{', S1\=not, H3\='{', H\='{', H\=not, H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,atm(not,H)), S1, H3|T], S2).
prove([not, H, S1 ,not,not,not, H3|T], S2):- H\=not, S1\='{', S1\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([not, H, S1 ,not,not, H3|T], S2):- H\=not, S1\='{', S1\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, atm(not,atm(not,H3))|T], S2).
prove([not, H, S1,not, H3|T], S2):- H\=not, S1\='{', S1\=not, H3\='{', H\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, atm(not,H3)|T], S2).
prove([not, H, S1 , H3|T], S2):- H\=not, S1\='{', S1\=not, H3\='{', H\='{', H\=not, S1\=not, H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([atm(not,H), S1, H3|T], S2).
prove([H, S1, not,not,not, H3|T], S2):- H\=not, S1\='{', S1\=not, H3\='{', S1\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([H, S1, atm(not,atm(not,atm(not,H3)))|T], S2).
prove([H, S1, not,not, H3|T], S2):- H\=not, S1\='{', S1\=not, H3\='{', S1\='{', H3\=not, T\=['&'|_], T\=['V'|_], prove([H, S1, atm(not,atm(not,H3))|T], S2).
prove([H, S1, not, H3|T], S2):- H\=not, S1\='{', S1\=not, H3\='{', S1\='{', S1\=not, H3\=not, T\=['&'|_], T\=['V'|_], prove([H, S1, atm(not,H3)|T], S2).

%%prove(A&B+)
prove([H,'&',H3|T], '+'):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], wrt([H, '&', H3], '+'), proof(H, '&', H3, '+'), prove(T, '+').
%%prove(AVB+)
prove([H,'V',H3|T], '+'):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], wrt([H, 'V', H3], '+'), write("/\\"), proof(H, 'V', H3, '+'), prove(T, '+').
%%prove(A&B-)
prove([H,'&',H3|T], '-'):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], wrt([H, '&', H3], '-'), write("/\\"), proof(H, '&', H3, '-'), prove(T, '-').
%%prove(AVB-)
prove([H,'V',H3|T], '-'):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], wrt([H, 'V', H3], '-'), proof(H, 'V', H3, '-'), prove(T, '-').

%%simplify prove(A&B&C)+/- prove{A&B&C-} prove(AVBVC)+/-
prove([not,not, H, S1, not,not, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H2)), S2, atm(not,atm(not,H3))|T], S3).
prove([not,not, H, S1, not,not, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H2)), S2, atm(not,H3)|T], S3).
prove([not,not, H, S1, not,not, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H2\=not, H3\=not, H3\='V', H3\='&', prove([atm(not,atm(not,H)), S1, atm(not,atm(not,H2)), S2, H3|T], S3).
prove([not,not, H, S1, not, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,H2), S2, atm(not,atm(not,H3))|T], S3).
prove([not,not, H, S1, not, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,atm(not,H)), S1, atm(not,H2), S2, atm(not,H3)|T], S3).
prove([not,not, H, S1, not, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H2\=not, H3\=not, H3\='V', H3\='&', prove([atm(not,atm(not,H)), S1, atm(not,H2), S2, H3|T], S3).
prove([not,not, H, S1, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,atm(not,H)), S1, H2, S2, atm(not,atm(not,H3))|T], S3).
prove([not,not, H, S1, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,atm(not,H)), S1, H2, S2, atm(not,H3)|T], S3).
prove([not,not, H, S1, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H2\=not, H3\=not, H3\='V', H3\='&', prove([atm(not,atm(not,H)), S1, H2, S2, H3|T], S3).
prove([not, H, S1, not,not, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,H), S1, atm(not,atm(not,H2)), S2, atm(not,atm(not,H3))|T], S3).
prove([not, H, S1, not,not, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,H), S1, atm(not,atm(not,H2)), S2, atm(not,H3)|T], S3).
prove([not, H, S1, not,not, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H2\=not, H3\=not, H3\='V', H3\='&', prove([atm(not,H), S1, atm(not,atm(not,H2)), S2, H3|T], S3).
prove([not, H, S1, not, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,H), S1, atm(not,H2), S2, atm(not,atm(not,H3))|T], S3).
prove([not, H, S1, not, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,H), S1, atm(not,H2), S2, atm(not,H3)|T], S3).
prove([not, H, S1, not, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H2\=not, H3\=not, H3\='V', H3\='&', prove([atm(not,H), S1, atm(not,H2), S2, H3|T], S3).
prove([not, H, S1, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,H), S1, H2, S2, atm(not,atm(not,H3))|T], S3).
prove([not, H, S1, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H3\=not, prove([atm(not,H), S1, H2, S2, atm(not,H3)|T], S3).
prove([not, H, S1, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, H\='{', H2\=not, H3\=not, H3\='V', H3\='&', prove([atm(not,H), S1, H2, S2, H3|T], S3).
prove([H, S1, not,not, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H3\=not, prove([H, S1, atm(not,atm(not,H2)), S2, atm(not,atm(not,H3))|T], S3).
prove([H, S1, not,not, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H3\=not, prove([H, S1, atm(not,atm(not,H2)), S2, atm(not,H3)|T], S3).
prove([H, S1, not,not, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H3\=not, H3\='V', H3\='&', prove([H, S1, atm(not,atm(not,H2)), S2, H3|T], S3).
prove([H, S1, not, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H3\=not, prove([H, S1, atm(not,H2), S2, atm(not,atm(not,H3))|T], S3).
prove([H, S1, not, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H3\=not, prove([H, S1, atm(not,H2), S2, atm(not,H3)|T], S3).
prove([H, S1, not, H2, S2, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H2\=not, H3\=not, H3\='V', H3\='&', prove([H, S1, atm(not,H2), S2, H3|T], S3).
prove([H, S1, H2, S2, not,not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H3\=not, prove([H, S1, H2, S2, atm(not,atm(not,H3))|T], S3).
prove([H, S1, H2, S2, not, H3|T], S3):- H\=not, S2\='{', S2\=not, S1\=not, S1\='{', H3\=not, prove([H, S1, H2, S2, atm(not,H3)|T], S3).

%%prove(A&B&C+)
prove([H,'&',H2,'&',H3|T], '+'):- H3\='{', H3\=not, wrt([H,'&',H2,'&',H3], '+'), proof(H, '&', H2, '&', H3, '+'), prove(T, '+').
%%prove(AVBVC+)
prove([H,'V',H2,'V',H3|T], '+'):- H3\='{', H3\=not, wrt([H,'V',H2,'V',H3], '+'), write("  /\\"), proof(H, 'V', H2, 'V', H3, '+'), prove(T, '+').
%%prove(A&B&C-)
prove([H,'&',H2,'&',H3|T], '-'):- H3\='{', H3\=not, wrt([H,'&',H2,'&',H3], '-'), write("  /\\"), proof(H, '&', H2, '&', H3, '-'), prove(T, '-').
%%prove(AVBVC-)
prove([H,'V',H2,'V',H3|T], '-'):- H3\='{', H3\=not, wrt([H,'V',H2,'V',H3], '-'), proof(H, 'V', H2, 'V', H3, '-'), prove(T, '-').

prove(['{', H, '&', H2, '}', '&', H3|T], S):- wrt(['{', H, '&', H2, '}', '&', H3], S), prove([H, '&', H2, '&', H3|T], S).
prove(['{', H, 'V', H2, '}', 'V', H3|T], S):- wrt(['{', H, 'V', H2, '}', 'V', H3], S), prove([H, 'V', H2, 'V', H3|T], S).
prove(['{', H, '&', H2, '}', 'V', H3|T], '+'):- wrt(['{', H, '&', H2, '}', 'V', H3], '+'), prove([H3, 'V', '{', H, '&', H2, '}'|T], '+').  
prove(['{', H, 'V', H2, '}', '&', H3|T], '+'):- wrt(['{', H, 'V', H2, '}', '&', H3], '+'), prove([H3, '&', '{', H, 'V', H2, '}'|T], '+').
prove(['{', H, '&', H2, '}', 'V', H3|T], '-'):- wrt(['{', H, '&', H2, '}', 'V', H3], '-'), prove([H3, 'V', '{', H, '&', H2, '}'|T], '-').
prove(['{', H, 'V', H2, '}', '&', H3|T], '-'):- wrt(['{', H, 'V', H2, '}', '&', H3], '-'), prove([H3, '&', '{', H, 'V', H2, '}'|T], '-').

%%simplify notnot{A&B}+/- notnot{AVB}+/-
prove([not,not, '{', not,not,H, AO, not,not,H2, '}'|T], S):- prove([not,not, '{', atm(not,atm(not,H)), AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not,not, '{', not,not,H, AO, not,H2, '}'|T], S):- prove([not,not, '{', atm(not,atm(not,H)), AO, atm(not,H2), '}'|T], S).
prove([not,not, '{', not,not,H, AO, H2, '}'|T], S):- prove([not,not, '{', atm(not,atm(not,H)), AO, H2, '}'|T], S).
prove([not,not, '{', not,H, AO, not,not,H2, '}'|T], S):- prove([not,not, '{', atm(not,H), AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not,not, '{', not,H, AO, not,H2, '}'|T], S):- prove([not,not, '{', atm(not,H), AO, atm(not,H2), '}'|T], S).
prove([not,not, '{', not,H, AO, H2, '}'|T], S):- prove([not,not, '{', atm(not,H), AO, H2, '}'|T], S).
prove([not,not, '{', H, AO, not,not,H2, '}'|T], S):- prove([not,not, '{', H, AO, atm(not,atm(not,H2)), '}'|T], S).
prove([not,not, '{', H, AO, not,H2, '}'|T], S):- prove([not,not, '{', H, AO, atm(not,H2), '}'|T], S).
%%simplify not{A&B}+/- not{AVB}+/-
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
