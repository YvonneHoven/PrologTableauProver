%% making functions dynamic to be able to use assert & discontiguous to be able to put all functions not necessarily side by side
:- dynamic prf(_,_).
:- dynamic prf(_,_,_).
:- dynamic assprove(_).
:- dynamic toprove/2.
:- dynamic list(_).
:- discontiguous proof/6.
:- discontiguous proof/4.
:- discontiguous toprove/2.
:- discontiguous prove/2.
:- discontiguous finprove/2.
:- discontiguous finprove/6.
:- discontiguous prove/4.
:- discontiguous membr/3.


%% all assertions of the premises
ass([]).
ass([not,not,not, H]):- wrt([not,not,not, H], '+'), assert(assprove([not,not,not,H])).  
ass([not,not, H]):- wrt([not,not, H], '+'), assert(assprove([not,not,H])).
ass([not, H]):- wrt([atm(not,H)], '+'), assert(prf(atm(not,H), '+')).
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
ass([A, '&', C|T]):- A\=not, C\=not, C\='{', wrt([A,'&',C], '+'), write(" "), ass(T), assert(assprove([A, '&', C])).

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
%%simplify assert not{A&B} 
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
ass([not, '{', H, 'V', H2, '}'|T]):- wrt([not, '{', H, 'V', H2, '}'], '+'), assert(assprove([not, '{', H, 'V', H2, '}'])), write(" "), ass(T).
%%assert A&{B&C}
ass([H, '&', '{', H2, '&', H3, '}'|T]):- wrt([H, '&', '{', H2, '&', H3, '}'], '+'), assert(assprove([H, '&', '{', H2, '&', H3, '}'])), write(" "), ass(T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% the main code for the program
printList([], _).
printList([atm(not,H)|T], S):- write("not "), write(H), write(", "), write(S),  write(' | '), printList(T, S).
printList([H|T], S) :- H\=atm(not,_), write(H), write(", "), write(S), write(' | '), printList(T, S).

final(L,P,_):- L\=lp, search(L,P,+).
final(lp,_,N):- search(lp,N,-).

search(_,[],_):- write("No other facts about rho obtain").
search(L,[H|T],+):- H\=atm(not,_), write(H), writeln(" is related to true (1)"), search(L,T,+).
search(L,[H|T],+):- H=atm(not,B), write(B), writeln(" is related to false (0)"), search(L,T,+).
search(lp,[H|T],-):- H\=atm(not,_), search(lp,T,-).
search(lp,[H|T],-):- H=atm(not,_), search(lp,T,-).

prepareAnswer(L):- findall(Y, prf(Y, '+'), PL), findall(X, prf(X, '-'), NL), findall(YY, prf(1,YY, '+'), PoL), findall(XX, prf(1,XX, '-'), NeL), findall(YYY, prf(2,YYY, '+'), PosL), findall(XXX, prf(2,XXX, '-'), NegL), findall(YYYY, prf(3,YYYY, '+'), PosiL), findall(XXXX, prf(3,XXXX, '-'), NegaL),
    	prepareAnswer2(L,PL,NL,PoL,NeL,PosL,NegL,PosiL,NegaL).
        
prepareAnswer2(L,PL,NL,[],[],[],[],[],[]):-  
        write('positive literals: '), nl, write("|"), printList(PL, '+'), nl,
    	write('negative literals: '), nl, write("|"), printList(NL, '-'), nl, showCounters(L, PL, NL).
        
prepareAnswer2(L,PL,NL,PoL,NeL,_,_,_,_):- (PoL\=[]; NeL\=[]),
    	write('positive literals: '), nl, write("|"), printList(PL, '+'), printList(PoL, '+'), nl, 
    	write('negative literals: '), nl, write("|"), printList(NL, '-'), printList(NeL, '-'), nl, showAllCounters(1,L,PL,NL,PoL,NeL).
        
prepareAnswer2(L,PL,NL,_,_,PosL,NegL,_,_):- (PosL\=[]; NegL\=[]),
        write('positive literals: '), nl, write("|"), printList(PL, '+'), printList(PosL, '+'), nl,
    	write('negative literals: '), nl, write("|"), printList(NL, '-'), printList(NegL, '-'), nl, showAllCounters(2,L,PL,NL,PosL,NegL).
        
prepareAnswer2(L,PL,NL,_,_,_,_,PosiL,NegaL):- (PosiL\=[]; NegaL\=[]),
        write('positive literals: '), nl, write("|"), printList(PL, '+'), printList(PosiL, '+'), nl,
    	write('negative literals: '), nl, write("|"), printList(NL, '-'), printList(NegaL, '-'), nl, showAllCounters(3,L,PL,NL,PosiL,NegaL).

showAllCounters(Num,L,PL,NL,P,N):- append(PL,P,Positive), append(NL,N,Negative), showCounters(Num,L,Positive,Negative).

showCounters(Num,fde, PosL, NegL):- counter(fde,PosL,NegL), findall(Z, list(Z), ZZ), printCounter(Num,fde,ZZ,PosL,NegL), retractall(list(_)). 
showCounters(Num,k3, PosL, NegL):- counter(k3,PosL,NegL), findall(Z, list(Z), ZZ), printCounter(Num,k3,ZZ,PosL,NegL), retractall(list(_)).
showCounters(Num,lp, PosL, NegL):- counter(lp,PosL,NegL), findall(Z, list(Z), ZZ), printCounter(Num,lp,ZZ,PosL,NegL), retractall(list(_)).

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
mbr(k3,X,[atm(not,X)|_]):- assert(list([atm(not,X),+])).
mbr(k3,X,[B|T]):- B\=atm(not,X), mbr(k3,X,T).
mbr(lp,X,[atm(not,X)|_]):- assert(list([atm(not,X),-])).
mbr(lp,X,[B|T]):- B\=atm(not,X), mbr(lp,X,T).

wr(atm(not,A)):- write("not"), write(A).
wr(A):- A\=atm(not,_), write(A).

printCounter(Num,Logic,[],PL,NL):- write("branch #"), write(Num), write(" "), write(Logic), write(" is open, counter-example found "), write(Logic), writeln(": "), print(PL, NL), nl, final(Logic,PL,NL).
printCounter(Num,Logic,List,_,_):- List\=[], printCounter2(Logic,Num,List).
printCounter2(_,_,[]).
printCounter2(Logic,Num,[[X,+,-]|T]):- write("Closed branch "), write(Logic), write(" #"), write(Num), write(" has "), wr(X), write(",+ and "), wr(X), writeln(",-"), printCounter2(Logic,Num,T).
printCounter2(Logic,Num,[[atm(not,X),+]|T]):- write("Closed branch "), write(Logic), write(" #"), write(Num), write(" has not"), wr(X), write(",+ and "), wr(X), writeln(",+"), printCounter2(Logic,Num,T).
printCounter2(Logic,Num,[[atm(not,X),-]|T]):- write("Closed branch "), write(Logic), write(" #"), write(Num), write(" has not"), wr(X), write(",- and "), wr(X), writeln(",-"), printCounter2(Logic,Num,T).

printCounter(Logic,[],PL,NL):- write("branch is open, counter-example found "), write(Logic), writeln(": "), print(PL, NL), nl, final(Logic,PL,NL).
printCounter(Logic,List,_,_):- List\=[], printCounter2(Logic,List).
printCounter2(_,[]).
printCounter2(Logic,[[X,+,-]|T]):- write("Closed branch "), write(Logic), write(" has "), wr(X), write(",+ and "), wr(X), writeln(",-"), printCounter2(Logic,T).
printCounter2(Logic,[[atm(not,X),+]|T]):- write("Closed branch "), write(Logic), write(" has not"), wr(X), write(",+ and "), wr(X), writeln(",+"), printCounter2(Logic,T).
printCounter2(Logic,[[atm(not,X),-]|T]):- write("Closed branch "), write(Logic), write(" has not"), wr(X), write(",- and "), wr(X), writeln(",-"), printCounter2(Logic,T).

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

asst(A):- retractall(prf(_,_)), retractall(prf(_,_,_)), ass(A).

%%prove([premises], '|fde', [inferences]), prove([premises], '|k3', [inferences]), prove([premises], '|lp', [inferences]) 
prove(A, '|',L, C):- C\=[_], C\=[not,_], asst(A), wrt(C, '-'), nl, findall([Z], assprove(Z), AS), check(AS), writeln("inferences solving:"), prove(C, '-'), findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP), check(TP, FP), nl, prepareAnswer(L).
prove(A, '|',L, C):- C=[B], asst(A), wrt(C, '-'), assert(prf(B, '-')), nl, findall([Z], assprove(Z), AS), check(AS), findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP), check(TP, FP), nl, prepareAnswer(L).
prove(A, '|',L, C):- C=[not,B], asst(A), wrt(C, '-'), assert(prf(atm(not,B), '-')), nl, findall([Z], assprove(Z), AS), check(AS), findall([Y], toprove(Y, '+'), TP), findall([X], toprove(X, '-'), FP), check(TP, FP), nl, prepareAnswer(L).

check(TP, FP):- TP\=[], FP\=[], nl, write("//"), finprove(TP, '+'), finprove(FP, '-'), retractall(toprove(_,_)).
check(TP, []):- TP\=[], nl, write("//"), finprove(TP, '+'), retractall(toprove(_,_)).
check([], FP):- FP\=[], nl, write("//"), finprove(FP, '-'), retractall(toprove(_,_)).
check([], []).

check([]).
check([[H]|T]):- H\=[[]], writeln("premises solving:"), prsolve([[H]|T]), nl, retractall(assprove(_)).
prsolve([]).
prsolve([[H]|T]):- prove(H, '+'), prsolve(T).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%the real logic behind the code

prove([atm(not,atm(not,(atm(not,H))))|T],S):- T\=['&'|_], T\=['V'|_], wrt([not,not,not,H],S), wrt([not,H],S), assert(prf(atm(not,H),S)), prove(T,S).
prove([atm(not,(atm(not,H)))|T],S):- T\=['&'|_], T\=['V'|_], wrt([not,not,H],S), wrt([H],S), assert(prf(H,S)), prove(T,S).
prove([not,not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,not,H], S), wrt([not,H],S), assert(prf(atm(not,H),S)), prove(T, S).
prove([not,not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,not,H], S), wrt([H],S), assert(prf(H,S)), prove(T, S).
prove([not, H|T], S):- H\='{', H\=not, T\=['&'|_], T\=['V'|_], wrt([not,H], S), assert(prf(atm(not,H),S)), prove(T, S). 

prfwrt(atm(not,atm(not,atm(not,A))), S):- A\=atm(not,_), write("notnotnot"), write(A), write(","), write(S). 
prfwrt(atm(not,atm(not,A)), S):- A\=atm(not,_), write("notnot"), write(A), write(","), write(S). 
prfwrt(atm(not,A), S):- A\=atm(not,_), write("not"), write(A), write(","), write(S).  
prfwrt(A,S):- A\=atm(not,_), write(A), write(","), write(S).
prfwrt([],S):- write(","), writeln(S).

finprove([],_).
finprove([[H]|T], S):- finprove(H, S), finprove(T,S).
prove([H|[]], S):- H\=[_], H\=not, H\=atm(not,_), wrt([H], S), assert(prf(H, S)).
prove([], _).

%%proof(A&B+) proof(A&B&C+)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '+'):- wrt([not,not,A], '+'), wrt([not,not,B], '+'), wrt([A], '+'), wrt([B], '+'), assert(prf(A,'+')), assert(prf(B,'+')).
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
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), '-'):- wrt([not,not,A], '-'), wrt([not,not,B], '-'), wrt([A], '-'), wrt([B], '-'), assert(prf(A,'-')), assert(prf(B,'-')).
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


%%%%%%%%%%%%%%%verschilmetDFS%%%%%%%%%%%%%%%%%%%%%%%%
%%proof(AVB+) 
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B))], '+'), assert(toprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B))], '+')).
proof(atm(not,atm(not,A)), 'V', B, '+'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B], '+'), assert(toprove([atm(not,atm(not,A)), 'V', B], '+')).
proof(A, 'V', atm(not,atm(not,B)), '+'):- A\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B))], '+'), assert(toprove([A, 'V', atm(not,atm(not,B))], '+')).
proof(A, 'V', B, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, 'V', B], '+'), assert(toprove([A, 'V', B], '+')).
finprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B))], '+'):- wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B))], '+'), prfwrt(atm(not,atm(not,A)), '+'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '+'), nl, prfwrt(A, '+'), write("   OR   "), wrt([B], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')).
finprove([atm(not,atm(not,A)), 'V', B], '+'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B], '+'), prfwrt(atm(not,atm(not,A)), '+'), write("   OR   "), prfwrt(B, '+'), nl, prfwrt(A, '+'), write("   OR   "), wrt([B], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')).
finprove([A, 'V', atm(not,atm(not,B))], '+'):- A\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B))], '+'), prfwrt(A, '+'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '+'), nl, prfwrt(A, '+'), write("   OR   "), wrt([B], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')).
finprove([A, 'V', B], '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, 'V', B], '+'), prfwrt(A, '+'), write("   OR   "), wrt([B], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')).

%%proof(AVBVC+)
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'), assert(tofinprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+')).
proof(atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C, '+'):- C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C], '+'), assert(toprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C], '+')).
proof(atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C)), '+'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))], '+'), assert(toprove([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))], '+')).
proof(A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'), assert(toprove([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+')).
proof(atm(not,atm(not,A)), 'V', B, 'V', C, '+'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B, 'V', C], '+'), assert(toprove([atm(not,atm(not,A)), 'V', B, 'V', C], '+')).
proof(A, 'V', atm(not,atm(not,B)), 'V', C, '+'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B)), 'V', C], '+'), assert(toprove([A, 'V', atm(not,atm(not,B)), 'V', C], '+')).
proof(A, 'V', B, 'V', atm(not,atm(not,C)), '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, 'V', B, 'V', atm(not,atm(not,C))], '+'), assert(toprove([A, 'V', B, 'V', atm(not,atm(not,C))], '+')).
proof(A, 'V', B, 'V', C, '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, 'V', B, 'V', C], '+'), assert(toprove([A, 'V', B, 'V', C], '+')).
finprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'), prfwrt(atm(not,atm(not,A)), '+'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '+'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '+'), nl, prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).
finprove([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C], '+'):- C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', atm(not,atm(not,B)), 'V', C], '+'), prfwrt(atm(not,atm(not,A)), '+'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '+'), write("   OR   "), prfwrt(C, '+'), nl, prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).
finprove([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))], '+'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B, 'V', atm(not,atm(not,C))], '+'), prfwrt(atm(not,atm(not,A)), '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '+'), nl, prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).
finprove([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'):- A\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B)), 'V', atm(not,atm(not,C))], '+'), prfwrt(A, '+'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '+'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '+'), nl, prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).
finprove([atm(not,atm(not,A)), 'V', B, 'V', C], '+'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), 'V', B, 'V', C], '+'), prfwrt(atm(not,atm(not,A)), '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), prfwrt(C, '+'), nl, prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).
finprove([A, 'V', atm(not,atm(not,B)), 'V', C], '+'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, 'V', atm(not,atm(not,B)), 'V', C], '+'), prfwrt(A, '+'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '+'), write("   OR   "), prfwrt(C, '+'), nl, prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).
finprove([A, 'V', B, 'V', atm(not,atm(not,C))], '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, 'V', B, 'V', atm(not,atm(not,C))], '+'), prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '+'), nl, prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).
finprove([A, 'V', B, 'V', C], '+'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, 'V', B, 'V', C], '+'), prfwrt(A, '+'), write("   OR   "), prfwrt(B, '+'), write("   OR   "), wrt([C], '+'), assert(prf(1,A,'+')), assert(prf(2,B,'+')), assert(prf(3,C,'+')).

%%proof(A&B-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B))], '-'), assert(toprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B))], '-')).
proof(atm(not,atm(not,A)), '&', B, '-'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B], '-'), assert(toprove([atm(not,atm(not,A)), '&', B], '-')).
proof(A, '&', atm(not,atm(not,B)), '-'):- A\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B))], '-'), assert(toprove([A, '&', atm(not,atm(not,B))], '-')).
proof(A, '&', B, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, '&', B], '-'), assert(toprove([A, '&', B], '-')).
finprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B))], '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B))], '-'), prfwrt(atm(not,atm(not,A)), '-'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '-'), nl, prfwrt(A, '-'), write("   OR   "), wrt([B], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')).
finprove([atm(not,atm(not,A)), '&', B], '-'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B], '-'), prfwrt(atm(not,atm(not,A)), '-'), write("   OR   "), prfwrt(B, '-'), nl, prfwrt(A, '-'), write("   OR   "), wrt([B], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')).
finprove([A, '&', atm(not,atm(not,B))], '-'):- A\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B))], '-'), prfwrt(A, '-'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '-'), nl, prfwrt(A, '-'), write("   OR   "), wrt([B], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')).
finprove([A, '&', B], '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, '&', B], '-'), prfwrt(A, '-'), write("   OR   "), wrt([B], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')).

%%proof(A&B&C-)
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'), assert(tofinprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-')).
proof(atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C, '-'):- C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C], '-'), assert(toprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C], '-')).
proof(atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C)), '-'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))], '-'), assert(toprove([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))], '-')).
proof(A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'), assert(toprove([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-')).
proof(atm(not,atm(not,A)), '&', B, '&', C, '-'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B, '&', C], '-'), assert(toprove([atm(not,atm(not,A)), '&', B, '&', C], '-')).
proof(A, '&', atm(not,atm(not,B)), '&', C, '-'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B)), '&', C], '-'), assert(toprove([A, '&', atm(not,atm(not,B)), '&', C], '-')).
proof(A, '&', B, '&', atm(not,atm(not,C)), '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, '&', B, '&', atm(not,atm(not,C))], '-'), assert(toprove([A, '&', B, '&', atm(not,atm(not,C))], '-')).
proof(A, '&', B, '&', C, '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,atm(not,_))), C\=atm(not,atm(not,atm(not,_))), wrt([A, '&', B, '&', C], '-'), assert(toprove([A, '&', B, '&', C], '-')).
finprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'), prfwrt(atm(not,atm(not,A)), '-'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '-'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '-'), nl, prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
finprove([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C], '-'):- C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', atm(not,atm(not,B)), '&', C], '-'), prfwrt(atm(not,atm(not,A)), '-'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '-'), write("   OR   "), prfwrt(C, '-'), nl, prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
finprove([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))], '-'):- B\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B, '&', atm(not,atm(not,C))], '-'), prfwrt(atm(not,atm(not,A)), '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '-'), nl, prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
finprove([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'):- A\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B)), '&', atm(not,atm(not,C))], '-'), prfwrt(A, '-'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '-'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '-'), nl, prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
finprove([atm(not,atm(not,A)), '&', B, '&', C], '-'):- B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([atm(not,atm(not,A)), '&', B, '&', C], '-'), prfwrt(atm(not,atm(not,A)), '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), prfwrt(C, '-'), nl, prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
finprove([A, '&', atm(not,atm(not,B)), '&', C], '-'):- A\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, '&', atm(not,atm(not,B)), '&', C], '-'), prfwrt(A, '-'), write("   OR   "), prfwrt(atm(not,atm(not,B)), '-'), write("   OR   "), prfwrt(C, '-'), nl, prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
finprove([A, '&', B, '&', atm(not,atm(not,C))], '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), wrt([A, '&', B, '&', atm(not,atm(not,C))], '-'), prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), prfwrt(atm(not,atm(not,C)), '-'), nl, prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
finprove([A, '&', B, '&', C], '-'):- A\=atm(not,atm(not,_)), B\=atm(not,atm(not,_)), C\=atm(not,atm(not,_)), wrt([A, '&', B, '&', C], '-'), prfwrt(A, '-'), write("   OR   "), prfwrt(B, '-'), write("   OR   "), wrt([C], '-'), assert(prf(1,A,'-')), assert(prf(2,B,'-')), assert(prf(3,C,'-')).
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

prove([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'|T], '+'):- wrt([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'], '+'), wrt([atm(not,atm(not,H))],'+'), wrt([H],'+'), assert(prf(H, '+')), wrt(['{', H2, '&', H3, '}'], '+'), wrt([H2], '+'), assert(prf(H2, '+')), wrt([H3], '+'), assert(prf(H3, '+')), prove(T, '+').
prove([H, '&', '{', H2, '&', H3, '}'|T], '+'):- H\=atm(not,atm(not,_)), wrt([H, '&', '{', H2, '&', H3, '}'], '+'), wrt([H],'+'), assert(prf(H, '+')), wrt(['{', H2, '&', H3, '}'], '+'), wrt([H2], '+'), assert(prf(H2, '+')), wrt([H3], '+'), assert(prf(H3, '+')), prove(T, '+').

prove([atm(not,atm(not,H)), '&', '{', H2, 'V', H3, '}'|T], '+'):- wrt([atm(not,atm(not,H)), '&', '{', H2, 'V', H3, '}'], '+'), wrt([atm(not,atm(not,H))], '+'), wrt([H],'+'), assert(prf(H, '+')), wrt(['{',H2,'V',H3,'}'], '+'), assert(toprove([H2, 'V', H3], '+')), prove(T, '+').
prove([H, '&', '{', H2, 'V', H3, '}'|T], '+'):- H\=atm(not,atm(not,_)), wrt([H, '&', '{', H2, 'V', H3, '}'], '+'), wrt([H], '+'), assert(prf(H, '+')), wrt(['{',H2,'V',H3,'}'], '+'), assert(toprove([H2, 'V', H3], '+')), prove(T, '+').

prove([atm(not,atm(not,H)), 'V', '{', H2, '&', H3, '}'|T], '-'):- wrt([atm(not,atm(not,H)), 'V', '{', H2, '&', H3, '}'], '-'), wrt([atm(not,atm(not,H))], '-'), wrt([H],'-'), assert(prf(H, '-')), wrt(['{',H2,'&',H3,'}'], '-'), assert(toprove([H2, '&', H3], '-')), prove(T, '-').
prove([H, 'V', '{', H2, '&', H3, '}'|T], '-'):- H\=atm(not,atm(not,_)), wrt([H, 'V', '{', H2, '&', H3, '}'], '-'), wrt([H], '-'), assert(prf(H, '-')), wrt(['{',H2,'&',H3,'}'], '-'), assert(toprove([H2, '&', H3], '-')), prove(T, '-').

prove([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'|T], '-'):- wrt([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'], '-'), wrt([atm(not,atm(not,H))], '-'), wrt([H],'-'), assert(prf(H, '-')), wrt(['{', H2, 'V', H3, '}'], '-'), wrt([H2], '-'), assert(prf(H2, '-')), wrt([H3], '-'), assert(prf(H3, '-')), prove(T, '-').
prove([H, 'V', '{', H2, 'V', H3, '}'|T], '-'):- H\=atm(not,atm(not,_)), wrt([H, 'V', '{', H2, 'V', H3, '}'], '-'), wrt([H], '-'), assert(prf(H, '-')), wrt(['{', H2, 'V', H3, '}'], '-'), wrt([H2], '-'), assert(prf(H2, '-')), wrt([H3], '-'), assert(prf(H3, '-')), prove(T, '-').


%%%%%%%%%%%%%%%%%verschilmetDFS%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
prove([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'|T], '+'):- wrt([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'], '+'), assert(toprove([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'], '+')), prove(T, '+').
finprove([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'], '+'):- wrt([atm(not,atm(not,H)), 'V', '{', H2, 'V', H3, '}'], '+'), finprove([atm(not,atm(not,H)), 'V', H2, 'V', H3], '+').
prove([H, 'V', '{', H2, 'V', H3, '}'|T], '+'):- H\=atm(not,atm(not,_)), wrt([H, 'V', '{', H2, 'V', H3, '}'], '+'), assert(toprove([H, 'V', '{', H2, 'V', H3, '}'], '+')), prove(T, '+').
finprove([H, 'V', '{', H2, 'V', H3, '}'], '+'):- H\=atm(not,atm(not,_)), wrt([H, 'V', '{', H2, 'V', H3, '}'], '+'), finprove([H, 'V', H2, 'V', H3], '+').

prove([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'|T], '-'):- wrt([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'], '-'), assert(toprove([atm(not,atm(not,H)), '&', '{',H2, '&', H3,'}'], '-')), prove(T, '-').
finprove([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'], '-'):- wrt([atm(not,atm(not,H)), '&', '{', H2, '&', H3, '}'], '-'), finprove([atm(not,atm(not,H)), '&', H2, '&', H3], '-').
prove([H, '&', '{', H2, '&', H3, '}'|T], '-'):- H\=atm(not,atm(not,_)), wrt([H, '&', '{', H2, '&', H3, '}'], '-'), assert(toprove([H, '&', '{',H2, '&', H3,'}'], '-')), prove(T, '-').
finprove([H, '&', '{', H2, '&', H3, '}'], '-'):- H\=atm(not,atm(not,_)), wrt([H, '&', '{', H2, '&', H3, '}'], '-'), finprove([H, '&', H2, '&', H3], '-').
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
prove([H,'V',H3|T], '+'):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], write("/\\"), wrt([H,'V',H3|T], '+'), assert(toprove([H, 'V', H3], '+')), prove(T, '+').
%%prove(A&B-)
prove([H,'&',H3|T], '-'):- H3\='{', H3\=not, T\=['&'|_], T\=['V'|_], write("/\\"), wrt([H,'&',H3|T], '-'), assert(toprove([H, '&', H3], '-')), prove(T, '-').
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
prove([H,'V',H2,'V',H3|T], '+'):- H3\='{', H3\=not, write("/\\"), wrt([H,'V',H2,'V',H3], '+'), assert(toprove([H, 'V', H2, 'V', H3], '+')), prove(T, '+').
%%prove(A&B&C-)
prove([H,'&',H2,'&',H3|T], '-'):- H3\='{', H3\=not, write("/\\"), wrt([H,'&',H2,'&',H3], '-'), assert(toprove([H, '&', H2, '&', H3], '-')), prove(T, '-').
%%prove(AVBVC-)
prove([H,'V',H2,'V',H3|T], '-'):- H3\='{', H3\=not, wrt([H,'V',H2,'V',H3], '-'), proof(H, 'V', H2, 'V', H3, '-'), prove(T, '-').

prove(['{', H, '&', H2, '}', '&', H3|T], S):- wrt(['{', H, '&', H2, '}', '&', H3], S), prove([H3, '&', '{', H, '&', H2, '}'|T], S).
prove(['{', H, 'V', H2, '}', 'V', H3|T], S):- wrt(['{', H, 'V', H2, '}', 'V', H3], S), prove([H3, 'V', '{', H, 'V', H2, '}'|T], S).
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

prove([not,not, '{', H, '&', H2, '}'|T], '+'):- wrt([not,not, '{', H, '&', H2, '}'], '+'), wrt(['{',H,'&',H2,'}'],'+'), proof(H, '&', H2, '+'), prove(T, '+').
prove([not, '{', H, '&', H2, '}'|T], '+'):- wrt([not, '{', H, '&', H2, '}'], '+'), wrt([not,H,'V',not,H2], '+'), write("  /\\"), proof(atm(not, H), 'V', atm(not, H2), '+'), prove(T, '+').

prove([not,not, '{', H, 'V', H2, '}'|T], '+'):- wrt([not,not, '{', H, 'V', H2, '}'], '+'), wrt(['{',H,'V',H2,'}'], '+'), write("  /\\"), proof(H, 'V', H2, '+'), prove(T, '+').
prove([not, '{', H, 'V', H2, '}'|T], '+'):- wrt([not, '{', H, 'V', H2, '}'], '+'), wrt([atm(not,H),'&',atm(not,H2)], '+'), proof(atm(not, H), '&', atm(not, H2), '+'), prove(T, '+').

prove([not,not, '{', H, '&', H2, '}'|T], '-'):- wrt([not,not, '{', H, '&', H2, '}'], '-'), wrt(['{',H,'&',H2,'}'], '-'), write("  /\\"), proof(H, '&', H2, '-'), prove(T, '-').
prove([not, '{', H, '&', H2, '}'|T], '-'):- wrt([not, '{', H, '&', H2, '}'], '-'), wrt([atm(not,H),'V',atm(not,H2)], '-'), proof(atm(not, H), 'V', atm(not, H2), '-'), prove(T, '-').

prove([not,not, '{', H, 'V', H2, '}'|T], '-'):- wrt([not,not, '{', H, 'V', H2, '}'], '-'), wrt(['{',H,'V',H2,'}'], '-'), proof(H, 'V', H2, '-'), prove(T, '-').
prove([not, '{', H, 'V', H2, '}'|T], '-'):- wrt([not, '{', H, 'V', H2, '}'], '-'), wrt([atm(not,H),'&',atm(not,H2)], '-'), write("  /\\"), proof(atm(not, H), '&', atm(not, H2), '-'), prove(T, '-').
