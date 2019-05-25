# PrologTableauProver
for Many-Valued Logics


System Usability Scores

BFS
https://web.usabilityscale.com/form?ex=-LeC_McOi3pYoKgq4Y3x&pr=-LeCZFV5fV0Ckr9n-88B

DFS
https://web.usabilityscale.com/form?ex=-LeC_PUfa3pPKHmqqW_f&pr=-LeCZFV5fV0Ckr9n-88B



BUGS:
x   verschil aan nl aant einde bij de &regelonderelkaar
    indenten van de andere oplossingen en evt / \
x   prove([not,{notnotH V notnot H2}] variaties toevoegen
x   prove([not,{notH V notnot H2}]
x   prove([not,{notnotH V not H2}]
x   en de assert not{aVB}   assert not{a&B} varianten
x   bij alle prove H H3 ook nog dat H3\='{'
??  bij alle prove H H3 ook nog dat T\=[&] T\=[V]
    en fail24-5.png
    refactoring
    prf(H) alsnotnot dan weghalen
    testen &&
    kijken nl


   als-prf-(notnot-iets-notnot)-dan-nog-niet-2e-lijn-indent-van-de-notnot-weggehaald------en-A\=atm(not...)
   prf-functie-nakijken-op-atm(not,atm(not-----en-nl
   na-topove_assert-ook-retract-en-opnieuw
   bij-alle-begin_assert(toprove())-nog-wrt()-vooraan
   kijken-of-alle-toprove()-wel-een-daadwerkelijke-oplossing-maken-of-weer-terug-naar-assert(toprove)
   wrt(not)VSwrt(atm(not,)
   assprove(notnot...?
   wrt(atmnot??VSwrt(notnot
   hoe met 1 atom als inference, dan printie 2x
   bagoff sorteren, zelfden naast elkaar, zoek alle prf(), maak iets((not)A, +)
   Vnotnotnota,-   -> nota,-???


donderdag:
x  check alle asserts
x  voeg assertnotnotnotA... toe
x  denk om A\=not
x  kijk voor bugs
   kijk voor redundancys
x  kijk voor lastigste V& &V combis
------------
vrijdag:
x  V& &V
x  bugs
-------
zaterdag+zondag:
   []list counterex

