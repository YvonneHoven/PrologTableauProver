# PrologTableauProver
for Many-Valued Logics

assumptions: 
- never assert a premise which can branch out the tableau
- never have more than 1 branch splitting moments (in bfs)

System Usability Scores
https://www.survio.com/survey/d/M8R2S8P5K9X3Q9W3I

possibilities with this prover to assert premises
notnotnotH
notnotH
notH
H
{notnotnotA & notnotnotB} till
{A & B}
notnotnotA & notnotnotB till
A & B
notnot{notnotA & notnotB} till
notnot{A & B}
not{notnotA V notnotB} till
not{A V B}
notA&{notB & notC} till
notA&{B & C}
A&{notB & notC} till
A&{B & C}

possibilities with this prover to prove inferences
notnotnotH
notnotH
notH
H
notnotA & notnotB+ till
A&B+
notnotA & notnotB & notnotC+till
A&B&C+
notnotA V notnotB- till
AVB-
notnotA V notnotB V notnotC- till
AVBVC-
{notnotnotA & notnotnotB} +/- till
{A&B} +/-
{notnotnotA V notnotnotB} +/- till
{AVB} +/-
notnotA & {notB & notC} +/- till
A & {B & C} +/-
notnotA V {notB V notC} +/- till
A V {B V C} +/-
notnotA & {notB V notC} + till
A & {B V C} +
notnotA V {notB & notC} - till
A V {B & C} -
notnotnotA & notnotnotB +/- till
A & B +/-
notnotnotA V notnotnotB +/- till
A V B +/-
notnotA & notnotB & notnotC +/- till
A & B & C +/-
notnotA V notnotB V notnotC +/-  till
A V B V C
{A&B}&C +/-
{AVB}VC +/-
{A&B}VC +/-
{AVB}&C +/-
notnot {notnotA & notnotB} +/- till
not{A&B} +/-
notnot {notnotA V notnotB} +/-
not{AVB} +/-


