----------------------------- MODULE MyNQueens -----------------------------
EXTENDS Naturals, Sequences

N == 4


queens == [1..N -> 1..N]

\* Make the relation between queens whether is able to attack each other or not
Attackable(queens, i, j) ==
    \/ queens[i] = queens[j]
    \/ i - j = queens[i] - queens[j]
    \/ i - j = queens[j] - queens[i]

sampleQ1 == <<2,4,1,3>>
(*
In Evaluate Constant Expression:
\A i, j \in 1..4: i = j \/ \neg Attackable(sampleQ1, i, j) 
> TRUE
*)

sampleQ2 == <<2,4,3,1>>
(*
In Evaluate Constant Expression:
\A i, j \in 1..4: i = j \/ \neg Attackable(sampleQ2, i, j) 
> FALSE
*)

=============================================================================
\* Modification History
\* Last modified Sun Aug 16 10:18:23 JST 2020 by daioh
\* Created Sun Aug 16 10:03:36 JST 2020 by daioh
