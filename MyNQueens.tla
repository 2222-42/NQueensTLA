----------------------------- MODULE MyNQueens -----------------------------
EXTENDS Naturals, Sequences

N == 4


\* queens == [1..N -> 1..N]

\* Make the relation between queens whether is able to attack each other or not
Attackable(queens, i, j) ==
    \/ queens[i] = queens[j]
    \/ i - j = queens[i] - queens[j]
    \/ i - j = queens[j] - queens[i]

sampleQ1 == <<2,4,1,3>>
(*
In Evaluate Constant Expression:
    \A i, j \in 1..4: i = j \/ \neg Attackable(sampleQ1, i, j) 
To search in more shorter steps by the following:
    \A i \in 1..Len(sampleQ1)-1: 
        \A j \in (i + 1)..Len(sampleQ1):
            \neg Attackable(sampleQ1, i, j) 
> TRUE
*)

sampleQ2 == <<2,4,3,1>>
(*
In Evaluate Constant Expression:
\A i, j \in 1..4: i = j \/ \neg Attackable(sampleQ2, i, j) 
> FALSE
*)

\* IsSolution is defined by there are no attackable
IsSolution(queens) ==
    \A i \in 1..Len(queens)-1: 
        \A j \in (i + 1)..Len(queens): 
            \neg Attackable(queens, i, j) 

=============================================================================
\* Modification History
\* Last modified Sun Aug 16 10:18:23 JST 2020 by daioh
\* Created Sun Aug 16 10:03:36 JST 2020 by daioh
