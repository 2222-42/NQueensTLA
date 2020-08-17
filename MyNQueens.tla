----------------------------- MODULE MyNQueens -----------------------------
EXTENDS Naturals, Sequences

CONSTANT N

ASSUME N \in Nat \ {0}


\* queens == [1..N -> 1..N]

\* Make the relation between queens whether is able to attack each other or not
Attackable(queens, i, j) ==
    \/ queens[i] = queens[j]
    \/ i - j = queens[i] - queens[j]
    \/ i - j = queens[j] - queens[i]

(*
sampleQ1 == <<2,4,1,3>>
In Evaluate Constant Expression:
    \A i, j \in 1..4: i = j \/ \neg Attackable(sampleQ1, i, j) 
To search in more shorter steps by the following:
    \A i \in 1..Len(sampleQ1)-1: 
        \A j \in (i + 1)..Len(sampleQ1):
            \neg Attackable(sampleQ1, i, j) 
> TRUE
    IsSolution(sampleQ1) 
> TRUE
*)

(*
sampleQ2 == <<2,4,3,1>>
In Evaluate Constant Expression:
    \A i, j \in 1..4: i = j \/ \neg Attackable(sampleQ2, i, j) 
> FALSE
    IsSolution(sampleQ2) 
> FALSE
*)

\* IsSolution is defined by there are no attackable
IsSafe(queens) ==
    \A i \in 1..Len(queens)-1: 
        \A j \in (i + 1)..Len(queens): 
            \neg Attackable(queens, i, j) 
(* There might be not enough condition to assert it is solved.
Think the following case: when there are no queens in the board N*N.
e.g. 
IsSolution(<<2,4,1>>) 
> TRUE
So I guess the naming is not good. And change it IsSolution into IsSafe
*)
IsSolution(queens) ==
    /\ Len(queens) = N
    /\ IsSafe(queens)
(*
IsSolution(<<2,4,1>>) 
> FALSE
IsSolution(<<2,4,3,1>>)
> FALSE
IsSolution(<<2,4,1,3>>)
> TRUE
*)

(* --algorithm MyNQueens
    variables solutions = {}, targets = {<<>>}, candidates = {}
begin
    while (targets # {}) do
        with queens \in targets do
            candidates := {c \in 1..N : IsSafe(Append(queens, c))};

            \* if (\A i \in 1..Len(queens)-1: \neg Attackable(queens, i, Len(queens) + 1)) then
            \*     body
            \* end if;
            
            if (Len(queens) + 1 = N) then
                targets := targets \ {queens};
                solutions := solutions \union {Append(queens, c): c \in candidates}
            else
                targets := (targets \ {queens}) \union {Append(queens, c): c \in candidates}
            end if;
        end with;

    end while;
end algorithm*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4252b56e2b6417777d6799239b0b4138
VARIABLES solutions, targets, candidates, pc

vars == << solutions, targets, candidates, pc >>

Init == (* Global variables *)
        /\ solutions = {}
        /\ targets = {<<>>}
        /\ candidates = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF (targets # {})
               THEN /\ \E queens \in targets:
                         /\ candidates' = {c \in 1..N : IsSafe(Append(queens, c))}
                         /\ IF (Len(queens) + 1 = N)
                               THEN /\ targets' = targets \ {queens}
                                    /\ solutions' = (solutions \union {Append(queens, c): c \in candidates'})
                               ELSE /\ targets' = ((targets \ {queens}) \union {Append(queens, c): c \in candidates'})
                                    /\ UNCHANGED solutions
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << solutions, targets, candidates >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-73f3370284ae9add551490dc262449d2

Invariant == 
    /\ solutions \subseteq { queens \in [1..N -> 1..N] : IsSolution(queens) }


=============================================================================
\* Modification History
\* Last modified Sun Aug 16 10:18:23 JST 2020 by daioh
\* Created Sun Aug 16 10:03:36 JST 2020 by daioh
