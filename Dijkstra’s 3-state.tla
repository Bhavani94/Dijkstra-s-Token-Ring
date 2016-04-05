------------------------------- MODULE token -------------------------------
EXTENDS Integers
CONSTANTS N
(* Dijkstra's stabilizing token ring algorithm
--fair algorithm StabTokenRing {
variable token = [j \in 0..N |-> 0];
    { while (TRUE)
        { 
            either with (j \in 1..N)
            { 
                await (token[j] /= token[(j-1)]);
                token[j] := token[(j-1)];
            }
            or
            {
                await (token[0] = token[N]);
                token[0] := (token[0]+1)%3;
             }
        }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLE token

vars == << token >>

Init == (* Global variables *)
        /\ token = [j \in 0..N |-> 0]

Next == \/ /\ \E j \in 1..N:
                /\ (token[j] /= token[(j-1)])
                /\ token' = [token EXCEPT ![j] = token[(j-1)]]
        \/ /\ (token[0] = token[N])
           /\ token' = [token EXCEPT ![0] = (token[0]+1)%3]

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION
InvProp1 == (\E k \in 1..N: token[k] >= token[k-1] \/ token[0] = token[N]) \* There should be at least one token 
=============================================================================
Bhavani Sunara Raman (50169253; bhavanis@buffalo.edu)
