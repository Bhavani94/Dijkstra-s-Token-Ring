------------------------------ MODULE token4 ------------------------------
EXTENDS Integers
CONSTANT L
ASSUME L \in Nat \ {0,1}
Procs == 1..(L-1)
(* Dijkstra's stabilizing 4 state token ring with processes
--algorithm Token4stateRing {
    variable up = [k \in 0..L |-> 0], c = [k \in 0..L |-> 0];
    fair process (j \in Procs)
    {
            J1: while (TRUE)
                {
                    either with (j \in Procs)
                    {
                        await(c[(j-1)] /= c[j]);
                        c[j] := c[(j-1)];
                        up[j] := 1;
                    }
                    or with (j \in Procs)
                    {
                        await(c[(j+1)] = c[j] /\ up[j] = 1 /\ up[(j+1)] = 0);
                        up[self] := 0; 
                    }
                                    
                }
    }

    fair process (i \in {0})
    {
         I0: up[0] := 1; \* process 0's "up" is always 1
         I1: while (TRUE)
         { 
                 await (c[1] = c[0] /\ up[1] = 0);
                 {
                    if(c[0] = 1)
                    {c[0] := 0}
                    else c[0] := 1} 
                    }    
            }
    }
    fair process (z \in {L})
    {
            Z0: up[self] := 0; \* process L's "up" is always 0
            Z1: up[L]:= 1;     \* process L's "up" is always 1
            Z2: while (TRUE)
            {
               await(c[(L-1)] /= c[L]);
                    c[L] := c[(L-1)];                
            }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES up, c, pc

vars == << up, c, pc >>

ProcSet == (Procs) \cup ({0})

Init == (* Global variables *)
        /\ up = [k \in 0..L |-> 0]
        /\ c = [k \in 0..L |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "J1"
                                        [] self \in {0} -> "I0"]

J1(self) == /\ pc[self] = "J1"
            /\ \/ /\ \E j \in Procs:
                       /\ (c[(j-1)] /= c[j])
                       /\ c' = [c EXCEPT ![j] = c[(j-1)]]
                       /\ up' = [up EXCEPT ![j] = 1]
               \/ /\ \E j \in Procs:
                       /\ (c[(j+1)] = c[j] /\ up[j] = 1 /\ up[(j+1)] = 0)
                       /\ up' = [up EXCEPT ![self] = 0]
                  /\ c' = c
            /\ pc' = [pc EXCEPT ![self] = "J1"]

j(self) == J1(self)

I0(self) == /\ pc[self] = "I0"
            /\ up' = [up EXCEPT ![0] = 1]
            /\ pc' = [pc EXCEPT ![self] = "I1"]
            /\ c' = c

I1(self) == /\ pc[self] = "I1"
            /\ (c[1] = c[0] /\ up[1] = 0)
            /\ IF c[0] = 1
                  THEN /\ c' = [c EXCEPT ![0] = 0]
                  ELSE /\ c' = [c EXCEPT ![0] = 1]
            /\ pc' = [pc EXCEPT ![self] = "I1"]
            /\ up' = up

i(self) == I0(self) \/ I1(self)

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: i(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(i(self))

\* END TRANSLATION
InvProp1 == (up[0] = 1) /\ (up[L] = 0)
 \*InvProp2 == []<> c[0] = c[L] \*( Always eventually, node 0 will have the token once the system stabilizes after faults) 
=============================================================================
\*Bhavani Sundara Raman (50169253; bhavanis@buffalo.edu) Sagar Dhamija (sagardha@buffalo.edu)
\* Modification History
\* Last modified fri Dec 4 19:05:21 EST 2015 by Bhavani
\* Created fri Dec 4 15:37:31 EST 2015 by Bhavani
