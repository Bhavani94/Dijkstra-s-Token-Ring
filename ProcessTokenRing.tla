-------------------- MODULE ProcessTokenRing -------------------
EXTENDS Integers
CONSTANT N, M
ASSUME N \in Nat \ {0}
Procs == 1..N


(* Dijkstra's stabilizing token ring with processes
--algorithm TokenRing {
  variable token = [k \in 0..N |-> (k%M)];

   fair process (j \in Procs)
    { J0: while (TRUE)
            { await token[self] /= token[(self-1)];
              token[self] := token [(self-1)];
            }
    }
   fair process (i \in {0})
    { I0: while (TRUE)
           { await (token[self] = token[N]);
             token[self] := (token[N]+1) % M
           }
    }
}
 ****************************************************************)
(* In the above you can add label J1 for command part of J0, and I1 for command part of I0
And the result doesn't change. Stabilization is not violated. 
*)
\* BEGIN TRANSLATION
VARIABLE token

vars == << token >>

ProcSet == (Procs) \cup ({0})

Init == (* Global variables *)
        /\ token = [k \in 0..N |-> (k%M)]

j(self) == /\ token[self] /= token[(self-1)]
           /\ token' = [token EXCEPT ![self] = token [(self-1)]]

i(self) == /\ (token[self] = token[N])
           /\ token' = [token EXCEPT ![self] = (token[N]+1) % M]

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: i(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(i(self))

\* END TRANSLATION
Stabilization == <> \A x \in 0..N: token[x]=0
TypeOK == \A x \in 0..N: token[x] < M

==================================================================

Dijkstra's stabilizing token ring algorithm
using Processes!

Consider a ring of processes 0..n
Each process has a variable x
Variable of j is x.j
Suppose x.j is an integer for now

At process j, j > 0
x.j ≠ x.(j-1) --> x.j = x.(j-1)

At process 0
x.0 = x.N --> x.0 = x.N+1

Let initial state be such that all x values are 0

Invariants?
Faults?
Stabilization?

What if we restrict domain of x?
Let x be from 0..M-1
Change action at 0 as 
x.0 = x.N --> x.0 = (x.N+1) mod M

What if M =2 (Assume N is arbitrary)
What if M = N?
