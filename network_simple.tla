------------------------------------------------ MODULE network_simple ------------------------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT N
ASSUME N \in Nat \ {0,1}
Procs == 1..N

(*
--algorithm network_simple 
{
	variable network = [p \in Procs |-> <<>>];

	define
	{
		send(to, msg) == [network EXCEPT ![to] = Append(@, msg)]
		bcast(msg) == [to \in Procs |-> Append(network[to], msg)]
	}

	fair process (p \in Procs)
	variable msg = "hello";
	{
		RECV:either
		{
			msg := <<>>;
			if (Len(network[self]) > 0)
			{
				pop: msg := Head(network[self]);
				network[self] := Tail(@)
			};
			pr:print <<"received", msg>>;
		}

		or
		SEND:{
			with (k \in Procs \ {self})
			{
				network := send(k, msg);
				print <<"send", msg, "to", k>>;
			};
		}
	}
}
*)


\* BEGIN TRANSLATION
VARIABLES network, pc

(* define statement *)
send(to, msg) == [network EXCEPT ![to] = Append(@, msg)]
bcast(msg) == [to \in Procs |-> Append(network[to], msg)]

VARIABLE msg

vars == << network, pc, msg >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ network = [p \in Procs |-> <<>>]
        (* Process p *)
        /\ msg = [self \in Procs |-> "hello"]
        /\ pc = [self \in ProcSet |-> "RECV"]

RECV(self) == /\ pc[self] = "RECV"
              /\ \/ /\ msg' = [msg EXCEPT ![self] = <<>>]
                    /\ IF Len(network[self]) > 0
                          THEN /\ pc' = [pc EXCEPT ![self] = "pop"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "pr"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "SEND"]
                    /\ msg' = msg
              /\ UNCHANGED network

pop(self) == /\ pc[self] = "pop"
             /\ msg' = [msg EXCEPT ![self] = Head(network[self])]
             /\ network' = [network EXCEPT ![self] = Tail(@)]
             /\ pc' = [pc EXCEPT ![self] = "pr"]

pr(self) == /\ pc[self] = "pr"
            /\ PrintT(<<"received", msg[self]>>)
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << network, msg >>

SEND(self) == /\ pc[self] = "SEND"
              /\ \E k \in Procs \ {self}:
                   /\ network' = send(k, msg[self])
                   /\ PrintT(<<"send", msg[self], "to", k>>)
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ msg' = msg

p(self) == RECV(self) \/ pop(self) \/ pr(self) \/ SEND(self)

Next == (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

========================================================================================================================
\* Modification History
\* Last modified Wed Oct 28 16:15:29 EDT 2015 by eddieaili
\* Created Wed Oct 28 15:20:56 EDT 2015 by eddieaili
