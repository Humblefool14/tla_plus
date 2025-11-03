------------------------------- MODULE euclid -------------------------------
\* Modification History
\* Last modified Mon Nov 03 22:08:57 IST 2025 by srikar
\* Created Mon Nov 03 21:51:28 IST 2025 by srikar
EXTENDS Naturals

CONSTANTS M, N

VARIABLES x, y

Init == (x = M) /\ (y = N)

Next == \/ ( x > y
            /\ x' = x - y
            /\ y' = y )
        \/ ( y > x
            /\ y' = y - x
            /\ x' = x )
            
Spec == Init /\ [][Next]_<<x, y>>

TypeOK == /\ x \in Nat
          /\ y \in Nat
          /\ x > 0
          /\ y > 0
            
===================================================================