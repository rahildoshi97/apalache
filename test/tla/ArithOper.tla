---------------------------- MODULE ArithOper --------------------------
EXTENDS Integers

VARIABLE
    \* @type: Int;
    val2,
    \* @type: Int;
    val3

Init ==
    /\ val2 = 2
    /\ val3 = 0

m1 ==
    /\ val2' = val2 + (1 * 1)
    /\ val2 = (4 - 2)
    /\ UNCHANGED <<val3>>

m2 ==
    /\ val3 > 0
    /\ val3' = (100 \div (-3))
    /\ UNCHANGED <<val2>>

m3 ==
    /\ val3 <= (99 + 1)
    /\ val3' = val3 + (3 - 2)
    /\ UNCHANGED <<val2>>

Next ==
    \/ m1
    \/
        /\ m1
        /\ m3
    \/ m2
    \/ m3

inv1 ==
    /\ val3 > 20
    /\ val2 < 100
=================================================================
