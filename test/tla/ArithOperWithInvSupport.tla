---------------------------- MODULE ArithOperWithInvSupport --------------------------
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
    /\ val2' = val2 + 1
    /\ UNCHANGED <<val1, val3>>

Next == m1

inv1 == val2 < 100
=================================================================
