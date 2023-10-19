---------------------------- MODULE ArithOper2 --------------------------
EXTENDS Integers

VARIABLE
    \* @type: Bool;
    val1,
    \* @type: Int;
    val2,
    \* @type: Int;
    val3

Init ==
    /\ val1 = FALSE
    /\ val2 = 2
    /\ val3 = 0

m1 ==
    /\ val1 = FALSE
    /\ val2' = val2 + 1
    /\ UNCHANGED <<val1, val3>>

Next == m1

inv1 == val2 < 100
=================================================================

m4 == val3 >= 0 // check neg(m4) flase