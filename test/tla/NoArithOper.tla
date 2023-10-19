---------------------------- MODULE NoArithOper --------------------------
VARIABLE
    \* @type: Bool;
    val1,
    \* @type: Int;
    val2

Init ==
    /\ val1 = FALSE
    /\ val2 = 1

Next ==
    /\ val1' = ~val1
    /\ val2' = 1
    /\ val2 = 1
=================================================================
