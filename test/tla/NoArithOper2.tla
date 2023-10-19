---------------------------- MODULE NoArithOper2 --------------------------
VARIABLE
    \* @type: Bool;
    val1,
    \* @type: Bool;
    val2

Init ==
    /\ val1 = FALSE
    /\ val2 = TRUE

m1 ==
    /\ val1 = FALSE
    /\ val2' = ~val2
    /\ UNCHANGED <<val1>>

Next == m1

inv1 == val1 = FALSE
=================================================================
