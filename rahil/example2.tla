---------------------------- MODULE example2 --------------------------
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
    /\ val2 = 1
    /\ val3 = 0

m1 ==
    /\ val1' = ~val1
    /\ val2' = 1
    /\ val2 = 1
    /\ UNCHANGED <<val3>>

m2 ==
    /\ val3 = 0
    /\ val3' = 55
    /\ UNCHANGED <<val1, val2>>

m3 ==
    /\ val3 < 100
    /\ val3' = val3 + 1
    /\ UNCHANGED <<val1, val2>>

Next ==
    \/ m1
    \/ m2
    \* \/ m3
=================================================================

(set-logic HORN)

(declare-fun pred (Bool Int Int ) Bool)

;Init
(assert
	(forall ((val1 Bool) (val2 Int) (val3 Int) )
		(=>
			(and (= val1 false) (= val2 1) (= val3 0))
			(pred val1 val2 val3 )
		)
	)
)

;m1
(assert
	(forall ((val1 Bool) (val2 Int) (val3 Int) (val1.prime Bool) (val2.prime Int) (val3.prime Int) )
		(=>
			(and (pred val1 val2 val3 )
			(and (= val1.prime (not val1)) (= val2.prime 1) (= val2 1) (= val3.prime val3))
			(pred val1.prime val2.prime val3.prime )
		)
	)
)

;m2
(assert
	(forall ((val1 Bool) (val2 Int) (val3 Int) (val1.prime Bool) (val2.prime Int) (val3.prime Int) )
		(=>
			(and (pred val1 val2 val3 )
			(and (= val3 0) (= val3.prime 55) (and (= val1.prime val1) (= val2.prime val2))))
			(pred val1.prime val2.prime val3.prime )
		)
	)
)

(check-sat)
(exit)

(assert (forall ((val1 Bool) (val2 Int)) (=> (and (= val1 false) (= val2 1)) (pred val1 val2) ) ) )

(assert (forall ((val1 Bool) (val2 Int) (val1_prime Bool) (val2_prime Int)) (=> (and (pred val1 val2) (= val2 1) (= val1_prime (not val1)) (= val2_prime 1)) (pred val1_prime val2_prime) ) ) )
