---------------------------- MODULE example1 --------------------------
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

Inv ==
    /\ val2 = 1
    /\ val1 = FALSE
=================================================================

(set-logic HORN)

(declare-fun pred (Bool Int ) Bool)

;Init
(assert
	(forall ((val1 Bool) (val2 Int) )
		(=>
			(and (= val1 false) (= val2 1))
			(pred val1 val2 )
		)
	)
)

;Next
(assert
	(forall ((val1 Bool) (val2 Int) (val1.prime Bool) (val2.prime Int) )
		(=>
			(and (pred val1 val2 )
			(and (= val1.prime (not val1)) (= val2.prime 1) (= val2 1)))
			(pred val1.prime val2.prime )
		)
	)
)

(check-sat)
(exit)

;Initial state
(assert (forall ((val1 Bool) (val2 Int) ) (=> (and (= val1 false) (= val2 1)) (pred val1 val2 ) ) ) )

;Next
(assert (forall ((val1 Bool) (val2 Int) (val1.prime Bool) (val2.prime Int) ) (=> (and (pred val1 val2 ) (and (= val1.prime (not val1)) (= val2.prime 1) (= val2 1))) (pred val1.prime val2.prime ) ) ) )
