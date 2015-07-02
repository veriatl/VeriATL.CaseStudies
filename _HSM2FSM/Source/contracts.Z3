;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Preconditions                                                                                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;pre1: different state machines have different names
(assert (! (forall ((s1 Int) (s2 Int))
		   (=> (and (not (= s1 s2)) (StateMachine s1) (StateMachine s2))
		       (not (= (nameMach s1) (nameMach s2))))) :named pre1))

;pre2: within a state machine, states have unique names
(assert (! (forall ((sm Int) (s1 Int) (s2 Int))
		   (=> (and (StateMachine sm) (AbstractState s1) (AbstractState s2) (st-stateMachine s1 sm) (st-stateMachine s2 sm) (= (name s1) (name s2)))
		       (= s1 s2))) :named pre2))

;pre3a: a state does belong to at least one state machine
(assert (! (forall ((st Int)) (=> (AbstractState st)
				  (exists ((sm Int)) (and (StateMachine sm) (st-stateMachine st sm))))) :named pre3a))

;pre3b: a state does belong to at most one state machine
(assert (! (forall ((st Int)) (=> (AbstractState st)
				  (forall ((sm1 Int) (sm2 Int)) 
					  (=> (and (StateMachine sm1) (st-stateMachine st sm1)  (StateMachine sm2) (st-stateMachine st sm2))
					      (= sm1 sm2))))) :named pre3b))

;pre4: at most one compositeState
(assert (! (forall ((st Int) (cs1 Int) (cs2 Int))
		   (=> (and (AbstractState st) (CompositeState cs1) (CompositeState cs2) (compositeState st cs1) (compositeState st cs2)) 
		       (= cs1 cs2))) :named pre4))

;pre5a: a transition does belong to at least one state machine
(assert (! (forall ((t Int)) (=> (Transition t)
				 (exists ((sm Int)) (and (StateMachine sm) (tran-stateMachine t sm))))) :named pre5a))

;pre5b: a transition does belong to at most one state machine
(assert (! (forall ((t Int)) (=> (Transition t)
				 (forall ((sm1 Int) (sm2 Int)) 
					 (=> (and (StateMachine sm1) (tran-stateMachine t sm1)  (StateMachine sm2) (tran-stateMachine t sm2))
					     (= sm1 sm2))))) :named pre5b))

;pre6a: a transition has at least one source
(assert (! (forall ((t Int)) (=> (Transition t)
				 (exists ((st Int)) (and (AbstractState st) (source t st))))) :named pre6a))

;pre6b: a transition has at most one source
(assert (! (forall ((t Int)) (=> (Transition t)
				 (forall ((st1 Int) (st2 Int)) 
					 (=> (and (AbstractState st1) (source t st1)  (AbstractState st2) (source t st2))
					     (= st1 st2))))) :named pre6b))

;pre7a: a transition has at least one target
(assert (! (forall ((t Int)) (=> (Transition t)
				 (exists ((st Int)) (and (AbstractState st) (target t st))))) :named pre7a))

;pre7b: a transition has at most one target
(assert (! (forall ((t Int)) (=> (Transition t)
				 (forall ((st1 Int) (st2 Int)) 
					 (=> (and (AbstractState st1) (target t st1)  (AbstractState st2) (target t st2))
					     (= st1 st2))))) :named pre7b))

;pre8: transition and source belong to the same state machine
(assert (! (forall ((t Int)(st Int)(sm1 Int)(sm2 Int)) 
	   (=> (and (Transition t) (AbstractState st) (StateMachine sm1) (StateMachine sm2) (st-stateMachine st sm1) (tran-stateMachine t sm2) (source t st))
	       (= sm1 sm2))) :named pre8))

;pre9: transition and target belong to the same state machine
(assert (! (forall ((t Int)(st Int)(sm1 Int)(sm2 Int)) 
	   (=> (and (Transition t) (AbstractState st) (StateMachine sm1) (StateMachine sm2) (st-stateMachine st sm1) (tran-stateMachine t sm2) (target t st))
	       (= sm1 sm2))) :named pre9))


;pre10: source and target belong to the same state machine
(assert (! (forall ((t Int)(src Int)(trg Int)(sm1 Int)(sm2 Int)) 
		   (=> (and (Transition t) (AbstractState src) (AbstractState trg) (StateMachine sm1) (StateMachine sm2)(source t src) (target t trg) (st-stateMachine src sm1) (st-stateMachine trg sm2))
		       (= sm1 sm2))) :named pre11))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Postconditions                                                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; post1: different target state machines have different names
;; (assert (! (not (forall ((s1 Int) (s2 Int))
;; 			(=> (and (not (= s1 s2)) (TGStateMachine s1) (TGStateMachine s2))
;; 			    (not (= (TGnameMach s1) (TGnameMach s2)))))) :named post1))


; post2: within a state machine, states have unique names
(assert (! (not (forall ((sm Int) (s1 Int) (s2 Int))
       			(=> (and (TGStateMachine sm) (TGAbstractState s1) (TGAbstractState s2) (TGst-stateMachine s1 sm) (TGst-stateMachine s2 sm) (not (= s1 s2)) )
       			    (not (= (TGname s1) (TGname s2)))))) :named post2))

;; ; post3a: a state does belong to at least one state machine
;; (assert (! (not (forall ((st Int)) (=> (TGAbstractState st)
;;  				       (exists ((sm Int)) (and (TGStateMachine sm) (TGst-stateMachine st sm)))))) :named post3a))

;; ; post3b: a state does not belong to more than one state machine
;; (assert (! (not (forall ((st Int)) (=> (TGAbstractState st)
;;  				  (forall ((sm1 Int) (sm2 Int)) 
;;  					  (=> (and (TGStateMachine sm1) (TGst-stateMachine st sm1)  (TGStateMachine sm2) (TGst-stateMachine st sm2))
;;  					      (= sm1 sm2)))))) :named post3b))

;; ; post4a: a transition does belong to at least one state machine
;; (assert (! (not (forall ((t Int)) (=> (TGTransition t)
;;    				      (exists ((sm Int)) (and (TGStateMachine sm) (TGtran-stateMachine t sm)))))) :named post4a))

;; ;post4b: a transition does belong to at most one state machine
;; (assert (! (not (forall ((t Int)) (=> (TGTransition t)
;; 				      (forall ((sm1 Int) (sm2 Int)) 
;;  					      (=> (and (TGStateMachine sm1) (TGtran-stateMachine t sm1)  (TGStateMachine sm2) (TGtran-stateMachine t sm2))
;;  						  (= sm1 sm2)))))) :named post4b))

;; ;post5a: a transition has at least one source
;; (assert (!  (not (forall ((t Int)) (=> (TGTransition t)
;; 				 (exists ((st Int)) (and (TGAbstractState st) (TGsource t st)))))) :named post5a))

;; ;post5b: a transition has at most one source
;; (assert (! (not (forall ((t Int)) (=> (TGTransition t)
;; 				 (forall ((st1 Int) (st2 Int)) 
;; 					 (=> (and (TGAbstractState st1) (TGsource t st1)  (TGAbstractState st2) (TGsource t st2))
;; 					     (= st1 st2)))))) :named post5b))

;; ;post6: transition and source belong to the same state machine
;; (assert (! (not (forall ((t Int)(st Int)(sm1 Int)(sm2 Int)) 
;; 			(=> (and (TGTransition t) (TGAbstractState st) (TGStateMachine sm1) (TGStateMachine sm2) (TGst-stateMachine st sm1) (TGtran-stateMachine t sm2) (TGsource t st))
;; 			    (= sm1 sm2)))) :named post6))

;; ;post7: transition and target belong to the same state machine
;; (assert (!  (not (forall ((t Int)(st Int)(sm1 Int)(sm2 Int)) 
;; 			(=> (and (TGTransition t) (TGAbstractState st) (TGStateMachine sm1) (TGStateMachine sm2) (TGst-stateMachine st sm1) (TGtran-stateMachine t sm2) (TGtarget t st))
;; 			    (= sm1 sm2)))) :named post7))


;; ;post8a: a transition has at least one target
;;  (assert (! (not (forall ((t Int)) (=> (TGTransition t)
;;  				 (exists ((st Int)) (and (TGAbstractState st) (TGtarget t st)))))) :named post8a))

;; ;post8b: a transition has at most one target
;; (assert (! (not (forall ((t Int)) (=> (TGTransition t)
;; 				 (forall ((st1 Int) (st2 Int)) 
;; 					 (=> (and (TGAbstractState st1) (TGtarget t st1)  (TGAbstractState st2) (TGtarget t st2))
;; 					     (= st1 st2)))))) :named post8b))

;post9: source and target belong to the same state machine
;; (assert (! (not (forall ((t Int)(src Int)(trg Int)(sm1 Int)(sm2 Int)) 
;; 		   (=> (and (TGTransition t) (TGAbstractState src) (TGAbstractState trg) (TGStateMachine sm1) (TGStateMachine sm2)(TGsource t src) (TGtarget t trg) (TGst-stateMachine src sm1) (TGst-stateMachine trg sm2))
;; 		       (= sm1 sm2)))) :named post9))