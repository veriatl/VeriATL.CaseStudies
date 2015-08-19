procedure fsm_transition_contain_sm()
// valid src model, consider re-factoring.
requires (forall st: ref::
	st!=null && read($srcHeap,st,alloc) && dtype(st)<:HSM$AbstractState
	==>
	dtype(read($srcHeap,st,HSM$AbstractState.stateMachine)) == HSM$StateMachine
);
// same as in pre5a
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	==>
	dtype(read($srcHeap,t,HSM$Transition.stateMachine)) == HSM$StateMachine
);
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	==>
	dtype(read($srcHeap,t,HSM$Transition.source)) <: HSM$AbstractState
);
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	==>
	dtype(read($srcHeap,t,HSM$Transition.target)) <: HSM$AbstractState
);
// pre6a
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	==>
	(read($srcHeap,read($srcHeap,t,HSM$Transition.source),alloc) 
	&& read($srcHeap,t,HSM$Transition.source)!=null
	&& dtype(read($srcHeap,t,HSM$Transition.source)) <: HSM$AbstractState)
);
// pre7a
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	==>
	(read($srcHeap,read($srcHeap,t,HSM$Transition.target),alloc)
	&& read($srcHeap,t,HSM$Transition.target)!=null
	&& dtype(read($srcHeap,t,HSM$Transition.target)) <: HSM$AbstractState)
);
// pre5a
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	==>
	(exists sm: ref:: sm!=null && read($srcHeap,sm,alloc) && dtype(sm)==HSM$StateMachine&& read($srcHeap,t,HSM$Transition.stateMachine)==sm)
);
//pre8
requires (forall t,src: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition &&
	src!=null && read($srcHeap,src,alloc) && dtype(src)<:HSM$AbstractState &&
	read($srcHeap,t,HSM$Transition.source) == src
	==>
	(forall sm1,sm2: ref:: 
		sm1!=null && read($srcHeap,sm1,alloc) && dtype(sm1)<:HSM$StateMachine &&
		sm2!=null && read($srcHeap,sm2,alloc) && dtype(sm2)<:HSM$StateMachine &&
		read($srcHeap,t,HSM$Transition.stateMachine) == sm1 &&
		read($srcHeap,src,HSM$AbstractState.stateMachine) == sm2
			==>
		sm1 == sm2));
//pre9
requires (forall t,trg: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition &&
	trg!=null && read($srcHeap,trg,alloc) && dtype(trg)<:HSM$AbstractState &&
	read($srcHeap,t,HSM$Transition.target) == trg
	==>
	(forall sm1,sm2: ref:: 
		sm1!=null && read($srcHeap,sm1,alloc) && dtype(sm1)<:HSM$StateMachine &&
		sm2!=null && read($srcHeap,sm2,alloc) && dtype(sm2)<:HSM$StateMachine &&
		read($srcHeap,t,HSM$Transition.stateMachine) == sm1 &&
		read($srcHeap,trg,HSM$AbstractState.stateMachine) == sm2
			==>
		sm1 == sm2));
// pre11
requires (forall t,src,trg: ref::
{
read($srcHeap,t,alloc),
read($srcHeap,src,alloc),
read($srcHeap,trg,alloc) 
}
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition &&
	src!=null && read($srcHeap,src,alloc) && dtype(src)<:HSM$AbstractState &&
	trg!=null && read($srcHeap,trg,alloc) && dtype(trg)<:HSM$AbstractState &&
	read($srcHeap,t,HSM$Transition.source) == src &&
	read($srcHeap,t,HSM$Transition.target) == trg 
	==>
	(forall sm1,sm2: ref:: 
		sm1!=null && read($srcHeap,sm1,alloc) && dtype(sm1)<:HSM$StateMachine &&
		sm2!=null && read($srcHeap,sm2,alloc) && dtype(sm2)<:HSM$StateMachine &&
		read($srcHeap,src,HSM$AbstractState.stateMachine) == sm1 &&
		read($srcHeap,trg,HSM$AbstractState.stateMachine) == sm2
			==>
		sm1 == sm2));
modifies $tarHeap,$linkHeap;
// post9: fsm_transition_contain_sm
ensures (forall t,src,trg: ref::
{
read($tarHeap,t,alloc),
read($tarHeap,src,alloc),
read($tarHeap,trg,alloc)
}
	t!=null && read($tarHeap,t,alloc) && dtype(t)==FSM$Transition &&
	src!=null && read($tarHeap,src,alloc) && dtype(src)<:FSM$AbstractState &&
	trg!=null && read($tarHeap,trg,alloc) && dtype(trg)<:FSM$AbstractState &&
	read($tarHeap,t,FSM$Transition.source) == src &&
	read($tarHeap,t,FSM$Transition.target) == trg 
	==>
	(forall sm1,sm2: ref:: 
		sm1!=null && read($tarHeap,sm1,alloc) && dtype(sm1)<:FSM$StateMachine &&
		sm2!=null && read($tarHeap,sm2,alloc) && dtype(sm2)<:FSM$StateMachine &&
		read($tarHeap,src,FSM$AbstractState.stateMachine) == sm1 &&
		read($tarHeap,trg,FSM$AbstractState.stateMachine) == sm2
			==>
		sm1 == sm2));
// post9: fsm_transition_contain_sm, compiled by OCL2Boogie		
ensures (forall t:ref :: {read($tarHeap,t,alloc)}
  t!=null && read($tarHeap,t,alloc) && dtype(t)==FSM$Transition
    ==> 
(forall s1,s2:ref :: {read($tarHeap,s1,alloc),read($tarHeap,s2,alloc)}
  s1!=null && read($tarHeap,s1,alloc) && dtype(s1)<:FSM$AbstractState &&
  s2!=null && read($tarHeap,s2,alloc) && dtype(s2)<:FSM$AbstractState 
    ==> read($tarHeap, t, FSM$Transition.source) == s1 && read($tarHeap, t, FSM$Transition.target) == s2 ==> 
(forall sm1,sm2:ref :: {read($tarHeap,sm1,alloc), read($tarHeap,sm2,alloc)}
  sm1!=null && read($tarHeap,sm1,alloc) && dtype(sm1)<:FSM$StateMachine &&
  sm2!=null && read($tarHeap,sm2,alloc) && dtype(sm2)<:FSM$StateMachine 
    ==> read($tarHeap, s1, FSM$AbstractState.stateMachine) == sm1 && read($tarHeap, s2, FSM$AbstractState.stateMachine) == sm2 ==> sm1 == sm2)
)
);
{

	call init_tar_model(); 

	call SM2SM_matchAll();
	call RS2RS_matchAll();
	call IS2IS_matchAll();
	call IS2RS_matchAll();
	call T2TA_matchAll();
	call T2TB_matchAll();
	call T2TC_matchAll();



	call SM2SM_applyAll();
	call RS2RS_applyAll();
	call IS2IS_applyAll();
	call IS2RS_applyAll();
	call T2TA_applyAll();
	call T2TB_applyAll();
	call T2TC_applyAll();
	



}


