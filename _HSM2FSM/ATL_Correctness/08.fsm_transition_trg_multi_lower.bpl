procedure fsm_transition_trg_multi_lower()
// valid src model, consider re-factoring.
requires (forall st: ref::
	st!=null && read($srcHeap,st,alloc) && dtype(st)<:HSM$AbstractState
	&& read($srcHeap,st,HSM$AbstractState.stateMachine) !=null
	&& read($srcHeap,read($srcHeap,st,HSM$AbstractState.stateMachine),alloc)
	==>
	dtype(read($srcHeap,st,HSM$AbstractState.stateMachine)) == HSM$StateMachine
);
// same as in pre5a
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	&& read($srcHeap,t,HSM$Transition.stateMachine)!=null
	&& read($srcHeap,read($srcHeap,t,HSM$Transition.stateMachine),alloc)
	==>
	dtype(read($srcHeap,t,HSM$Transition.stateMachine)) == HSM$StateMachine
);
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	&& read($srcHeap,t,HSM$Transition.source)!=null
	&& read($srcHeap,read($srcHeap,t,HSM$Transition.source),alloc)
	==>
	dtype(read($srcHeap,t,HSM$Transition.source)) <: HSM$AbstractState
);
requires (forall t: ref::
	t!=null && read($srcHeap,t,alloc) && dtype(t)==HSM$Transition
	&& read($srcHeap,t,HSM$Transition.target)!=null
	&& read($srcHeap,read($srcHeap,t,HSM$Transition.target),alloc)
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
modifies $tarHeap,$linkHeap;
// post8a: fsm_transition_trg_multi_lower
 ensures (forall t: ref::
	t!=null && read($tarHeap,t,alloc) && dtype(t)==FSM$Transition
	==>
	(read($tarHeap,read($tarHeap,t,FSM$Transition.target),alloc)
	&& read($tarHeap,t,FSM$Transition.target)!=null
	&& dtype(read($tarHeap,t,FSM$Transition.target)) <: FSM$AbstractState)
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


