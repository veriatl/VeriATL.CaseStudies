procedure unique_fsm_state_names()
// valid src model, consider re-factoring.
requires (forall st: ref::
	st!=null && read($srcHeap,st,alloc) && dtype(st)<:HSM$AbstractState
	==>
	dtype(read($srcHeap,st,HSM$AbstractState.stateMachine)) == HSM$StateMachine
);
// pre1
requires (forall o1,o2: ref :: 
	o1!=null && read($srcHeap,o1,alloc) && dtype(o1)==HSM$StateMachine&&
	o2!=null && read($srcHeap,o2,alloc) && dtype(o2)==HSM$StateMachine
	&& o1!=o2
	==>
	read($srcHeap,o1,HSM$StateMachine.name) != read($srcHeap,o2,HSM$StateMachine.name)
);
// pre2
requires (forall o1,o2: ref :: 
	o1!=null && read($srcHeap,o1,alloc) && dtype(o1)<:HSM$AbstractState&&
	o2!=null && read($srcHeap,o2,alloc) && dtype(o2)<:HSM$AbstractState
	&& o1!=o2
	==>
	read($srcHeap,o1,HSM$AbstractState.name) != read($srcHeap,o2,HSM$AbstractState.name)
);
modifies $tarHeap,$linkHeap;
// post2: unique_fsm_state_names
ensures (forall o1,o2: ref :: 
	o1!=null && read($tarHeap,o1,alloc) && dtype(o1)<:FSM$AbstractState&&
	o2!=null && read($tarHeap,o2,alloc) && dtype(o2)<:FSM$AbstractState
	&& o1!=o2
	==>
	read($tarHeap,o1,FSM$AbstractState.name) != read($tarHeap,o2,FSM$AbstractState.name)
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


