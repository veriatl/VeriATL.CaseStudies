procedure fsm_state_multi_upper()
// valid src model, consider re-factoring.
requires (forall st: ref::
{read($srcHeap,st,alloc)}
	st!=null && read($srcHeap,st,alloc) && dtype(st)<:HSM$AbstractState
	&& read($srcHeap,st,HSM$AbstractState.stateMachine) !=null
	&& read($srcHeap,read($srcHeap,st,HSM$AbstractState.stateMachine),alloc)
	==>
	dtype(read($srcHeap,st,HSM$AbstractState.stateMachine)) == HSM$StateMachine
);
// pre1
requires (forall o1,o2: ref :: 
{read($srcHeap,o1,alloc),read($srcHeap,o2,alloc)}
	o1!=null && read($srcHeap,o1,alloc) && dtype(o1)==HSM$StateMachine&&
	o2!=null && read($srcHeap,o2,alloc) && dtype(o2)==HSM$StateMachine
	&& o1!=o2
	==>
	read($srcHeap,o1,HSM$StateMachine.name) != read($srcHeap,o2,HSM$StateMachine.name)
);
// pre2
requires (forall o1,o2: ref :: 
{read($srcHeap,o1,alloc),read($srcHeap,o2,alloc)}
	o1!=null && read($srcHeap,o1,alloc) && dtype(o1)<:HSM$AbstractState&&
	o2!=null && read($srcHeap,o2,alloc) && dtype(o2)<:HSM$AbstractState
	&& o1!=o2
	==>
	read($srcHeap,o1,HSM$AbstractState.name) != read($srcHeap,o2,HSM$AbstractState.name)
);
// pre3a rewrite
requires (forall st: ref:: {st!=null,read($srcHeap,st,alloc),dtype(st)<:HSM$AbstractState}
	st!=null && read($srcHeap,st,alloc) && dtype(st)<:HSM$AbstractState
	==>
	read($srcHeap,st,HSM$AbstractState.stateMachine) != null && read($srcHeap,read($srcHeap,st,HSM$AbstractState.stateMachine),alloc) 
);
// pre3b, not necessary to prove post3b
requires (forall st: ref:: {st!=null,read($srcHeap,st,alloc),dtype(st)<:HSM$AbstractState}
	st!=null && read($srcHeap,st,alloc) && dtype(st)<:HSM$AbstractState
	==>
	(forall sm1,sm2: ref:: 
		sm1!=null && read($srcHeap,sm1,alloc) && dtype(sm1)==HSM$StateMachine &&
		sm2!=null && read($srcHeap,sm2,alloc) && dtype(sm2)==HSM$StateMachine &&
		read($srcHeap,st,HSM$AbstractState.stateMachine) == sm1 &&
		read($srcHeap,st,HSM$AbstractState.stateMachine) == sm2
			==>
		sm1 == sm2));
modifies $tarHeap,$linkHeap;
// post3b: fsm_state_multi_upper
ensures (forall st: ref:: {read($tarHeap,st,alloc),st!=null,dtype(st)<:FSM$AbstractState}
	st!=null && read($tarHeap,st,alloc) && dtype(st)<:FSM$AbstractState
	==>
	(forall sm1,sm2: ref:: 
		sm1!=null && read($tarHeap,sm1,alloc) && dtype(sm1)==FSM$StateMachine &&
		sm2!=null && read($tarHeap,sm2,alloc) && dtype(sm2)==FSM$StateMachine &&
		read($tarHeap,st,FSM$AbstractState.stateMachine) == sm1 &&
		read($tarHeap,st,FSM$AbstractState.stateMachine) == sm2
			==>
		sm1 == sm2));
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


