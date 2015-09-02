// ------------------------------------------------------------
// -- Source Metamodel Modelling ------------------------------
// ------------------------------------------------------------

const unique HSM$StateMachine: ClassName extends  complete;
const unique HSM$StateMachine.transitions: Field ref;
const unique HSM$StateMachine.states: Field ref;
const unique HSM$StateMachine.name: Field String;

const unique HSM$Transition: ClassName extends  complete;
const unique HSM$Transition.stateMachine: Field ref;
const unique HSM$Transition.source: Field ref;
const unique HSM$Transition.target: Field ref;
const unique HSM$Transition.label: Field String;

const unique HSM$AbstractState: ClassName extends  complete;
	axiom (forall r: ref :: dtype(r)!=HSM$AbstractState);
const unique HSM$AbstractState.stateMachine: Field ref;
const unique HSM$AbstractState.name: Field String;
const unique HSM$AbstractState.compositeState: Field ref;

const unique HSM$InitialState: ClassName extends HSM$AbstractState complete;

const unique HSM$RegularState: ClassName extends HSM$AbstractState complete;

const unique HSM$CompositeState: ClassName extends HSM$AbstractState complete;
const unique HSM$CompositeState.states: Field ref;




const unique FSM$StateMachine: ClassName extends  complete;
const unique FSM$StateMachine.transitions: Field ref;
const unique FSM$StateMachine.states: Field ref;
const unique FSM$StateMachine.name: Field String;

const unique FSM$Transition: ClassName extends  complete;
const unique FSM$Transition.stateMachine: Field ref;
const unique FSM$Transition.source: Field ref;
const unique FSM$Transition.target: Field ref;
const unique FSM$Transition.label: Field String;

const unique FSM$AbstractState: ClassName extends  complete;
	axiom (forall r: ref :: dtype(r)!=FSM$AbstractState);
const unique FSM$AbstractState.stateMachine: Field ref;
const unique FSM$AbstractState.name: Field String;
const unique FSM$AbstractState.compositeState: Field ref;

const unique FSM$InitialState: ClassName extends FSM$AbstractState complete;

const unique FSM$RegularState: ClassName extends FSM$AbstractState complete;

const unique FSM$CompositeState: ClassName extends FSM$AbstractState complete;
const unique FSM$CompositeState.states: Field ref;











  
  
  
// ---------------------------------------------------------------
// -- Auxulary Type/Data Structure Modelling ---------------------
// ---------------------------------------------------------------
const classifierTable : [String, String] ClassName;




// ASM-specific



  axiom classifierTable[_FSM, _StateMachine] == FSM$StateMachine;
  axiom classifierTable[_FSM, _RegularState] == FSM$RegularState;
  axiom classifierTable[_FSM, _InitialState] == FSM$InitialState;
  axiom classifierTable[_FSM, _CompositeState] == FSM$CompositeState;
  axiom classifierTable[_FSM, _AbstractState] == FSM$AbstractState;
  axiom classifierTable[_FSM, _Transition] == FSM$Transition;
  
  axiom classifierTable[_HSM, _StateMachine] == HSM$StateMachine;
  axiom classifierTable[_HSM, _RegularState] == HSM$RegularState;
  axiom classifierTable[_HSM, _InitialState] == HSM$InitialState;
  axiom classifierTable[_HSM, _CompositeState] == HSM$CompositeState;
  axiom classifierTable[_HSM, _AbstractState] == HSM$AbstractState;
  axiom classifierTable[_HSM, _Transition] == HSM$Transition;
  
  
  
function surj_tar_model($s: HeapType, $t: HeapType): bool
{	(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == FSM$StateMachine ==>
		(exists $i: ref :: dtype($i) == HSM$StateMachine && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o))
	&&
	(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == FSM$InitialState ==>
		(exists $i: ref :: (dtype($i) == HSM$InitialState && read($s,$i,HSM$AbstractState.compositeState)==null) && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o))
	&&
	(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == FSM$RegularState ==>
		(exists $i: ref :: (dtype($i) == HSM$RegularState || (dtype($i)== HSM$InitialState && read($s,$i,HSM$AbstractState.compositeState)!=null) ) && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o))
	&&
	(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == FSM$Transition ==>
	 (	(exists $i: ref :: 
			dtype($i) == HSM$Transition 
		&& dtype(read($s, $i, HSM$Transition.source)) != HSM$CompositeState 
		&& dtype(read($s, $i, HSM$Transition.target)) != HSM$CompositeState 
		&& $i != null && read($s, $i, alloc) 
		&& getTarsBySrcs(Seq#Singleton($i))==$o)
	 || (exists t1,src,trg,c: ref :: 
			t1!=null && read($s, t1, alloc) && dtype(t1) == HSM$Transition 
		&& src!=null && read($s, src, alloc) && dtype(src) == HSM$CompositeState 
		&& trg!=null && read($s, trg, alloc) && dtype(trg) == HSM$AbstractState 
		&& c!=null && read($s, c, alloc) && dtype(c) == HSM$AbstractState 
		&& read($s, t1, HSM$Transition.source) == src 
		&& read($s, t1, HSM$Transition.target) == trg 
		&& read($s, c, HSM$AbstractState.compositeState) == src 
		&& !(dtype(trg) == HSM$CompositeState)
		&& getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c))==$o )	
	 || (exists t1,src,trg,c: ref :: 
			t1!=null && read($s, t1, alloc) && dtype(t1) == HSM$Transition 
		&& src!=null && read($s, src, alloc) && dtype(src) == HSM$AbstractState 
		&& trg!=null && read($s, trg, alloc) && dtype(trg) == HSM$CompositeState 
		&& c!=null && read($s, c, alloc) && dtype(c) == HSM$InitialState 
		&& read($s, t1, HSM$Transition.source) == src 
		&& read($s, t1, HSM$Transition.target) == trg 
		&& read($s, c, HSM$AbstractState.compositeState) == trg 
		&& !(dtype(src) == HSM$CompositeState)
		&& getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c))==$o)
	  )
	 )
}  



// === Aux ===

  
  
const unique _sm1: String;
const unique _sm2: String;
const unique _rs1: String;
const unique _rs2: String;
const unique _is1: String;
const unique _is2: String;
const unique _t1: String;
const unique _t2: String;
const unique _c: String;
const unique _src: String;
const unique _trg: String;
const unique _SM2SM: String;
const unique _RS2RS: String;
const unique _IS2IS: String;
const unique _IS2RS: String;
const unique _T2TA: String;
const unique _T2TB: String;
const unique _T2TC: String;
const unique _HSM: String;
const unique _FSM: String;
const unique _StateMachine: String;
const unique _AbstractState: String;
const unique _RegularState: String;
const unique _InitialState: String;
const unique _CompositeState: String;
const unique _Transition: String;
const unique _IN: String;




const unique _Field$name: NameFamily;
const unique _Field$links: NameFamily;
const unique _Field$stateMachine: NameFamily;
const unique _Field$compositeState: NameFamily;
const unique _Field$source: NameFamily;
const unique _Field$target: NameFamily;
const unique _Field$label: NameFamily;

  axiom (FieldOfDecl(HSM$StateMachine, _Field$name) == HSM$StateMachine.name);
  axiom (FieldOfDecl(HSM$Transition, _Field$source) == HSM$Transition.source);
  axiom (FieldOfDecl(HSM$Transition, _Field$target) == HSM$Transition.target);
  axiom (FieldOfDecl(HSM$Transition, _Field$label) == HSM$Transition.label);
  axiom (FieldOfDecl(HSM$Transition, _Field$stateMachine) == HSM$Transition.stateMachine); 
  axiom (FieldOfDecl(HSM$InitialState, _Field$compositeState) == HSM$AbstractState.compositeState);
  axiom (FieldOfDecl(HSM$RegularState, _Field$compositeState) == HSM$AbstractState.compositeState);
  axiom (FieldOfDecl(HSM$CompositeState, _Field$compositeState) == HSM$AbstractState.compositeState);

  

  
  axiom (FieldOfDecl(FSM$StateMachine, _Field$name) == FSM$StateMachine.name);
  axiom (FieldOfDecl(FSM$Transition, _Field$source) == FSM$Transition.source);
  axiom (FieldOfDecl(FSM$Transition, _Field$target) == FSM$Transition.target); 
  axiom (FieldOfDecl(FSM$Transition, _Field$label) == FSM$Transition.label); 
  axiom (FieldOfDecl(FSM$Transition, _Field$stateMachine) == FSM$Transition.stateMachine); 
  axiom (FieldOfDecl(FSM$InitialState, _Field$compositeState) == FSM$AbstractState.compositeState);
