procedure T2TB_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall t1,src,trg,c: ref :: t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)), alloc)
&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c))) <: FSM$Transition);
  modifies $tarHeap;
// Rule outcome
  ensures (forall t1,src,trg,c: ref :: t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)), FSM$Transition.label) == read($srcHeap, t1, HSM$Transition.label));
  ensures (forall t1,src,trg,c: ref :: t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)), FSM$Transition.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, t1, HSM$Transition.stateMachine))));
  ensures (forall t1,src,trg,c: ref :: t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)), FSM$Transition.source) == getTarsBySrcs(Seq#Singleton(c)));
  ensures (forall t1,src,trg,c: ref :: t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)), FSM$Transition.target) == getTarsBySrcs(Seq#Singleton(trg)));
// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && ( dtype($o) <: FSM$Transition && ($f == FSM$Transition.label || $f == FSM$Transition.stateMachine || $f == FSM$Transition.source || $f == FSM$Transition.target))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
  
  
implementation T2TB_applyAllTest () returns ()
{
	var $i : int;
	var link : ref;
	var links: Seq ref;
	
	links := NTransientLinkSet#getLinksByRule($linkHeap, _T2TB);
	assume T2TB_links($srcHeap,$linkHeap,$tarHeap,links);
	
	$i:=0;
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && ( dtype($o) <: FSM$Transition && ($f == FSM$Transition.label || $f == FSM$Transition.stateMachine || $f == FSM$Transition.source || $f == FSM$Transition.target))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_t1]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_src]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_trg]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_c])), FSM$Transition.label) == read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_t1], HSM$Transition.label)
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_t1]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_src]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_trg]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_c])), FSM$Transition.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_t1], HSM$Transition.stateMachine)))
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_t1]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_src]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_trg]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_c])), FSM$Transition.source) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_c]))
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_t1]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_src]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_trg]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_c])), FSM$Transition.target) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_trg]))
		);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: !read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
	{
		link := Seq#Index(links, $i);		
		call T2TB_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}

procedure T2TB_apply (in: ref) returns ();
  free requires surj_tar_model($srcHeap, $tarHeap);
  free requires $linkHeap[in, TransientLink#rule]==_T2TB;  
  free requires $linkHeap[in, alloc] == true;
  free requires dtype(in) <: Native$TransientLink;
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_t1];
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_src];
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_trg];
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_c];
  free requires Map#Domain($linkHeap[in, TransientLink#target])[_t2];
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_t1]) <:HSM$Transition;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_t1] != null;
  free requires read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_t1],alloc);
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_src]) <:HSM$CompositeState;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_src] != null;
  free requires read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_src],alloc);
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_trg]) <:HSM$AbstractState;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_trg] != null;
  free requires read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_trg],alloc);
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_c]) <:HSM$AbstractState;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_c] != null;
  free requires read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_c],alloc);
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t2]) <: FSM$Transition;
  free requires Map#Elements($linkHeap[in, TransientLink#target])[_t2] != null;
  free requires read($tarHeap,Map#Elements($linkHeap[in, TransientLink#target])[_t2],alloc);
  free requires getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_t1]),Map#Elements($linkHeap[in, TransientLink#source])[_src]),Map#Elements($linkHeap[in, TransientLink#source])[_trg]),Map#Elements($linkHeap[in, TransientLink#source])[_c])) == Map#Elements($linkHeap[in, TransientLink#target])[_t2];
  modifies $tarHeap;
  ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_t1]),Map#Elements($linkHeap[in, TransientLink#source])[_src]),Map#Elements($linkHeap[in, TransientLink#source])[_trg]),Map#Elements($linkHeap[in, TransientLink#source])[_c])), FSM$Transition.label) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_t1], HSM$Transition.label);
  ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_t1]),Map#Elements($linkHeap[in, TransientLink#source])[_src]),Map#Elements($linkHeap[in, TransientLink#source])[_trg]),Map#Elements($linkHeap[in, TransientLink#source])[_c])), FSM$Transition.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_t1], HSM$Transition.stateMachine)));
  ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_t1]),Map#Elements($linkHeap[in, TransientLink#source])[_src]),Map#Elements($linkHeap[in, TransientLink#source])[_trg]),Map#Elements($linkHeap[in, TransientLink#source])[_c])), FSM$Transition.source) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_c]));
  ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_t1]),Map#Elements($linkHeap[in, TransientLink#source])[_src]),Map#Elements($linkHeap[in, TransientLink#source])[_trg]),Map#Elements($linkHeap[in, TransientLink#source])[_c])), FSM$Transition.target) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_trg]));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && ( dtype($o) <: FSM$Transition && ($f == FSM$Transition.label || $f == FSM$Transition.stateMachine || $f == FSM$Transition.source || $f == FSM$Transition.target))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o !=  getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_t1]),Map#Elements($linkHeap[in, TransientLink#source])[_src]),Map#Elements($linkHeap[in, TransientLink#source])[_trg]),Map#Elements($linkHeap[in, TransientLink#source])[_c])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );	
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
		 
implementation T2TB_apply (in: ref) returns ()
{
var stk: Seq BoxType;
var $i: int;
var t2: ref;	//slot: 6
var t1: ref;	//slot: 2
var src: ref;	//slot: 3
var trg: ref;	//slot: 4
var c: ref;	//slot: 5
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _t1);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, t1 := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _src);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, src := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _trg);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, trg := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _c);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, c := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _t2);
call stk := NTransientLink#getTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, t2 := OpCode#Store(stk);
call stk := OpCode#Load(stk, t2);
call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, t1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: HSM$Transition;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),HSM$Transition.label)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) <: FSM$Transition;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$Transition.label,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, t1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: HSM$Transition;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),HSM$Transition.stateMachine)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assume $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_t1], HSM$Transition.stateMachine)));
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) <: FSM$Transition;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$Transition.stateMachine,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, c);
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assume $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_c]));
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) <: FSM$Transition;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$Transition.source,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, trg);
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assume $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_trg]));
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) <: FSM$Transition;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$Transition.target,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Pop(stk);

}





		 
// properties of each link of e2r rule
function T2TB_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall t1,src,trg,c: ref :: {read($srcHeap, t1, alloc),read($srcHeap, src, alloc),read($srcHeap, trg, alloc),read($srcHeap, c, alloc)}
 t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) 
			&& Map#Elements(read($linkHeap, l, TransientLink#source))[_t1] == t1 
			&& Map#Elements(read($linkHeap, l, TransientLink#source))[_src] == src 
			&& Map#Elements(read($linkHeap, l, TransientLink#source))[_trg] == trg 
			&& Map#Elements(read($linkHeap, l, TransientLink#source))[_c] == c )
)
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t2] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t2], alloc) && getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_t1]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_src]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_trg]),Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_c])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t2]
		)

}