procedure IS2IS_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall is1: ref :: is1!=null && read($srcHeap, is1, alloc) && dtype(is1) <: HSM$InitialState 
 ==>
 read($srcHeap, is1, HSM$AbstractState.compositeState)==null  ==>
getTarsBySrcs(Seq#Singleton(is1)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(is1)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(is1))) <: FSM$InitialState);
  modifies $tarHeap;
// Rule outcome


  ensures (forall is1: ref :: is1!=null && read($srcHeap, is1, alloc) && dtype(is1) <: HSM$InitialState 
 ==>
 read($srcHeap, is1, HSM$AbstractState.compositeState)==null  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(is1)), FSM$AbstractState.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, is1, HSM$AbstractState.stateMachine))));
  ensures (forall is1: ref :: is1!=null && read($srcHeap, is1, alloc) && dtype(is1) <: HSM$InitialState 
 ==>
 read($srcHeap, is1, HSM$AbstractState.compositeState)==null  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(is1)), FSM$AbstractState.name) == read($srcHeap, is1, HSM$AbstractState.name));



// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$InitialState && ( dtype($o) <: FSM$InitialState && ($f == FSM$AbstractState.stateMachine || $f == FSM$AbstractState.name))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
  
  
implementation IS2IS_applyAllTest () returns ()
{
	var $i : int;
	var link : ref;
	var links: Seq ref;
	
	links := NTransientLinkSet#getLinksByRule($linkHeap, _IS2IS);
	assume IS2IS_links($srcHeap,$linkHeap,$tarHeap,links);
	
	$i:=0;
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
			$o != null && read(old($tarHeap), $o, alloc) ==>
				((dtype($o) <: FSM$InitialState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$InitialState && ($f == FSM$AbstractState.name || $f == FSM$AbstractState.stateMachine)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_is1])), FSM$AbstractState.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_is1], HSM$AbstractState.name]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_is1])), FSM$AbstractState.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_is1], HSM$AbstractState.stateMachine)))
		);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
	{
		link := Seq#Index(links, $i);		
		call IS2IS_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}


procedure IS2IS_apply (in: ref) returns ();
  free requires surj_tar_model($srcHeap, $tarHeap);
  free requires $linkHeap[in, TransientLink#rule]==_IS2IS;  
  free requires $linkHeap[in, alloc] == true;
  free requires dtype(in) <: Native$TransientLink;
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_is1];
  free requires Map#Domain($linkHeap[in, TransientLink#target])[_is2];
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_is1]) <:HSM$InitialState;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_is1] != null;
  free requires read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_is1],alloc);
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_is2]) <: FSM$InitialState;
  free requires Map#Elements($linkHeap[in, TransientLink#target])[_is2] != null;
  free requires read($tarHeap,Map#Elements($linkHeap[in, TransientLink#target])[_is2],alloc);
  free requires getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_is1])) == Map#Elements($linkHeap[in, TransientLink#target])[_is2];
  free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_is1], HSM$AbstractState.compositeState)==null;
  modifies $tarHeap;
  ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_is1])), FSM$AbstractState.name) == read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_is1],HSM$AbstractState.name);
  ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_is1])), FSM$AbstractState.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_is1], HSM$AbstractState.stateMachine)));		
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) <: FSM$InitialState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$InitialState && ($f == FSM$AbstractState.name || $f == FSM$AbstractState.stateMachine)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_is1])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );	
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
		 
implementation IS2IS_apply (in: ref) returns ()
{

var stk: Seq BoxType;
var $i: int;
var is2: ref;	//slot: 3
var is1: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _is1);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, is1 := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _is2);
call stk := NTransientLink#getTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, is2 := OpCode#Store(stk);
call stk := OpCode#Load(stk, is2);
call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, is1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: HSM$InitialState;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),HSM$AbstractState.stateMachine)));
assert $Unbox(top(stk)) == (read($srcHeap, is1, HSM$AbstractState.stateMachine));
				
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assume $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref == getTarsBySrcs(Seq#Singleton(read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_is1],HSM$AbstractState.stateMachine)));
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) <: FSM$InitialState;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$AbstractState.stateMachine,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, is1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: HSM$InitialState;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),HSM$AbstractState.name)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) <: FSM$InitialState;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$AbstractState.name,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Pop(stk);

}




		 
// properties of each link of e2r rule
function IS2IS_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) <: HSM$InitialState ==> 
	read($srcHeap, r, HSM$AbstractState.compositeState)==null  ==>
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_is1] == r ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_is2] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_is2], alloc) && getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_is1])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_is2]
		)

}