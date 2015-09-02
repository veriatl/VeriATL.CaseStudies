procedure RS2RS_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall rs1: ref :: rs1!=null && read($srcHeap, rs1, alloc) && dtype(rs1) <: HSM$RegularState 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(rs1)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(rs1)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(rs1))) <: FSM$RegularState);
  modifies $tarHeap;
// Rule outcome


  ensures (forall rs1: ref :: rs1!=null && read($srcHeap, rs1, alloc) && dtype(rs1) <: HSM$RegularState 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(rs1)), FSM$AbstractState.name) == read($srcHeap, rs1, HSM$AbstractState.name));
  ensures (forall rs1: ref :: rs1!=null && read($srcHeap, rs1, alloc) && dtype(rs1) <: HSM$RegularState 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(rs1)), FSM$AbstractState.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, rs1, HSM$AbstractState.stateMachine))));


// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$RegularState && ( dtype($o) <: FSM$RegularState && ($f == FSM$AbstractState.name || $f == FSM$AbstractState.stateMachine))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);

implementation RS2RS_applyAllTest () returns ()
{
	var $i : int;
	var link : ref;
	var links: Seq ref;
	
	links := NTransientLinkSet#getLinksByRule($linkHeap, _RS2RS);
	assume RS2RS_links($srcHeap,$linkHeap,$tarHeap,links);
	
	$i:=0;
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
			$o != null && read(old($tarHeap), $o, alloc) ==>
				((dtype($o) <: FSM$RegularState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$RegularState && ($f == FSM$AbstractState.name || $f == FSM$AbstractState.stateMachine)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs1])), FSM$AbstractState.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs1], HSM$AbstractState.name]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs1])), FSM$AbstractState.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs1], HSM$AbstractState.stateMachine)))
		);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
	{
		link := Seq#Index(links, $i);		
		call RS2RS_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}

procedure RS2RS_apply(in: ref) returns();
free requires surj_tar_model($srcHeap, $tarHeap);
//free requires isValidSrc($srcHeap);
//free requires isInstTar($tarHeap);
// link info
free requires $linkHeap[in, alloc] == true;
free requires dtype(in) == Native$TransientLink;
// rule info
free requires $linkHeap[in, TransientLink#rule]==_RS2RS;  
free requires Map#Domain($linkHeap[in, TransientLink#source])[_rs1];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_rs1]) <: HSM$RegularState;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_rs1] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rs1], alloc);

free requires Map#Domain($linkHeap[in, TransientLink#target])[_rs2];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_rs2]) <: FSM$RegularState;
free requires Map#Elements($linkHeap[in, TransientLink#target])[_rs2] != null;
free requires read($tarHeap, Map#Elements($linkHeap[in, TransientLink#target])[_rs2], alloc);

// Correspondence I/O
free requires getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_rs1])) == Map#Elements($linkHeap[in, TransientLink#target])[_rs2];
free requires dtype(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rs1], HSM$AbstractState.stateMachine)) != class._System.array;
// Guard
free requires true ;
// modifies
modifies $tarHeap;
// Rule outcome

ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_rs1])), FSM$AbstractState.name) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rs1], HSM$AbstractState.name);
ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_rs1])), FSM$AbstractState.stateMachine) == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rs1], HSM$AbstractState.stateMachine)));


// Frame 
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$RegularState && ( dtype($o) <: FSM$RegularState && ($f == FSM$AbstractState.name || $f == FSM$AbstractState.stateMachine))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_rs1])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );
// Preserving
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);
		 

implementation RS2RS_apply (in: ref) returns ()
{

var stk: Seq BoxType;
var $newCol: ref;
var rs2: ref;	//slot: 3
var rs1: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _rs1);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, rs1 := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _rs2);
call stk := NTransientLink#getTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, rs2 := OpCode#Store(stk);
call stk := OpCode#Load(stk, rs2);
call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, rs1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),HSM$AbstractState.name)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$AbstractState.name,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, rs1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),HSM$AbstractState.stateMachine)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$AbstractState.stateMachine,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Pop(stk);

}


		 
// properties of each link of e2r rule
function RS2RS_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) <: HSM$RegularState ==> 
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_rs1] == r ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_rs2] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_rs2], alloc) && getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs1])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_rs2]
		)

}