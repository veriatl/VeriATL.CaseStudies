procedure SM2SM_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall sm1: ref :: sm1!=null && read($srcHeap, sm1, alloc) && dtype(sm1) <: HSM$StateMachine 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(sm1)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(sm1)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(sm1))) <: FSM$StateMachine);
  modifies $tarHeap;
// Rule outcome


  ensures (forall sm1: ref :: sm1!=null && read($srcHeap, sm1, alloc) && dtype(sm1) <: HSM$StateMachine 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(sm1)), FSM$StateMachine.name) == read($srcHeap, sm1, HSM$StateMachine.name));


// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$StateMachine && ( dtype($o) <: FSM$StateMachine && ($f == FSM$StateMachine.name))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
  
  
implementation SM2SM_applyAllTest () returns ()
{
	var $i : int;
	var link : ref;
	var links: Seq ref;
	
	links := NTransientLinkSet#getLinksByRule($linkHeap, _SM2SM);
	assume SM2SM_links($srcHeap,$linkHeap,$tarHeap,links);
	
	$i:=0;
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
			$o != null && read(old($tarHeap), $o, alloc) ==>
				((dtype($o) <: FSM$StateMachine && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$StateMachine && $f == FSM$StateMachine.name) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_sm1])), FSM$StateMachine.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_sm1], HSM$StateMachine.name]
		);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
	{
		link := Seq#Index(links, $i);		
		call SM2SM_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}


procedure SM2SM_apply(in: ref) returns();
free requires surj_tar_model($srcHeap, $tarHeap);
//free requires isValidSrc($srcHeap);
//free requires isInstTar($tarHeap);
// link info
free requires $linkHeap[in, alloc] == true;
free requires dtype(in) == Native$TransientLink;
// rule info
free requires $linkHeap[in, TransientLink#rule]==_SM2SM;  
free requires Map#Domain($linkHeap[in, TransientLink#source])[_sm1];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_sm1]) <: HSM$StateMachine;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_sm1] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_sm1], alloc);

free requires Map#Domain($linkHeap[in, TransientLink#target])[_sm2];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_sm2]) <: FSM$StateMachine;
free requires Map#Elements($linkHeap[in, TransientLink#target])[_sm2] != null;
free requires read($tarHeap, Map#Elements($linkHeap[in, TransientLink#target])[_sm2], alloc);

// Correspondence I/O
free requires getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_sm1])) == Map#Elements($linkHeap[in, TransientLink#target])[_sm2];
// Guard
free requires true ;
// modifies
modifies $tarHeap;
// Rule outcome

ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_sm1])), FSM$StateMachine.name) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_sm1], HSM$StateMachine.name);


// Frame 
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$StateMachine && ( dtype($o) <: FSM$StateMachine && ($f == FSM$StateMachine.name))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_sm1])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );
// Preserving
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);
  

implementation SM2SM_apply (in: ref) returns ()
{

var stk: Seq BoxType;
var $newCol: ref;
var sm2: ref;	//slot: 3
var sm1: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _sm1);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, sm1 := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _sm2);
call stk := NTransientLink#getTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, sm2 := OpCode#Store(stk);
call stk := OpCode#Load(stk, sm2);
call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, sm1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),HSM$StateMachine.name)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),FSM$StateMachine.name,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Pop(stk);

}



// properties of each link of e2r rule
function SM2SM_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) <: HSM$StateMachine ==> 
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_sm1] == r ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_sm2] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_sm2], alloc) && getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_sm1])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_sm2]
		)

}