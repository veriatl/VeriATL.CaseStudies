/*
rule R2R { from s : ER!Relship 
           to t : REL!Relation ( name  <- s.name ) }

*/

procedure R2R_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$Relship 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(s)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(s))) <: REL$Relation);
  modifies $tarHeap;
// Rule outcome


  ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$Relship 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$Relation.name) == read($srcHeap, s, ER$Relship.name));


// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$Relship && ( dtype($o) <: REL$Relation && ($f == REL$Relation.name))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);

implementation R2R_applyAllTest()
{

	var $i : int;
	var link : ref;
	var links:Seq ref;

    links := NTransientLinkSet#getLinksByRule($linkHeap, _R2R);
    assume R2R_links($srcHeap,$linkHeap,$tarHeap,links);

	$i:=0;

	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
			$o != null && read(old($tarHeap), $o, alloc) ==>
				((dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$Relship && $f == REL$Relation.name) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$Relation.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$Relship.name]
		);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
		
	{
		link := Seq#Index(links, $i);		
		call R2R_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}


procedure R2R_apply(in: ref) returns();
free requires surj_tar_model($srcHeap, $tarHeap);
//free requires isValidSrc($srcHeap);
//free requires isInstTar($tarHeap);
// link info
free requires $linkHeap[in, alloc] == true;
free requires dtype(in) == Native$TransientLink;
// rule info
free requires $linkHeap[in, TransientLink#rule]==_R2R;  
free requires Map#Domain($linkHeap[in, TransientLink#source])[_s];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_s]) <: ER$Relship;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_s] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], alloc);

free requires Map#Domain($linkHeap[in, TransientLink#target])[_t];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t]) <: REL$Relation;
free requires Map#Elements($linkHeap[in, TransientLink#target])[_t] != null;
free requires read($tarHeap, Map#Elements($linkHeap[in, TransientLink#target])[_t], alloc);

// Correspondence I/O
free requires getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])) == Map#Elements($linkHeap[in, TransientLink#target])[_t];
// Guard
free requires true ;
// modifies
modifies $tarHeap;
// Rule outcome

ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$Relation.name) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$Relship.name);


// Frame 
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$Relship && ( dtype($o) <: REL$Relation && ($f == REL$Relation.name))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );
// Preserving
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);

implementation R2R_apply (in: ref) returns ()
{

var stk: Seq BoxType;
var $newCol: ref;
var t: ref;	//slot: 3
var s: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _s);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, s := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _t);
call stk := NTransientLink#getTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, t := OpCode#Store(stk);
call stk := OpCode#Load(stk, t);
call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, s);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ER$Relship.name)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),REL$Relation.name,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Pop(stk);

}



// properties of each link of r2r rule
function R2R_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) <: ER$Relship ==> 
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_s] == r ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t], alloc) && getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t]
		)

}