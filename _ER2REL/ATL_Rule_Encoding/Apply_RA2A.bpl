/*
rule RA2A { from att : ER!ERAttribute, rs  : ER!Relship ( att.relship = rs )
	        to t : REL!RELAttribute
			       ( name <- att.name, isKey <- att.isKey, relation <- rs ) }

*/


procedure RA2A_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall att,rs: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) <: ER$Relship 
 ==>
 read($srcHeap, att, ER$ERAttribute.relship) == rs  ==>
getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), alloc)
&& dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs))) <: REL$RELAttribute);
  modifies $tarHeap;
// Rule outcome


  ensures (forall att,rs: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) <: ER$Relship 
 ==>
 read($srcHeap, att, ER$ERAttribute.relship) == rs  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), REL$RELAttribute.name) == read($srcHeap, att, ER$ERAttribute.name));
  ensures (forall att,rs: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) <: ER$Relship 
 ==>
 read($srcHeap, att, ER$ERAttribute.relship) == rs  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), REL$RELAttribute.isKey) == read($srcHeap, att, ER$ERAttribute.isKey));
  ensures (forall att,rs: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) <: ER$Relship 
 ==>
 read($srcHeap, att, ER$ERAttribute.relship) == rs  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), REL$RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(rs)));


// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 2 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: ER$Relship && ( dtype($o) <: REL$RELAttribute && ($f == REL$RELAttribute.name || $f == REL$RELAttribute.isKey || $f == REL$RELAttribute.relation))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);

implementation RA2A_applyAllTest()
{

	var $i : int;
	var links : Seq ref;
	var link : ref;

	links := NTransientLinkSet#getLinksByRule($linkHeap, _RA2A);
	assume RA2A_links($srcHeap,$linkHeap,$tarHeap,links);

	$i:=0;

		
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])), REL$RELAttribute.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att], ER$ERAttribute.name]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])), REL$RELAttribute.isKey) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att], ER$ERAttribute.isKey]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])), REL$RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs]))
		);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 2 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: ER$Relship && ( dtype($o) <: REL$RELAttribute && ($f == REL$RELAttribute.name || $f == REL$RELAttribute.isKey || $f == REL$RELAttribute.relation))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
	{
		link := Seq#Index(links, $i);			
		call RA2A_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}


procedure RA2A_apply(in: ref) returns();
free requires surj_tar_model($srcHeap, $tarHeap);
//free requires isValidSrc($srcHeap);
//free requires isInstTar($tarHeap);
// link info
free requires $linkHeap[in, alloc] == true;
free requires dtype(in) == Native$TransientLink;
// rule info
free requires $linkHeap[in, TransientLink#rule]==_RA2A;  
free requires Map#Domain($linkHeap[in, TransientLink#source])[_att];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_att]) <: ER$ERAttribute;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_att] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], alloc);
free requires Map#Domain($linkHeap[in, TransientLink#source])[_rs];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_rs]) <: ER$Relship;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_rs] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rs], alloc);

free requires Map#Domain($linkHeap[in, TransientLink#target])[_t];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t]) <: REL$RELAttribute;
free requires Map#Elements($linkHeap[in, TransientLink#target])[_t] != null;
free requires read($tarHeap, Map#Elements($linkHeap[in, TransientLink#target])[_t], alloc);

// Correspondence I/O
free requires getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rs])) == Map#Elements($linkHeap[in, TransientLink#target])[_t];
// Guard
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ER$ERAttribute.relship) == Map#Elements($linkHeap[in, TransientLink#source])[_rs] ;
// modifies
modifies $tarHeap;
// Rule outcome

ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rs])), REL$RELAttribute.name) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ER$ERAttribute.name);
ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rs])), REL$RELAttribute.isKey) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ER$ERAttribute.isKey);
ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rs])), REL$RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_rs]));


// Frame 
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 2 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: ER$Relship && ( dtype($o) <: REL$RELAttribute && ($f == REL$RELAttribute.name || $f == REL$RELAttribute.isKey || $f == REL$RELAttribute.relation))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rs])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );
// Preserving
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);

implementation RA2A_apply (in: ref) returns ()
{

var stk: Seq BoxType;
var $newCol: ref;
var t: ref;	//slot: 4
var att: ref;	//slot: 2
var rs: ref;	//slot: 3
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _att);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, att := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _rs);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, rs := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _t);
call stk := NTransientLink#getTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, t := OpCode#Store(stk);
call stk := OpCode#Load(stk, t);
call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, att);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ER$ERAttribute.name)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),REL$RELAttribute.name,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, att);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ER$ERAttribute.isKey)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): bool);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),REL$RELAttribute.isKey,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, rs);
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),REL$RELAttribute.relation,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Pop(stk);

}


// properties of each link of e2r rule
function RA2A_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) <: ER$Relship ==> 
		read($srcHeap, att, ER$ERAttribute.relship) == rs ==>
			(exists l:ref :: l!=null &&
				Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_att] == att  && Map#Elements(read($linkHeap, l, TransientLink#source))[_rs] == rs ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t] != null 
		 && read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t], alloc)
		 && getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t]
		)
}