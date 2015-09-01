/*
rule RA2AK { from att : ER!ERAttribute, rse : ER!RelshipEnd 
	           ( att.entity = rse.entity and att.isKey = true )
	to   t : REL!RELAttribute 
	         ( name <- att.name, isKey <- att.isKey, relation <- rse.relship )}

*/



procedure RA2AK_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall att,rse: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rse!=null && read($srcHeap, rse, alloc) && dtype(rse) <: ER$RelshipEnd 
 ==>
 read($srcHeap, att, ER$ERAttribute.entity) == read($srcHeap, rse, ER$RelshipEnd.entity) && read($srcHeap, att, ER$ERAttribute.isKey) == true  ==>
getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), alloc)
&& dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse))) <: REL$RELAttribute);
  modifies $tarHeap;
// Rule outcome


  ensures (forall att,rse: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rse!=null && read($srcHeap, rse, alloc) && dtype(rse) <: ER$RelshipEnd 
 ==>
 read($srcHeap, att, ER$ERAttribute.entity) == read($srcHeap, rse, ER$RelshipEnd.entity) && read($srcHeap, att, ER$ERAttribute.isKey) == true  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), REL$RELAttribute.name) == read($srcHeap, att, ER$ERAttribute.name));
  ensures (forall att,rse: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rse!=null && read($srcHeap, rse, alloc) && dtype(rse) <: ER$RelshipEnd 
 ==>
 read($srcHeap, att, ER$ERAttribute.entity) == read($srcHeap, rse, ER$RelshipEnd.entity) && read($srcHeap, att, ER$ERAttribute.isKey) == true  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), REL$RELAttribute.isKey) == read($srcHeap, att, ER$ERAttribute.isKey));
  ensures (forall att,rse: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rse!=null && read($srcHeap, rse, alloc) && dtype(rse) <: ER$RelshipEnd 
 ==>
 read($srcHeap, att, ER$ERAttribute.entity) == read($srcHeap, rse, ER$RelshipEnd.entity) && read($srcHeap, att, ER$ERAttribute.isKey) == true  ==>
read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), REL$RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(read($srcHeap, rse, ER$RelshipEnd.relship))));


// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 2 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: ER$RelshipEnd && ( dtype($o) <: REL$RELAttribute && ($f == REL$RELAttribute.name || $f == REL$RELAttribute.isKey || $f == REL$RELAttribute.relation))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);

implementation RA2AK_applyAllTest()
{

	var $i : int;
	var link : ref;
	var links: Seq ref;
	

	links := NTransientLinkSet#getLinksByRule($linkHeap, _RA2AK);
	assume RA2AK_links($srcHeap,$linkHeap,$tarHeap,links);

	$i:=0;

		
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rse])), REL$RELAttribute.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att], ER$ERAttribute.name]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rse])), REL$RELAttribute.isKey) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att], ER$ERAttribute.isKey]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rse])), REL$RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(read($srcHeap,Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rse],ER$RelshipEnd.relship))));
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 2 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: ER$RelshipEnd && ( dtype($o) <: REL$RELAttribute && ($f == REL$RELAttribute.name || $f == REL$RELAttribute.isKey || $f == REL$RELAttribute.relation))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
		
	{
		link := Seq#Index(links, $i);			
		call RA2AK_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}



procedure RA2AK_apply(in: ref) returns();
free requires surj_tar_model($srcHeap, $tarHeap);
//free requires isValidSrc($srcHeap);
//free requires isInstTar($tarHeap);
// link info
free requires $linkHeap[in, alloc] == true;
free requires dtype(in) == Native$TransientLink;
// rule info
free requires $linkHeap[in, TransientLink#rule]==_RA2AK;  
free requires Map#Domain($linkHeap[in, TransientLink#source])[_att];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_att]) <: ER$ERAttribute;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_att] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], alloc);
free requires Map#Domain($linkHeap[in, TransientLink#source])[_rse];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_rse]) <: ER$RelshipEnd;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_rse] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rse], alloc);

free requires Map#Domain($linkHeap[in, TransientLink#target])[_t];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t]) <: REL$RELAttribute;
free requires Map#Elements($linkHeap[in, TransientLink#target])[_t] != null;
free requires read($tarHeap, Map#Elements($linkHeap[in, TransientLink#target])[_t], alloc);

// Correspondence I/O
free requires getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rse])) == Map#Elements($linkHeap[in, TransientLink#target])[_t];
// Guard
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ER$ERAttribute.entity) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rse], ER$RelshipEnd.entity) && read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ER$ERAttribute.isKey) == true ;

free requires dtype(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rse], ER$RelshipEnd.relship)) != class._System.array;

// modifies
modifies $tarHeap;
// Rule outcome

ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rse])), REL$RELAttribute.name) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ER$ERAttribute.name);
ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rse])), REL$RELAttribute.isKey) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ER$ERAttribute.isKey);
ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rse])), REL$RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_rse], ER$RelshipEnd.relship)));


// Frame 
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 2 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: ER$RelshipEnd && ( dtype($o) <: REL$RELAttribute && ($f == REL$RELAttribute.name || $f == REL$RELAttribute.isKey || $f == REL$RELAttribute.relation))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]),Map#Elements($linkHeap[in, TransientLink#source])[_rse])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );
// Preserving
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);

implementation RA2AK_apply (in: ref) returns ()
{

var stk: Seq BoxType;
var $newCol: ref;
var t: ref;	//slot: 4
var att: ref;	//slot: 2
var rse: ref;	//slot: 3
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _att);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, att := OpCode#Store(stk);
call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _rse);
call stk := NTransientLink#getSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, rse := OpCode#Store(stk);
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
call stk := OpCode#Load(stk, rse);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ER$RelshipEnd.relship)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),REL$RELAttribute.relation,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Pop(stk);

}


function RA2AK_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall att,rse: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) <: ER$ERAttribute 
 && rse!=null && read($srcHeap, rse, alloc) && dtype(rse) <: ER$RelshipEnd ==> 
		read($srcHeap, att, ER$ERAttribute.entity) == read($srcHeap,rse, ER$RelshipEnd.entity) && read($srcHeap,att,ER$ERAttribute.isKey) ==>
			(exists l:ref :: l!=null &&
				Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_att] == att  && Map#Elements(read($linkHeap, l, TransientLink#source))[_rse] == rse ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t] != null 
		 && read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t], alloc)
		 && getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rse])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t]
		)
}