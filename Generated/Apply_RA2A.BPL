/*
rule RA2A { from att : ER!ERAttribute, rs  : ER!Relship ( att.relship = rs )
	        to t : REL!RELAttribute
			       ( name <- att.name, isKey <- att.isKey, relation <- rs ) }

*/
// properties of each link of e2r rule
function RA2A_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
		read($srcHeap, att, ERAttribute.relship) == rs ==>
			(exists l:ref :: l!=null &&
				Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_att] == att  && Map#Elements(read($linkHeap, l, TransientLink#source))[_rs] == rs ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t] != null 
		 && read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t], alloc)
		 && getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t]
		)
}



procedure RA2A_applys(links: Seq ref)
requires $IsGoodHeap($tarHeap);
requires links == NTransientLinkSet#getLinksByRule($linkHeap, _RA2A);
requires RA2A_links($srcHeap,$linkHeap,$tarHeap,links);
requires surj_tar_model($srcHeap, $tarHeap);
requires (forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
		read($srcHeap, att, ERAttribute.relship) == rs ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), alloc) 
	 && getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)) != null 
	 && dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs))) == REL$Relation	);	// troublesome
modifies $tarHeap;
ensures (forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
		read($srcHeap, att, ERAttribute.relship) == rs ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), RELAttribute.name) == read($srcHeap, att, ERAttribute.name));
ensures (forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
		read($srcHeap, att, ERAttribute.relship) == rs ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), RELAttribute.isKey) == read($srcHeap, att, ERAttribute.isKey));
ensures (forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
		read($srcHeap, att, ERAttribute.relship) == rs ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(rs)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(  dtype($o) == REL$RELAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Relship 
		&& ($f == RELAttribute.name || $f == RELAttribute.isKey || $f == RELAttribute.relation)) 
	 || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);
{

	var $i : int;
	var link : ref;

	
	$i:=0;

		
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])), RELAttribute.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att], ERAttribute.name]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])), RELAttribute.isKey) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att], ERAttribute.isKey]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_att]), Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs])), RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_rs]))
		);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(  dtype($o) == REL$RELAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Relship 
		&& ($f == RELAttribute.name || $f == RELAttribute.isKey || $f == RELAttribute.relation)) 
	 || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
		
	{
		link := Seq#Index(links, $i);			
		call RA2A_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}


procedure RA2A_apply (in: ref) returns ()
    free requires surj_tar_model($srcHeap, $tarHeap);
  free requires $linkHeap[in, TransientLink#rule]==_RA2A;  
  free requires $linkHeap[in, alloc] == true;
  free requires dtype(in) == Native$TransientLink;
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_att];
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_rs];
  free requires Map#Domain($linkHeap[in, TransientLink#target])[_t];
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_att]) == ER$ERAttribute;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_att] != null;
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_rs]) == ER$Relship;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_rs] != null;
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t]) == REL$RELAttribute;
  free requires Map#Elements($linkHeap[in, TransientLink#target])[_t] != null;
  free requires getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]), Map#Elements($linkHeap[in, TransientLink#source])[_rs])) == Map#Elements($linkHeap[in, TransientLink#target])[_t];
  free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_att], ERAttribute.relship) == Map#Elements($linkHeap[in, TransientLink#source])[_rs];
  modifies $tarHeap;
  ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]), Map#Elements($linkHeap[in, TransientLink#source])[_rs])), RELAttribute.name) == read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_att],ERAttribute.name);
  ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]), Map#Elements($linkHeap[in, TransientLink#source])[_rs])), RELAttribute.isKey) == read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_att],ERAttribute.isKey);
  ensures read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]), Map#Elements($linkHeap[in, TransientLink#source])[_rs])), RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_rs]));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(  dtype($o) == REL$RELAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Relship 
		&& ($f == RELAttribute.name || $f == RELAttribute.isKey || $f == RELAttribute.relation)) 
	 || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Build(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_att]), Map#Elements($linkHeap[in, TransientLink#source])[_rs])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
{

var stk: Seq BoxType;
var $i: int;
var t: ref;	//slot: 4
var att: ref;	//slot: 2
var rs: ref;	//slot: 3
var self: ref;	//slot: 0
var link: ref;	//slot: 1
stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _att);
call stk := NTransientLink#getSourceElement(
				stk,
				$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
				$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, att := OpCode#Store(stk);

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _rs);
call stk := NTransientLink#getSourceElement(
				stk,
				$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
				$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, rs := OpCode#Store(stk);

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _t);
call stk := NTransientLink#getTargetElement(
				stk,
				$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
				$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk, t := OpCode#Store(stk);

call stk := OpCode#Load(stk, t);
call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, att);

// get
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$name): Field (String)]));

call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);

// set
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
				FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$name): Field (String), 
				$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);


call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, att);

// get
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$isKey): Field (bool)]));

call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): bool);

// set
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
				FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$isKey): Field (bool), 
				$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);





call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, rs);

call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assume $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref == getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_rs]));


// set
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
				FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$relation): Field (ref), 
				$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);




call stk := OpCode#Pop(stk);


}