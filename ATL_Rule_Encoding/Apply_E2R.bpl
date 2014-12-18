/*
rule E2R { from s : ER!Entity 
		   to t : REL!Relation ( name  <- s.name, attrs <- s.attrs) }

*/

procedure E2R_applys();
requires surj_tar_model($srcHeap, $tarHeap);
requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==>
		read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), alloc) 
	 && getTarsBySrcs(Seq#Singleton(r)) != null 
	 && dtype(getTarsBySrcs(Seq#Singleton(r))) == REL$Relation	);
modifies $tarHeap;
// t.name <- s.name
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
		read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), Relation.name) == read($srcHeap, r, Entity.name));
// dtype(t.attrs) = class._System.array
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
	dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), Relation.attrs)) == class._System.array
);
// t.attrs != null && t.attrs.alloc
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
	read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), Relation.attrs) != null 
 && read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), Relation.attrs), alloc)
);
// length(t.attrs) = length(s.attrs)
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
		_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), Relation.attrs)) 
	 == _System.array.Length(read($srcHeap, r, Entity.attrs))
);
// t.attrs[j] == s.attrs[j]
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, r, Entity.attrs))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), Relation.attrs), IndexField(j))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, r, Entity.attrs), IndexField(j))): ref) )
			));
// frame property
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$Entity && ($f == Relation.name || $f == Relation.attrs)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);

implementation E2R_applys()
{

	var $i : int;
	var link : ref;
	var links: Seq ref;
	
	links := NTransientLinkSet#getLinksByRule($linkHeap, _E2R);
	assume E2R_links($srcHeap,$linkHeap,$tarHeap,links);
	
	$i:=0;

		
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
			$o != null && read(old($tarHeap), $o, alloc) ==>
				((dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$Entity && ($f == Relation.name || $f == Relation.attrs)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), Relation.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], Entity.name]
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), Relation.attrs)) == class._System.array
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), Relation.attrs)) == _System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], Entity.attrs))
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), Relation.attrs) != null && read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), Relation.attrs), alloc)
		);
		invariant (forall i: int:: 0<=i &&i <$i ==>	
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], Entity.attrs))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), Relation.attrs), IndexField(j))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], Entity.attrs), IndexField(j))): ref) )
			));
		
	{
		link := Seq#Index(links, $i);		
		call E2R_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}



procedure E2R_apply (in: ref) returns ()
  free requires surj_tar_model($srcHeap, $tarHeap);
  free requires $linkHeap[in, TransientLink#rule]==_E2R;  
  free requires $linkHeap[in, alloc] == true;
  free requires dtype(in) == Native$TransientLink;
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_s];
  free requires Map#Domain($linkHeap[in, TransientLink#target])[_t];
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_s]) == ER$Entity;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_s] != null;
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t]) == REL$Relation;
  free requires Map#Elements($linkHeap[in, TransientLink#target])[_t] != null;
  free requires getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])) == Map#Elements($linkHeap[in, TransientLink#target])[_t];
  free requires Seq#FromArray($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), Relation.attrs)) == Seq#Empty();	
  modifies $tarHeap;
  ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), Relation.name) == read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_s],Entity.name);
  ensures dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), Relation.attrs)) == class._System.array;
  // attrs != null and allocated
  ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), Relation.attrs) != null && read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), Relation.attrs), alloc)
  ;
  // len(t.attrs) = len(s.attrs)
  ensures _System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), Relation.attrs))
== _System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], Entity.attrs));
  // t.attrs[j] == s.attrs[j]
  ensures ( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], Entity.attrs))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), Relation.attrs), IndexField(j))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], Entity.attrs), IndexField(j))): ref) )
			);
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$Entity && ($f == Relation.name || $f == Relation.attrs)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );	
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
{

var stk: Seq BoxType;
var $i: int;
var t: ref;	//slot: 3
var s: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
var $resolved: ref;	
var $newCol: ref;	

stk := OpCode#Aux#InitStk();
link := in;

call stk := OpCode#Load(stk, link);
call stk := OpCode#Push(stk, _s);
call stk := NTransientLink#getSourceElement(
				stk,
				$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
				$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
				
call stk, s := OpCode#Store(stk);
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
call stk := OpCode#Load(stk, s);

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
call stk := OpCode#Load(stk, s);


// get
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$attrs): Field (ref)]));


call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);

havoc $resolved;
assume dtype($resolved) == class._System.array;
assume _System.array.Length(read($srcHeap, s, Entity.attrs)) == _System.array.Length($resolved);
assume ( forall j: int :: 0<=j && j<_System.array.Length($resolved)  ==>
$Unbox(read($tarHeap, $resolved, IndexField(j))):ref != null
&& read($tarHeap, $Unbox(read($tarHeap, $resolved, IndexField(j))):ref, alloc)
&& dtype($Unbox(read($tarHeap, $resolved, IndexField(j))):ref) == REL$Relation
&& $Unbox(read($tarHeap, $resolved, IndexField(j))):ref == getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, s, Entity.attrs), IndexField(j))): ref) )
);

// union
havoc $newCol;
assume dtype($newCol) == class._System.array;
assume $newCol != null && read($tarHeap, $newCol, alloc);
assume Seq#FromArray($tarHeap,$newCol) == Seq#Append(Seq#FromArray($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$attrs): Field (ref))), Seq#FromArray($tarHeap,$resolved));

// set
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
				FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$attrs): Field (ref), 
				$newCol
				);
				
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);	




call stk := OpCode#Pop(stk);


}

// properties of each link of e2r rule
function E2R_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_s] == r ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t], alloc) && getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t]
		)

}