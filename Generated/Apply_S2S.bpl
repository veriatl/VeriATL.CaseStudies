/*
rule S2S { 
  from s : ER!ERSchema to t : REL!RELSchema ( name  <- s.name, relations <-s.entities, relations <-s.relships)}
*/




procedure S2S_applys(links: Seq ref)
requires $IsGoodHeap($tarHeap);
requires links == NTransientLinkSet#getLinksByRule($linkHeap, _S2S);
requires S2S_links($srcHeap,$linkHeap,$tarHeap,links);
requires surj_tar_model($srcHeap, $tarHeap);
requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==>
		read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), alloc) 
	 && getTarsBySrcs(Seq#Singleton(r)) != null 
	 && dtype(getTarsBySrcs(Seq#Singleton(r))) == REL$RELSchema	);
modifies $tarHeap;
// t.name <- s.name
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
		read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.name) == read($srcHeap, r, ERSchema.name));
// dtype(t.relations) = class._System.array
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
	dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations)) == class._System.array
);
// t.relations != null && t.relations.alloc
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
	read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations) != null 
 && read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations), alloc)
);
// length(t.relations) = length(s.entities)+length(s.relships)
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
		_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations)) 
	 == _System.array.Length(read($srcHeap, r, ERSchema.entities))+_System.array.Length(read($srcHeap, r, ERSchema.relships))
);
// t.relations[j] == s.entities[j]
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, r, ERSchema.entities))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations), IndexField(j))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(j))): ref) )
			));
// t.relations[j+len(s.entities)] == s.relships[j]
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, r, ERSchema.relships))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations), IndexField(j+_System.array.Length(read($srcHeap, r, ERSchema.entities))))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j))): ref) )
			));
// frame
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		( (dtype($o) == REL$RELSchema && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERSchema && ($f == RELSchema.name || $f == RELSchema.relations)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);
{

	var $i : int;
	var link : ref;

	
	$i:=0;

		
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		// t.name <- s.name
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), RELSchema.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.name]
		);
		// dtype(t.relations) = class._System.array
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), RELSchema.relations)) == class._System.array
		);
		// length(t.relations) = length(s.entities)+length(s.relships)
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), RELSchema.relations)) == 
			_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.relships)) 
			+ _System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.entities))
		);
		// t.relations != null && t.relations.alloc
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), RELSchema.relations) != null && read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), RELSchema.relations), alloc)
		);
		// t.relations[j] == s.entities[j]
		invariant (forall i: int:: 0<=i &&i <$i ==>	
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.entities))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), RELSchema.relations), IndexField(j))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.entities), IndexField(j))): ref) )
			));
		// t.relations[j+len(s.entities)] == s.relships[j]
		invariant (forall i: int:: 0<=i &&i <$i ==>	
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.relships))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), RELSchema.relations), IndexField(j+_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.entities))))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ERSchema.relships), IndexField(j))): ref) )
			));	
		// frame
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) == REL$RELSchema && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERSchema && ($f == RELSchema.name || $f == RELSchema.relations)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
	{
		link := Seq#Index(links, $i);		
		call S2S_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}
			
procedure S2S_apply(in: ref) returns()
  free requires surj_tar_model($srcHeap, $tarHeap);
  free requires $linkHeap[in, TransientLink#rule]==_S2S;  
  free requires $linkHeap[in, alloc] == true;
  free requires dtype(in) == Native$TransientLink;
  free requires Map#Domain($linkHeap[in, TransientLink#source])[_s];
  free requires Map#Domain($linkHeap[in, TransientLink#target])[_t];
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_s]) == ER$ERSchema;
  free requires Map#Elements($linkHeap[in, TransientLink#source])[_s] != null;
  free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t]) == REL$RELSchema;
  free requires Map#Elements($linkHeap[in, TransientLink#target])[_t] != null;
  free requires getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])) == Map#Elements($linkHeap[in, TransientLink#target])[_t];
  free requires Seq#FromArray($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations)) == Seq#Empty();
  modifies $tarHeap;
  // name <-
  ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.name) == read($srcHeap,Map#Elements($linkHeap[in, TransientLink#source])[_s],ERSchema.name);
  // relations is a collection
  ensures dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations)) == class._System.array;
  // relations != null and allocated
  ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations) != null && read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations), alloc)
  ;
  // len(relations) = len(entities) + len(relships)
  ensures _System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations))
== _System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ERSchema.relships)) + _System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ERSchema.entities));
  // t.relations[j] == s.entities[j]
  ensures ( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ERSchema.entities))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations), IndexField(j))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ERSchema.entities), IndexField(j))): ref) )
			);
  // t.relations[j+len(s.entities)] == s.relships[j]
  ensures ( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ERSchema.relships))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations), IndexField(j+_System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ERSchema.entities))))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ERSchema.relships), IndexField(j))): ref) )
			);
  
  // frame properties
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) == REL$RELSchema && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERSchema && ($f == RELSchema.name || $f == RELSchema.relations)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
  // frame properties
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
var $resolved: ref;	//slot: 1
var $newCol: ref;	//slot: 1



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
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$entities): Field (ref)]));


call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);

// $Unbox(Seq#Index(stk, Seq#Length(stk)-1))
havoc $resolved;
assume dtype($resolved) == class._System.array;
assume _System.array.Length(read($srcHeap, s, ERSchema.entities)) == _System.array.Length($resolved);
assume ( forall j: int :: 0<=j && j<_System.array.Length($resolved)  ==>
$Unbox(read($tarHeap, $resolved, IndexField(j))):ref != null
&& read($tarHeap, $Unbox(read($tarHeap, $resolved, IndexField(j))):ref, alloc)
&& dtype($Unbox(read($tarHeap, $resolved, IndexField(j))):ref) == REL$Relation
&& $Unbox(read($tarHeap, $resolved, IndexField(j))):ref == getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, s, ERSchema.entities), IndexField(j))): ref) )
);

// union
havoc $newCol;
assume dtype($newCol) == class._System.array;
assume $newCol != null && read($tarHeap, $newCol, alloc);
assume Seq#FromArray($tarHeap,$newCol) == Seq#Append(Seq#FromArray($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations)), Seq#FromArray($tarHeap,$resolved));



// set,
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
				FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$relations): Field (ref), 
				$newCol
				);
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);	




call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, s);


// get
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$relships): Field (ref)]));


call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);

havoc $resolved;
assume dtype($resolved) == class._System.array;
assume _System.array.Length(read($srcHeap, s, ERSchema.relships)) == _System.array.Length($resolved);
assume ( forall j: int :: 0<=j && j<_System.array.Length($resolved)  ==>
$Unbox(read($tarHeap, $resolved, IndexField(j))):ref != null
&& read($tarHeap, $Unbox(read($tarHeap, $resolved, IndexField(j))):ref, alloc)
&& dtype($Unbox(read($tarHeap, $resolved, IndexField(j))):ref) == REL$Relation
&& $Unbox(read($tarHeap, $resolved, IndexField(j))):ref == getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, s, ERSchema.relships), IndexField(j))): ref) )
);

// union
havoc $newCol;
assume dtype($newCol) == class._System.array;
assume $newCol != null && read($tarHeap, $newCol, alloc);
assume Seq#FromArray($tarHeap,$newCol) == Seq#Append(Seq#FromArray($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), RELSchema.relations)), Seq#FromArray($tarHeap,$resolved));

// set
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), 
				FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))), _Field$relations): Field (ref), 
				$newCol
				);
				
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);	



call stk := OpCode#Pop(stk);

}


// properties of each link of e2r rule
function S2S_links(
	$srcHeap:HeapType,
	$linkHeap:HeapType,
	$tarHeap:HeapType,
	links: Seq ref):bool
{
(forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_s] == r ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t], alloc)
		)

}