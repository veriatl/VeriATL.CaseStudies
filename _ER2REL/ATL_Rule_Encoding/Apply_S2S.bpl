/*
rule S2S { 
  from s : ER!ERSchema to t : REL!RELSchema ( name  <- s.name, relations <-s.entities, relations <-s.relships)}
*/

procedure S2S_applyAllTest() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$ERSchema 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(s)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(s))) <: REL$RELSchema);
  modifies $tarHeap;
// Rule outcome


  ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$ERSchema 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$RELSchema.name) == read($srcHeap, s, ER$ERSchema.name));
  ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$ERSchema 
 ==>
 true  ==>
dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$RELSchema.relations)) == class._System.array
&&       read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$RELSchema.relations) != null
&&       read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$RELSchema.relations), alloc)
&&       (_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$RELSchema.relations)) == _System.array.Length(read($srcHeap, s, ER$ERSchema.entities)) + _System.array.Length(read($srcHeap, s, ER$ERSchema.relships)))
&&       ( forall __j: int :: 0<=__j && __j<_System.array.Length(read($srcHeap, s, ER$ERSchema.entities)) ==> $Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$RELSchema.relations), IndexField(__j))): ref == getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, s, ER$ERSchema.entities), IndexField(__j))): ref) ))
&&       ( forall __j: int :: 0<=__j && __j<_System.array.Length(read($srcHeap, s, ER$ERSchema.relships)) ==> $Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), REL$RELSchema.relations), IndexField(__j+_System.array.Length(read($srcHeap, s, ER$ERSchema.entities))))): ref == getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, s, ER$ERSchema.relships), IndexField(__j))): ref) )));

  ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$ERSchema 
 ==>
 true  ==>
 true );



// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	  || (dtype($o) == class._System.array));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERSchema && ( dtype($o) <: REL$RELSchema && ($f == REL$RELSchema.name || $f == REL$RELSchema.relations || $f == REL$RELSchema.relations))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);
		 
implementation S2S_applyAllTest()
{

	var $i : int;
	var link : ref;
	var links: Seq ref;
	

	links := NTransientLinkSet#getLinksByRule($linkHeap, _S2S);
	assume S2S_links($srcHeap,$linkHeap,$tarHeap,links);
	
	$i:=0;

		
	
	while($i < Seq#Length(links))
		invariant $i <= Seq#Length(links);
		invariant surj_tar_model($srcHeap, $tarHeap);
		// t.name <- s.name
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$RELSchema.name) == $srcHeap[Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.name]
		);
		// dtype(t.relations) = class._System.array
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$RELSchema.relations)) == class._System.array
		);
		// length(t.relations) = length(s.entities)+length(s.relships)
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$RELSchema.relations)) == 
			_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.relships)) 
			+ _System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.entities))
		);
		// t.relations != null && t.relations.alloc
		invariant (forall i: int:: 0<=i &&i <$i ==>			
			read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$RELSchema.relations) != null && read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$RELSchema.relations), alloc)
		);
		// t.relations[j] == s.entities[j]
		invariant (forall i: int:: 0<=i &&i <$i ==>	
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.entities))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$RELSchema.relations), IndexField(j))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.entities), IndexField(j))): ref) )
			));
		// t.relations[j+len(s.entities)] == s.relships[j]
		invariant (forall i: int:: 0<=i &&i <$i ==>	
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.relships))  ==>
				$Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])), REL$RELSchema.relations), IndexField(j+_System.array.Length(read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.entities))))): ref ==
				getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s], ER$ERSchema.relships), IndexField(j))): ref) )
			));	
		// frame
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) == REL$RELSchema && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERSchema && ($f == REL$RELSchema.name || $f == REL$RELSchema.relations)) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
		invariant (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
		 || (dtype($o) == class._System.array));
	{
		link := Seq#Index(links, $i);		
		call S2S_apply(link);
		$i := $i+1;
	}
	
	assume $HeapSucc(old($tarHeap), $tarHeap);
}
			



procedure S2S_apply(in: ref) returns();
free requires surj_tar_model($srcHeap, $tarHeap);
//free requires isValidSrc($srcHeap);
//free requires isInstTar($tarHeap);
// link info
free requires $linkHeap[in, alloc] == true;
free requires dtype(in) == Native$TransientLink;
// rule info
free requires $linkHeap[in, TransientLink#rule]==_S2S;  
free requires Map#Domain($linkHeap[in, TransientLink#source])[_s];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#source])[_s]) <: ER$ERSchema;
free requires Map#Elements($linkHeap[in, TransientLink#source])[_s] != null;
free requires read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], alloc);

free requires Map#Domain($linkHeap[in, TransientLink#target])[_t];
free requires dtype(Map#Elements($linkHeap[in, TransientLink#target])[_t]) <: REL$RELSchema;
free requires Map#Elements($linkHeap[in, TransientLink#target])[_t] != null;
free requires read($tarHeap, Map#Elements($linkHeap[in, TransientLink#target])[_t], alloc);
// isValidSrc
free requires dtype(read($srcHeap,  Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.entities)) == class._System.array;
free requires dtype(read($srcHeap,  Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.relships)) == class._System.array;
// isInstTar
free requires Seq#FromArray($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.relations)) == Seq#Empty();
// Correspondence I/O
free requires getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])) == Map#Elements($linkHeap[in, TransientLink#target])[_t];
// Guard
free requires true ;
// modifies
modifies $tarHeap;
// Rule outcome

ensures read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.name) == read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.name);
ensures dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.relations)) == class._System.array
&&       read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.relations) != null
&&       read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.relations), alloc)
&&       (_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.relations)) == _System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.entities)) + _System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.relships)))
&&       ( forall __j: int :: 0<=__j && __j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.entities)) ==> $Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.relations), IndexField(__j))): ref == getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.entities), IndexField(__j))): ref) ))
&&       ( forall __j: int :: 0<=__j && __j<_System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.relships)) ==> $Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])), REL$RELSchema.relations), IndexField(__j+_System.array.Length(read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.entities))))): ref == getTarsBySrcs(Seq#Singleton( $Unbox(read($srcHeap, read($srcHeap, Map#Elements($linkHeap[in, TransientLink#source])[_s], ER$ERSchema.relships), IndexField(__j))): ref) ));

ensures  true ;



// Frame 
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)) 
	  || (dtype($o) == class._System.array));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$ERSchema && ( dtype($o) <: REL$RELSchema && ($f == REL$RELSchema.name || $f == REL$RELSchema.relations || $f == REL$RELSchema.relations))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) && $o != getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[in, TransientLink#source])[_s])) ==> 
	(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
  );
// Preserving
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);


implementation S2S_apply (in: ref) returns ()
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
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ER$ERSchema.name)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),REL$RELSchema.name,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, s);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ER$ERSchema.entities)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
havoc $newCol;
assume dtype($newCol) == class._System.array;
assume $newCol != null && read($tarHeap, $newCol, alloc);
assume Seq#FromArray($tarHeap,$newCol) == Seq#Append(Seq#FromArray($tarHeap, read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), REL$RELSchema.relations)), Seq#FromArray($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1))));
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), REL$RELSchema.relations, $newCol);
assume $IsGoodHeap($tarHeap);
stk := Seq#Take(stk, Seq#Length(stk)-2);

call stk := OpCode#Dup(stk);
call stk := OpCode#GetASM(stk);
call stk := OpCode#Load(stk, s);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ER$ERSchema.relships)));
call stk := ASM#Resolve(stk, $srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref);
assert Seq#Length(stk) >= 2;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) != null;
assert read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), alloc);
havoc $newCol;
assume dtype($newCol) == class._System.array;
assume $newCol != null && read($tarHeap, $newCol, alloc);
assume Seq#FromArray($tarHeap,$newCol) == Seq#Append(Seq#FromArray($tarHeap, read($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), REL$RELSchema.relations)), Seq#FromArray($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1))));
$tarHeap := update($tarHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)), REL$RELSchema.relations, $newCol);
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
(forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) <: ER$ERSchema ==> 
		(exists l:ref :: l!=null &&
			Seq#Contains(links,l) && Map#Elements(read($linkHeap, l, TransientLink#source))[_s] == r ))
&&
(forall i: int:: 0<=i &&i <Seq#Length(links) ==>			
			Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t] != null &&
			read($tarHeap, Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t], alloc) && getTarsBySrcs(Seq#Singleton(Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#source])[_s])) == Map#Elements($linkHeap[Seq#Index(links,i), TransientLink#target])[_t]
		)

}