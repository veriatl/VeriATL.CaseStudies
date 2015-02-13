// the outcome of init is that: no rule to handle src tuple in ATL spec will return null, or not allocated yet.
procedure init_tar_model();
modifies $tarHeap;
ensures  (forall $o: ref :: $o == null || !read($tarHeap, $o, alloc));


procedure S2S_match();
requires (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$ERSchema ==> 
		getTarsBySrcs(Seq#Singleton(s))==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc));
modifies $tarHeap,$linkHeap;
ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$ERSchema ==> 
		getTarsBySrcs(Seq#Singleton(s))!=null 
		&& read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)
		&& dtype(getTarsBySrcs(Seq#Singleton(s))) == REL$RELSchema
		);
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELSchema && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERSchema && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

procedure E2R_match();
requires (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$Entity ==> 
		getTarsBySrcs(Seq#Singleton(s))==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc));
modifies $tarHeap,$linkHeap;
ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$Entity ==> 
		getTarsBySrcs(Seq#Singleton(s))!=null 
		&& read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)
		&& dtype(getTarsBySrcs(Seq#Singleton(s))) == REL$Relation
		);
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$Entity && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

procedure R2R_match();
requires (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$Relship ==> 
		getTarsBySrcs(Seq#Singleton(s))==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc));
modifies $tarHeap,$linkHeap;
ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$Relship ==> 
		getTarsBySrcs(Seq#Singleton(s))!=null 
		&& read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)
		&& dtype(getTarsBySrcs(Seq#Singleton(s))) == REL$Relation
		);
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$Relship && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

procedure EA2A_match();
requires (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			(forall ent: ref :: ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
				$srcHeap[att, ERAttribute.entity] == ent ==>
				getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent))==null || !read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), alloc)));
modifies $tarHeap,$linkHeap;
ensures (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			 (forall ent: ref :: ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
				$srcHeap[att, ERAttribute.entity] == ent ==>
				getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent))!=null 
				&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), alloc)
				&& dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent))) == REL$RELAttribute
				));
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Entity && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

procedure RA2A_match();
requires (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			(forall rs: ref :: rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
				$srcHeap[att, ERAttribute.relship] == rs ==>
				getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs))==null || !read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), alloc)));
modifies $tarHeap,$linkHeap;
ensures (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			 (forall rs: ref :: rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
				$srcHeap[att, ERAttribute.relship] == rs ==>
				getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs))!=null 
				&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), alloc)
				&& dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs))) == REL$RELAttribute
				));
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Relship && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

procedure RA2AK_match();
requires (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			(forall rse: ref :: rse!=null && read($srcHeap, rse, alloc) && dtype(rse) == ER$RelshipEnd ==> 
				($srcHeap[att, ERAttribute.entity] == $srcHeap[rse, RelshipEnd.entity] && $srcHeap[att, ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse))==null || !read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), alloc)));
modifies $tarHeap,$linkHeap;
ensures (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			 (forall rse: ref :: rse!=null && read($srcHeap, rse, alloc) && dtype(rse) == ER$RelshipEnd ==> 
				($srcHeap[att, ERAttribute.entity] == $srcHeap[rse, RelshipEnd.entity] && $srcHeap[att, ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), alloc)
					&& dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse))) == REL$RELAttribute
					));
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$RelshipEnd && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

procedure S2S_applys();
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
// frame property
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$Entity && $f == Relation.name) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);

procedure R2R_applys();
requires surj_tar_model($srcHeap, $tarHeap);
requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Relship ==>
		read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), alloc) 
	 && getTarsBySrcs(Seq#Singleton(r)) != null 
	 && dtype(getTarsBySrcs(Seq#Singleton(r))) == REL$Relation	);
modifies $tarHeap;
// t.name <- s.name
ensures (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Relship ==> 
		read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), Relation.name) == read($srcHeap, r, Relship.name));
// frame property
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		((dtype($o) == REL$Relation && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$Relship && $f == Relation.name) || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))));
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);


procedure EA2A_applys();
requires surj_tar_model($srcHeap, $tarHeap);
requires (forall att,ent: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
		read($srcHeap, att, ERAttribute.entity) == ent ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), alloc) 
	 && getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)) != null 
	 && dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent))) == REL$RELAttribute	); 
modifies $tarHeap;
ensures (forall att,ent: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
		read($srcHeap, att, ERAttribute.entity) == ent ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), RELAttribute.name) == read($srcHeap, att, ERAttribute.name));
ensures (forall att,ent: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
		read($srcHeap, att, ERAttribute.entity) == ent ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), RELAttribute.isKey) == read($srcHeap, att, ERAttribute.isKey));
ensures (forall att,ent: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
		read($srcHeap, att, ERAttribute.entity) == ent ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), RELAttribute.relation) == getTarsBySrcs(Seq#Singleton(ent)));
ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(  dtype($o) == REL$RELAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Entity 
		&& ($f == RELAttribute.name || $f == RELAttribute.isKey || $f == RELAttribute.relation)) 
	 || (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
ensures $HeapSucc(old($tarHeap), $tarHeap);
ensures surj_tar_model($srcHeap, $tarHeap);

procedure RA2A_applys();
requires surj_tar_model($srcHeap, $tarHeap);
requires (forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
		read($srcHeap, att, ERAttribute.relship) == rs ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), alloc) 
	 && getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)) != null 
	 && dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs))) == REL$RELAttribute	);	
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

procedure RA2AK_applys();
requires surj_tar_model($srcHeap, $tarHeap);
requires (forall att,rs: ref :: 
	att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute 
 && rs!=null && read($srcHeap, rs, alloc) && dtype(rs) == ER$Relship ==> 
		read($srcHeap, att, ERAttribute.relship) == rs ==>
		read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)), alloc) 
	 && getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs)) != null 
	 && dtype(getTarsBySrcs(Seq#Build(Seq#Singleton(att),rs))) == REL$RELAttribute	);	
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