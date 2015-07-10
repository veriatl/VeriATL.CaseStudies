

procedure driver()
  requires valid_src_model($srcHeap);
  // unique schema names
  requires (forall $i1, $i2: ref :: $i1!=$i2 && $i1!=null && read($srcHeap, $i1, alloc) && dtype($i1) == ER$ERSchema
				&& $i2!=null && read($srcHeap, $i2, alloc) && dtype($i2) <: ER$ERSchema ==>
				read($srcHeap, $i1, ERSchema.name) != read($srcHeap, $i2, ERSchema.name));
  // entity names are unique in schema
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, ERSchema.entities))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(j1))), Entity.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(j2))), Entity.name)
			));
  // relship names are unique in schema
  requires (forall r: ref :: { dtype(r) <: ER$ERSchema } r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, ERSchema.relships))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j1))), Relship.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j2))), Relship.name)
			));
  // disjoint entity and relship names
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall i: int :: 0<=i && i<_System.array.Length(read($srcHeap, r, ERSchema.entities))  ==>
			 ( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, r, ERSchema.relships))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(i))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(i))), Entity.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j))), Relship.name)
			)));
  // attr names are unique in entity
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, Entity.attrs))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, Entity.attrs), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, Entity.attrs), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, Entity.attrs), IndexField(j1))), ERAttribute.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, Entity.attrs), IndexField(j2))), ERAttribute.name)
			));
  // attr names are unique in relship
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Relship ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, Relship.attrs))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, Relship.attrs), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, Relship.attrs), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, Relship.attrs), IndexField(j1))), ERAttribute.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, Relship.attrs), IndexField(j2))), ERAttribute.name)
			));
  // entities have a key
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
			!( forall i: int :: 0<=i && i<_System.array.Length(read($srcHeap, r, Entity.attrs))  ==>
				 !read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, Entity.attrs), IndexField(i))), ERAttribute.isKey) 
			));
  modifies $tarHeap,$linkHeap;
	// relation names are unique in schema
  ensures (forall $o: ref :: {read($tarHeap, $o, alloc)} $o!=null && read($tarHeap, $o, alloc) && dtype($o) == REL$RELSchema ==> 
			( forall j1,j2: int :: {$Unbox(read($tarHeap, read($tarHeap, $o, RELSchema.relations), IndexField(j1))): ref, $Unbox(read($tarHeap, read($tarHeap, $o, RELSchema.relations), IndexField(j2))): ref} 
			   0<=j1 && j1<j2 && j2<_System.array.Length(read($tarHeap, $o, RELSchema.relations))  ==>
				$Unbox(read($tarHeap, read($tarHeap, $o, RELSchema.relations), IndexField(j1))): ref != $Unbox(read($tarHeap, read($tarHeap, $o, RELSchema.relations), IndexField(j2))): ref ==>
					read($tarHeap, $Unbox(read($tarHeap, read($tarHeap, $o, RELSchema.relations), IndexField(j1))), Relation.name) != read($tarHeap, $Unbox(read($tarHeap, read($tarHeap, $o, RELSchema.relations), IndexField(j2))), Relation.name)	
			));	
{
	
	var hp: HeapType  where $IsGoodHeap(hp);


	

	call init_tar_model(); 
	

	call S2S_match();
	call E2R_match();
	call R2R_match();
	call EA2A_match();
	call RA2A_match();
	call RA2AK_match();



	call S2S_applys();
	call E2R_applys();
	call R2R_applys();
	call EA2A_applys();
	call RA2A_applys();
	call RA2AK_applys();
	
	
// helper: to better explain the layout of RELSchema.relations
assert (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j: int :: _System.array.Length(read($srcHeap, r, ERSchema.entities))<=j && j<_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations))  ==>
				read($tarHeap, $Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations), IndexField(j))), Relation.name) == read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j-_System.array.Length(read($srcHeap, r, ERSchema.entities))))), Relship.name)
			));	
			


/*
// sanity check, redundant
assert (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j: int :: 0<=j && j<_System.array.Length(read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations))  ==>
				read($tarHeap, $Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations), IndexField(j))), Relation.name) == read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.entities), IndexField(j))), Entity.name)
			));	
assert (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, r, ERSchema.relships))  ==>
				read($tarHeap, $Unbox(read($tarHeap, read($tarHeap, getTarsBySrcs(Seq#Singleton(r)), RELSchema.relations), IndexField(j+_System.array.Length(read($srcHeap, r, ERSchema.entities))))), Relation.name) == read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ERSchema.relships), IndexField(j))), Relship.name)
			));	
*/

	
}
