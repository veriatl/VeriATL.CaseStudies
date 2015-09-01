procedure driver()
  requires valid_src_model($srcHeap);
  // unique schema names
  requires (forall $i1, $i2: ref :: $i1!=$i2 && $i1!=null && read($srcHeap, $i1, alloc) && dtype($i1) == ER$ERSchema
				&& $i2!=null && read($srcHeap, $i2, alloc) && dtype($i2) == ER$ERSchema ==>
				read($srcHeap, $i1, ER$ERSchema.name) != read($srcHeap, $i2, ER$ERSchema.name));
  // entity names are unique in schema
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, ER$ERSchema.entities))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.entities), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.entities), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.entities), IndexField(j1))), ER$Entity.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.entities), IndexField(j2))), ER$Entity.name)
			));
  // relship names are unique in schema
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, ER$ERSchema.relships))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.relships), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.relships), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.relships), IndexField(j1))), ER$Relship.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.relships), IndexField(j2))), ER$Relship.name)
			));
  // disjoint entity and relship names
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$ERSchema ==> 
			( forall i: int :: 0<=i && i<_System.array.Length(read($srcHeap, r, ER$ERSchema.entities))  ==>
			 ( forall j: int :: 0<=j && j<_System.array.Length(read($srcHeap, r, ER$ERSchema.relships))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.entities), IndexField(i))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.relships), IndexField(j))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.entities), IndexField(i))), ER$Entity.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$ERSchema.relships), IndexField(j))), ER$Relship.name)
			)));
  // attr names are unique in entity
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, ER$Entity.attrs))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ER$Entity.attrs), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ER$Entity.attrs), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$Entity.attrs), IndexField(j1))), ER$ERAttribute.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$Entity.attrs), IndexField(j2))), ER$ERAttribute.name)
			));
  // attr names are unique in relship
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Relship ==> 
			( forall j1,j2: int :: 0<=j1 && j1<j2 && j2<_System.array.Length(read($srcHeap, r, ER$Relship.attrs))  ==>
				$Unbox(read($srcHeap, read($srcHeap, r, ER$Relship.attrs), IndexField(j1))): ref != $Unbox(read($srcHeap, read($srcHeap, r, ER$Relship.attrs), IndexField(j2))): ref ==>
				read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$Relship.attrs), IndexField(j1))), ER$ERAttribute.name) != read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$Relship.attrs), IndexField(j2))), ER$ERAttribute.name)
			));
  // entities have a key
  requires (forall r: ref :: r!=null && read($srcHeap, r, alloc) && dtype(r) == ER$Entity ==> 
			!( forall i: int :: 0<=i && i<_System.array.Length(read($srcHeap, r, ER$Entity.attrs))  ==>
				 !read($srcHeap, $Unbox(read($srcHeap, read($srcHeap, r, ER$Entity.attrs), IndexField(i))), ER$ERAttribute.isKey) 
			));
  modifies $tarHeap,$linkHeap;
	// attribute names unique in relation, should not hold!
  ensures (forall $o: ref :: {read($tarHeap, $o, alloc)} $o!=null && read($tarHeap, $o, alloc) && dtype($o) == REL$Relation ==> 
			( forall j1,j2: int :: {$Unbox(read($tarHeap, read($tarHeap, $o, REL$Relation.attrs), IndexField(j1))): ref, $Unbox(read($tarHeap, read($tarHeap, $o, REL$Relation.attrs), IndexField(j2))): ref} 
			   0<=j1 && j1<j2 && j2<_System.array.Length(read($tarHeap, $o, REL$Relation.attrs))  ==>
				$Unbox(read($tarHeap, read($tarHeap, $o, REL$Relation.attrs), IndexField(j1))): ref != $Unbox(read($tarHeap, read($tarHeap, $o, REL$Relation.attrs), IndexField(j2))): ref ==>
					read($tarHeap, $Unbox(read($tarHeap, read($tarHeap, $o, REL$Relation.attrs), IndexField(j1))), REL$RELAttribute.name) != read($tarHeap, $Unbox(read($tarHeap, read($tarHeap, $o, REL$Relation.attrs), IndexField(j2))), REL$RELAttribute.name)	
			));
{
	
	var hp: HeapType  where $IsGoodHeap(hp);


	

	call init_tar_model(); 
	

	call S2S_matchAll();
	call E2R_matchAll();
	call R2R_matchAll();
	call EA2A_matchAll();
	call RA2A_matchAll();
	call RA2AK_matchAll();



	call S2S_applyAll();
	call E2R_applyAll();
	call R2R_applyAll();
	call EA2A_applyAll();
	call RA2A_applyAll();
	call RA2AK_applyAll();


	
}

