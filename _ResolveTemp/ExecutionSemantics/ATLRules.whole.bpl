// the outcome of init is that: no rule to handle src tuple in ATL spec will return null, or not allocated yet.
procedure init_tar_model();
modifies $tarHeap;
ensures  (forall $o: ref :: $o == null || !read($tarHeap, $o, alloc));



procedure ARefToBRef_matchAll() returns ();
  requires (forall aRef: ref :: aRef!=null && read($srcHeap, aRef, alloc) && dtype(aRef) <: Class$ARef 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(aRef)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(aRef)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall aRef: ref ::
aRef!=null && read($srcHeap, aRef, alloc) && dtype(aRef) <: Class$ARef 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(aRef)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(aRef)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(aRef))) == Clazz$BRef);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) == Clazz$BRef) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: Class$ARef && $f==alloc )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);





procedure AtoAnnotedB_matchAll() returns ();
  requires (forall a: ref :: a!=null && read($srcHeap, a, alloc) && dtype(a) <: Class$A 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(a)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(a)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall a: ref ::
a!=null && read($srcHeap, a, alloc) && dtype(a) <: Class$A 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(a)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(a)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(a))) == Clazz$B);
  ensures (forall a: ref ::
a!=null && read($srcHeap, a, alloc) && dtype(a) <: Class$A 
 ==>
 true  ==>
getTarsBySrcs2(Seq#Singleton(a)) !=null 
&& read($tarHeap, getTarsBySrcs2(Seq#Singleton(a)), alloc)
&& dtype(getTarsBySrcs2(Seq#Singleton(a))) == Clazz$Annotation);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| (dtype($o) == Clazz$B && $f==alloc && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: Class$A)
	|| (dtype($o) == Clazz$Annotation && $f==alloc && Seq#Length(getTarsBySrcs2_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs2_inverse($o), 0)) <: Class$A )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);





/* Applier */  
  
  
procedure ARefToBRef_applyAll() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall aRef: ref :: aRef!=null && read($srcHeap, aRef, alloc) && dtype(aRef) <: Class$ARef 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(aRef)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(aRef)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(aRef))) <: Clazz$BRef);
  modifies $tarHeap;
// Rule outcome


  ensures (forall aRef: ref :: aRef!=null && read($srcHeap, aRef, alloc) && dtype(aRef) <: Class$ARef 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(aRef)), Clazz$BRef.name) == read($srcHeap, aRef, Class$ARef.name));

  ensures (forall aRef: ref :: aRef!=null && read($srcHeap, aRef, alloc) && dtype(aRef) <: Class$ARef 
 ==>
 true  ==>
dtype(read($tarHeap, getTarsBySrcs(Seq#Singleton(aRef)), Clazz$BRef.ref)) == dtype(getTarsBySrcs(Seq#Singleton(read($srcHeap, aRef, Class$ARef.ref)))));

  ensures (forall aRef: ref :: aRef!=null && read($srcHeap, aRef, alloc) && dtype(aRef) <: Class$ARef 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(aRef)), Clazz$BRef.ref) == getTarsBySrcs(Seq#Singleton(read($srcHeap, aRef, Class$ARef.ref))));





// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(Seq#Length(getTarsBySrcs_inverse($o)) == 1 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: Class$ARef 
		&& ( dtype($o) == Clazz$BRef && ($f == Clazz$BRef.name || $f == Clazz$BRef.ref))) 
		|| (read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);

procedure AtoAnnotedB_applyAll() returns();
  requires surj_tar_model($srcHeap, $tarHeap);
  requires (forall a: ref :: a!=null && read($srcHeap, a, alloc) && dtype(a) <: Class$A 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(a)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(a)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(a))) <: Clazz$B);
  modifies $tarHeap;
// Rule outcome

 ensures (forall a: ref :: a!=null && read($srcHeap, a, alloc) && dtype(a) <: Class$A 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(a)), Clazz$B.annotation) == getTarsBySrcs2(Seq#Singleton(a)));

  ensures (forall a: ref :: a!=null && read($srcHeap, a, alloc) && dtype(a) <: Class$A 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs(Seq#Singleton(a)), Clazz$B.name) == read($srcHeap, a, Class$A.name));

  ensures (forall a: ref :: a!=null && read($srcHeap, a, alloc) && dtype(a) <: Class$A 
 ==>
 true  ==>
read($tarHeap, getTarsBySrcs2(Seq#Singleton(a)), Clazz$Annotation.tag) == _0
);





// Frame property
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	!read(old($tarHeap), $o, alloc) ==>
		 ( read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f)));
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
	$o != null && read(old($tarHeap), $o, alloc) ==>
		(read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f))
	 || (Seq#Length(getTarsBySrcs_inverse($o)) == 1 
		&& dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: Class$A
		&& ( dtype($o) == Clazz$B && ($f == Clazz$B.annotation || $f == Clazz$B.name)))
	 || (Seq#Length(getTarsBySrcs2_inverse($o)) == 1 
		&& dtype(Seq#Index(getTarsBySrcs2_inverse($o), 0)) <: Class$A
		&& ( dtype($o) == Clazz$Annotation && ($f == Clazz$Annotation.tag))));
  ensures $HeapSucc(old($tarHeap), $tarHeap);
  ensures surj_tar_model($srcHeap, $tarHeap);








