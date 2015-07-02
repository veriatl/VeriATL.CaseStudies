procedure test()
// valid src model
requires (forall aRef1: ref ::
	aRef1!=null && read($srcHeap, aRef1, alloc) && dtype(aRef1) <: Class$ARef 
		==>
	dtype(read($srcHeap,aRef1,Class$ARef.ref))==Class$A
);
// pre1
requires (forall aRef1,aRef2: ref ::
	aRef1!=null && read($srcHeap, aRef1, alloc) && dtype(aRef1) <: Class$ARef 
	&& aRef2!=null && read($srcHeap, aRef2, alloc) && dtype(aRef2) <: Class$ARef 
	&& aRef1!=aRef2
		==>
	read($srcHeap,aRef1,Class$ARef.name) != read($srcHeap,aRef2,Class$ARef.name)
);
// pre2, for post4
requires (forall aRef1,aRef2: ref ::
	aRef1!=null && read($srcHeap, aRef1, alloc) && dtype(aRef1) <: Class$ARef 
	&& aRef2!=null && read($srcHeap, aRef2, alloc) && dtype(aRef2) <: Class$ARef 
	&& aRef1!=aRef2
		==>
	read($srcHeap,aRef1,Class$ARef.ref) != read($srcHeap,aRef2,Class$ARef.ref)
);
// pre3
requires (forall a1,a2: ref ::
	a1!=null && read($srcHeap, a1, alloc) && dtype(a1) <: Class$A
	&& a2!=null && read($srcHeap, a2, alloc) && dtype(a2) <: Class$A
	&& a1!=a2
		==>
	read($srcHeap,a1,Class$A.name) != read($srcHeap,a2,Class$A.name)
);

modifies $tarHeap, $linkHeap;
// post1
ensures (forall bRef1,bRef2: ref ::
	bRef1!=null && read($tarHeap, bRef1, alloc) && dtype(bRef1) <: Clazz$BRef
	&& bRef2!=null && read($tarHeap, bRef2, alloc) && dtype(bRef2) <: Clazz$BRef 
	&& bRef1!=bRef2
		==>
	read($tarHeap,bRef1,Clazz$BRef.name) != read($tarHeap,bRef2,Clazz$BRef.name)

);
// post2
ensures (forall b1,b2: ref ::
	b1!=null && read($tarHeap, b1, alloc) && dtype(b1) <: Clazz$B
	&& b2!=null && read($tarHeap, b2, alloc) && dtype(b2) <: Clazz$B
	&& b1!=b2
		==>
	read($tarHeap,b1,Clazz$B.name) != read($tarHeap,b2,Clazz$B.name)

);
// post3
ensures (forall bRef1: ref ::
	bRef1!=null && read($tarHeap, bRef1, alloc) && dtype(bRef1) <: Clazz$BRef
	&& read($srcHeap, Seq#Index(getTarsBySrcs_inverse(bRef1),0), Class$ARef.ref) != null
	&& read($srcHeap, read($srcHeap, Seq#Index(getTarsBySrcs_inverse(bRef1),0), Class$ARef.ref), alloc)
		==>
	dtype(read($tarHeap,bRef1,Clazz$BRef.ref))==Clazz$B
);
// post4
ensures (forall bRef1,bRef2: ref ::
	bRef1!=null && read($tarHeap, bRef1, alloc) && dtype(bRef1) <: Clazz$BRef
	&& read($srcHeap, Seq#Index(getTarsBySrcs_inverse(bRef1),0), Class$ARef.ref) != null
	&& read($srcHeap, read($srcHeap, Seq#Index(getTarsBySrcs_inverse(bRef1),0), Class$ARef.ref), alloc)
	&& bRef2!=null && read($tarHeap, bRef2, alloc) && dtype(bRef2) <: Clazz$BRef
	&& read($srcHeap, Seq#Index(getTarsBySrcs_inverse(bRef2),0), Class$ARef.ref) != null
	&& read($srcHeap, read($srcHeap, Seq#Index(getTarsBySrcs_inverse(bRef2),0), Class$ARef.ref), alloc)
	&& bRef1!=bRef2
		==>
	read($tarHeap, read($tarHeap,bRef1,Clazz$BRef.ref), Clazz$B.name) != 
	read($tarHeap, read($tarHeap,bRef2,Clazz$BRef.ref), Clazz$B.name) 

);
// post5
// not hold, since don't know whether it can access class$aref.ref
free ensures (forall bRef1: ref ::
	bRef1!=null && read($tarHeap, bRef1, alloc) && dtype(bRef1) <: Clazz$BRef
		==>
	dtype(read($tarHeap,bRef1,Clazz$BRef.ref))==Clazz$B
);
{

	call init_tar_model(); 

	call ARefToBRef_matchAll();
	call AtoAnnotedB_matchAll();
	
	call ARefToBRef_applyAll();
	call AtoAnnotedB_applyAll();


}


