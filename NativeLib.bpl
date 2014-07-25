// ---------------------------------------------------------------
// -- Native library of ATL transformation framework -------------
// ---------------------------------------------------------------
  

procedure NTransientLink#setRule(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  requires typeof($Unbox(Seq#Index(stk, Seq#Length(stk)-2)):ref) == Native$TransientLink;
  modifies Heap;
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-2);
  ensures Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-2)):ref, TransientLink#rule] == $Unbox(Seq#Index(stk, Seq#Length(stk)-1)):String;
  ensures (forall<alpha> o:ref, f:Field alpha :: 
	Heap[o,f] == old(Heap[o,f]) ||
	(typeof(o)==Native$TransientLink && o == $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) && f==TransientLink#rule)
  );
 

procedure NTransientLink#addSourceElement(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 3;
  requires typeof($Unbox(Seq#Index(stk, Seq#Length(stk)-3)):ref) == Native$TransientLink;
  modifies Heap;
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-3);
  ensures Map#Domain(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#source])[$Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String];
  ensures Map#Elements(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#source])[$Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String] == $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
  ensures (forall<alpha> o:ref, f:Field alpha :: 
	Heap[o,f] == old(Heap[o,f]) ||
	(typeof(o)==Native$TransientLink && o == $Unbox(Seq#Index(stk, Seq#Length(stk)-3)) && f==TransientLink#source)
  );
  ensures (forall n: String :: n!=$Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String ==>
	Map#Domain(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#source])[n] == 
	old(Map#Domain(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#source]))[n]
  );	
  ensures (forall n: String :: n!=$Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String ==>
	Map#Elements(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#source])[n] == 
	old(Map#Elements(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#source]))[n]
  );
 
procedure NTransientLink#addTargetElement(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 3;
  requires typeof($Unbox(Seq#Index(stk, Seq#Length(stk)-3)):ref) == Native$TransientLink;
  modifies Heap;
  ensures typeof(Map#Elements(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)):ref, TransientLink#target])[$Unbox(Seq#Index(stk, Seq#Length(stk)-2)):String]) == typeof($Unbox(Seq#Index(stk, Seq#Length(stk)-1)):ref);
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-3);
  ensures Map#Domain(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#target])[$Unbox(Seq#Index(stk, Seq#Length(stk)-2)):String];
  ensures Map#Elements(Heap[$Unbox(Seq#Index(stk, Seq#Length(stk)-3)), TransientLink#target])[$Unbox(Seq#Index(stk, Seq#Length(stk)-2)):String] == $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
  ensures (forall<alpha> o:ref, f:Field alpha :: 
	Heap[o,f] == old(Heap[o,f]) ||
	(typeof(o)==Native$TransientLink && o == $Unbox(Seq#Index(stk, Seq#Length(stk)-3)) && f==TransientLink#target)
  );
  
procedure NTransientLink#getSourceElement(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires typeof( $Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref ) == Native$TransientLink;
  requires Map#Domain(Heap[$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref, TransientLink#source])[$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): String];
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(Map#Elements(Heap[$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref, TransientLink#source])[$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): String]));

 
procedure NTransientLink#getTargetElement(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires typeof( $Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref ) == Native$TransientLink;
  requires Map#Domain(Heap[$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref, TransientLink#target])[$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): String];
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(Map#Elements(Heap[$Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref, TransientLink#target])[$Unbox(Seq#Index(stk,Seq#Length(stk)-1)): String]));
  
procedure ASM#Resolve<alpha>(stk: Seq BoxType, heap: HeapType, e: alpha) returns (newStk: Seq BoxType);
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) == Asm;
  ensures newStk == Seq#Build(
	Seq#Take(stk, Seq#Length(stk)-2), 
	ASM#Resolve#Sem($Unbox(Seq#Index(stk, Seq#Length(stk)-2)), heap, e)
	
	);
  
  
  // ensures  (typeof(e) == Type#String) ==> newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1));
  // ensures  (typeof(e) == Type#Integer) ==> newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1));
  // ensures  (typeof(e) == Type#Boolean) ==> newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1));
  // ensures  isTarElem(e) ==> newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1));
  // ensures ... when isSrcElem ...
  // ensures ... when isCollection ...
  

// this must place before the declaration of __apply...
// Lemma to prove: ASM#Resolve#Sem(asm, heap, elem) == ASM#Resolve#Sem(asm, oldheap, elem)
// 		The prove followed by induction on the type of resolve element:  
//1. the primitive type is straightforward, since the output didnt rely on the heap. 
//2. The simple ref did not rely on heap neither.
//3. - The bound between link is sourceElements is fixed, and there is no legal ASM operation would break this. 
//	 - The bound between link is targetElements is fixed, and there is no legal ASM operation would break this. 
//	 	==> 
//		the target ref that from a link is the same between the heap and old heap.
function ASM#Resolve#Sem<alpha>(this: ref, heap: HeapType, elem: alpha) : BoxType;
  // axiom (forall this: ref, h: HeapType, anyINT: int :: 
	// (this == Asm) ==>
		// (ASM#Resolve#Sem(this, h, anyINT) == anyINT)
  // );
  // axiom (forall this: ref, h: HeapType, anyBOOL: bool :: 
	// (this == Asm) ==>
		// (ASM#Resolve#Sem(this, h, anyBOOL) == anyBOOL)
  // );
  // axiom (forall this: ref, h: HeapType, anySTRING: String :: 
	// (this == Asm) ==>
		// (ASM#Resolve#Sem(this, h, anySTRING) == anySTRING)
  // );
  // axiom (forall this: ref, h: HeapType, anyREF: ref :: 
	// (this == Asm && (NTransientLinkSet#getLinkBySourceElement(h, anyREF) == null)) ==>
		// (ASM#Resolve#Sem(this, h, anyREF) == anyREF)
  // );
  // axiom (forall this: ref, h: HeapType, anyREF: ref :: 
	// (this == Asm && (NTransientLinkSet#getLinkBySourceElement(h, anyREF) != null)) ==>
		// (ASM#Resolve#Sem(this, h, anyREF) == NTransientLink#getTargetFromSource(
			// h, NTransientLinkSet#getLinkBySourceElement(h, anyREF), anyREF)
		// )
  // );
  // axiom (forall this: ref, h: HeapType, anyCOL: [int]ref :: 
	// (this == Asm) ==>
		// (forall i: int :: (ASM#Resolve#Sem(this, h, anyCOL): [int] ref)[i] == ASM#Resolve#Sem(this, h, anyCOL[i]))
  // );  


// this information is comes from the ATL rules, but the axiom should be true all the time...
// the function return null when the src is null, or the isTarElem(src) is true.
function NTransientLinkSet#getLinkBySourceElement(heap: HeapType, src: ref): ref;
  // Transitivity 
  axiom (forall<alpha> l: ref, f: Field (Map String ref), h1, h2: HeapType, mName: String :: 
	(Map#Elements(h1[l, f])[mName] == Map#Elements(h2[l, f])[mName]) ==>
		NTransientLinkSet#getLinkBySourceElement(h1, Map#Elements(h1[l, f])[mName]) == NTransientLinkSet#getLinkBySourceElement(h2, Map#Elements(h2[l, f])[mName])
  );
// the actual output is comes from the ATL rules - the first output of a ATL rule
// ps: the third parameter seems not necessary...
function NTransientLink#getTargetFromSource(heap: HeapType, link: ref, src: ref): ref;

function NTransientLinkSet#getLinksByRule(h: HeapType, rName: String): Seq ref;
  axiom (forall h:HeapType, rName:String, i,j: int :: 
	( (0<=i && i<Seq#Length(NTransientLinkSet#getLinksByRule(h, rName))) && 
	  (i+1<=j && j<Seq#Length(NTransientLinkSet#getLinksByRule(h, rName))) ) ==>
		Seq#Index(NTransientLinkSet#getLinksByRule(h, rName),i) != Seq#Index(NTransientLinkSet#getLinksByRule(h, rName),j)
  );
  axiom (forall h:HeapType, rName:String, i,j: int :: 
	( 0<=i && i<Seq#Length(NTransientLinkSet#getLinksByRule(h, rName)) ) ==>
		( ValidLink(h, Seq#Index(NTransientLinkSet#getLinksByRule(h, rName),i)) &&
		  h[Seq#Index(NTransientLinkSet#getLinksByRule(h, rName),i), TransientLink#rule] == rName )
  ); 
// if two rule name is different, they return disjoint result 


function Fun#LIB#AllInstanceFrom(h:HeapType, t: TName): Seq ref;
  // the length of the return result is >=0; can be useful for termination proof.
  axiom (forall h:HeapType, t: TName :: 
    Seq#Length(Fun#LIB#AllInstanceFrom(h, t)) >= 0
  ); 
  // all the model elements contained by the return result are of type $t$.
  axiom (forall h:HeapType, t: TName, i:int :: 
	( 0<=i && i<Seq#Length(Fun#LIB#AllInstanceFrom(h,t)) ) ==> 
		typeof( Seq#Index(Fun#LIB#AllInstanceFrom(h,t),i) ) == t
  );
  // all the model elements contained by the return result are allocated
  axiom (forall h:HeapType, t: TName, i:int :: 
	( 0<=i && i<Seq#Length(Fun#LIB#AllInstanceFrom(h,t)) ) ==> 
		h[Seq#Index(Fun#LIB#AllInstanceFrom(h,t),i), alloc] 
  );
  // all the allocated ref that of type $t$ are contained by the return result. 
  axiom (forall h:HeapType, o: ref, t: TName :: 
	(h[o, alloc] && (typeof(o) == t)) ==>
		Seq#Contains(Fun#LIB#AllInstanceFrom(h,t),o)
  );
  // all the model elements contained by the return result are unique 
  axiom (forall h:HeapType, t: TName, i,j:int :: 
    ( (0<=i && i<Seq#Length(Fun#LIB#AllInstanceFrom(h, t))) && 
	  (i+1<=j && j<Seq#Length(Fun#LIB#AllInstanceFrom(h, t))) ) ==>
		Seq#Index(Fun#LIB#AllInstanceFrom(h, t),i) != Seq#Index(Fun#LIB#AllInstanceFrom(h, t),j)
  ); 
  
 
 
// Sig: TName.allInstanceFrom(In/out model)
// the top of the stack is IN/OUT, the second top is a TName.
procedure LIB#AllInstanceFrom(stk: Seq BoxType, h: HeapType) returns (newStk: Seq BoxType, res: Seq ref);
  ensures res == Fun#LIB#AllInstanceFrom(h, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)));
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(res));
 
  
//--------------------------------
//-------- Helper Function -------
//--------------------------------

function typeof<alpha>(alpha): TName;
  axiom (forall s: String :: typeof(s) == Type#String);
  axiom (forall i: int :: typeof(i) == Type#Integer);
  axiom (forall b: bool :: typeof(b) == Type#Boolean);
 
  
  
function toString(ref): String;

function isFullyAllocated(o: ref): bool;

function isTarElem<alpha>(e: alpha): bool;

function ValidLink(Heap: HeapType, l: ref): bool
{
	Heap[l, alloc] &&
	typeof(l) == Native$TransientLink 
}

const unique proc: Field bool;


function top(Seq BoxType): BoxType;
  axiom (forall stk: Seq BoxType :: top(stk) == Seq#Index(stk, Seq#Length(stk)-1));

function isSrcRef(ref) : bool;
  axiom (forall o: ref :: (typeof(o)==ER$ERSchema || typeof(o) == ER$ERAttribute || typeof(o) == ER$Entity) <==> isSrcRef(o));
  
function getSrcLink(ref): ref;
  axiom (forall o1,o2:ref :: o1 == o2 && isSrcRef(o1) ==> (getSrcLink(o1) == getSrcLink(o2) && typeof(getSrcLink(o1)) == Native$TransientLink ));
  
axiom (forall o1,o2: ref :: o1 == o2 ==> typeof(o1) == typeof(o2));