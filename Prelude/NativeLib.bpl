// ---------------------------------------------------------------
// -- Native library of ATL transformation framework -------------
// ---------------------------------------------------------------
  

var $srcHeap : HeapType where $IsGoodHeap($srcHeap);
var $tarHeap : HeapType where $IsGoodHeap($tarHeap);
var $linkHeap : HeapType where $IsGoodHeap($tarHeap);



function getTarsBySrcs(Seq ref): ref;

function getTarsBySrcs_inverse(ref): Seq ref;
axiom (forall i: Seq ref :: { getTarsBySrcs(i) } getTarsBySrcs_inverse(getTarsBySrcs(i)) == i);

function surj_tar_model($s: HeapType, $t: HeapType): bool
{
(
forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == REL$RELSchema ==>
	(exists $i: ref :: dtype($i) == ER$ERSchema && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o)
)
}


procedure NTransientLink#setRule
	(stk: Seq BoxType, link: ref, ruleName: String) 
returns 
	(newStk: Seq BoxType)
  requires Seq#Length(stk) >= 2; 
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-1)):String == ruleName;
  requires dtype(link) == Native$TransientLink;
  modifies $linkHeap;
  ensures read($linkHeap, link, TransientLink#rule) == ruleName;
  ensures (forall<T> $f: Field T :: $f!=TransientLink#rule ==> 
	read($linkHeap, link, $f) == read(old($linkHeap), link, $f)
  );
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($linkHeap, $o, $f) } $o != null && read(old($linkHeap), $o, alloc) ==> read($linkHeap, $o, $f) == read(old($linkHeap), $o, $f) || $o == link);
  ensures $HeapSucc(old($linkHeap), $linkHeap); 
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-2);
{
	$linkHeap := update($linkHeap, link, TransientLink#rule, ruleName);
	assume $IsGoodHeap($linkHeap);
	newStk := Seq#Take(stk, Seq#Length(stk)-2);
}
  

procedure  NTransientLink#addSourceElement
	(stk: Seq BoxType, link: ref, key: String, val: ref) 
returns 
	(newStk: Seq BoxType)
  requires Seq#Length(stk) >= 3; 
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-1)):ref == val;
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-2)):String == key;
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-3)):ref == link;
  requires dtype(link) == Native$TransientLink;
  modifies $linkHeap;
  ensures read($linkHeap, link, TransientLink#source) == Map#Build(old($linkHeap[link, TransientLink#source]), key, val);
  ensures (forall<T> $f: Field T :: $f!=TransientLink#source ==> 
	read($linkHeap, link, $f) == read(old($linkHeap), link, $f)
  );
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($linkHeap, $o, $f) } $o != null && read(old($linkHeap), $o, alloc) ==> read($linkHeap, $o, $f) == read(old($linkHeap), $o, $f) || $o == link);
  ensures $HeapSucc(old($linkHeap), $linkHeap); 
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-3);  
{
	$linkHeap := update($linkHeap, link, TransientLink#source, Map#Build($linkHeap[link, TransientLink#source], key, val));
	assume $IsGoodHeap($linkHeap);
	newStk := Seq#Take(stk, Seq#Length(stk)-3);
}
  
  
procedure NTransientLink#addTargetElement
	(stk: Seq BoxType, link: ref, key: String, val: ref) 
returns 
	(newStk: Seq BoxType)
  requires Seq#Length(stk) >= 3; 
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-1)):ref == val;
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-2)):String == key;
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-3)):ref == link;
  requires dtype(link) == Native$TransientLink;
  modifies $linkHeap;
  ensures read($linkHeap, link, TransientLink#target) == Map#Build(old($linkHeap[link, TransientLink#target]), key, val);
  ensures (forall<T> $f: Field T :: $f!=TransientLink#target ==> 
	read($linkHeap, link, $f) == read(old($linkHeap), link, $f)
  );
  ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($linkHeap, $o, $f) } $o != null && read(old($linkHeap), $o, alloc) ==> read($linkHeap, $o, $f) == read(old($linkHeap), $o, $f) || $o == link);
  ensures $HeapSucc(old($linkHeap), $linkHeap); 
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-3);
{
	$linkHeap := update($linkHeap, link, TransientLink#target, Map#Build($linkHeap[link, TransientLink#target], key, val));
	assume $IsGoodHeap($linkHeap);
	newStk := Seq#Take(stk, Seq#Length(stk)-3);
}

procedure NTransientLink#getSourceElement
	(stk: Seq BoxType, link: ref, key: String) 
returns 
	(newStk: Seq BoxType)
  requires Seq#Length(stk) >= 2; 
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-1)):String == key;
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-2)):ref == link;
  requires dtype(link) == Native$TransientLink;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(Map#Elements($linkHeap[link, TransientLink#source])[key]));
{
	newStk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(Map#Elements($linkHeap[link, TransientLink#source])[key]));
}

procedure NTransientLink#getTargetElement
	(stk: Seq BoxType, link: ref, key: String) 
returns 
	(newStk: Seq BoxType)
  requires Seq#Length(stk) >= 2; 
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-1)):String == key;
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-2)):ref == link;
  requires dtype(link) == Native$TransientLink; 
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(Map#Elements($linkHeap[link, TransientLink#target])[key]));
{
	newStk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(Map#Elements($linkHeap[link, TransientLink#target])[key]));
}

procedure ASM#Resolve<alpha>(stk: Seq BoxType, heap: HeapType, e: alpha) returns (newStk: Seq BoxType);
  requires $Unbox(Seq#Index(stk, Seq#Length(stk)-2)) == Asm;
  ensures newStk == Seq#Build(
	Seq#Take(stk, Seq#Length(stk)-2), 
	ASM#Resolve#Sem($Unbox(Seq#Index(stk, Seq#Length(stk)-2)), heap, e)
	);

function ASM#Resolve#Sem<alpha>(this: ref, heap: HeapType, elem: alpha) : BoxType;
	axiom (forall this:ref, heap: HeapType, elem: String ::
		ASM#Resolve#Sem(this, heap, elem) == $Box(elem)
	);
	
	
function invisble#getLinkbySources(s: Set ref): ref;
  axiom (forall s1,s2 : Set ref :: !Set#Equal(s1,s2) ==> 
	invisble#getLinkbySources(s1) != invisble#getLinkbySources(s2));
	
/* ------------------------------------------------------ */ 

function Fun#LIB#AllInstanceFrom(h:HeapType, t: ClassName): Seq ref;
  // the length of the return result is >=0; can be useful for termination proof.
  axiom (forall h:HeapType, t: ClassName :: 
    Seq#Length(Fun#LIB#AllInstanceFrom(h, t)) >= 0
  ); 
  // all the model elements contained by the return result are of type $t$.
  axiom (forall h:HeapType, t: ClassName, i:int :: 
	( 0<=i && i<Seq#Length(Fun#LIB#AllInstanceFrom(h,t)) ) ==> 
		dtype( Seq#Index(Fun#LIB#AllInstanceFrom(h,t),i) ) == t
  );
  // all the model elements contained by the return result are allocated
  axiom (forall h:HeapType, t: ClassName, i:int :: 
	( 0<=i && i<Seq#Length(Fun#LIB#AllInstanceFrom(h,t)) ) ==> 
		h[Seq#Index(Fun#LIB#AllInstanceFrom(h,t),i), alloc] && Seq#Index(Fun#LIB#AllInstanceFrom(h,t),i) != null
  );
  // all the allocated ref that of type $t$ are contained by the return result. 
  axiom (forall h:HeapType, o: ref, t: ClassName :: 
	(h[o, alloc] && (dtype(o) == t)) ==>
		Seq#Contains(Fun#LIB#AllInstanceFrom(h,t),o)
  );
  // all the model elements contained by the return result are unique 
  axiom (forall h:HeapType, t: ClassName, i,j:int :: 
    ( (0<=i && i<Seq#Length(Fun#LIB#AllInstanceFrom(h, t))) && 
	  (i+1<=j && j<Seq#Length(Fun#LIB#AllInstanceFrom(h, t))) ) ==>
		Seq#Index(Fun#LIB#AllInstanceFrom(h, t),i) != Seq#Index(Fun#LIB#AllInstanceFrom(h, t),j)
  ); 
  
 
procedure LIB#AllInstanceFrom(stk: Seq BoxType, h: HeapType) returns (newStk: Seq BoxType, res: Seq ref);
  ensures res == Fun#LIB#AllInstanceFrom(h, $Unbox(Seq#Index(stk, Seq#Length(stk)-2)));
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(res));
 
 
 
 
 
/* h refers to linkheap, r referes to the rule name */
function NTransientLinkSet#getLinksByRule(h:HeapType, rule: String): Seq ref;
  // the length of the return result is >=0; can be useful for termination proof.
  axiom (forall h:HeapType, r: String :: 
    Seq#Length(NTransientLinkSet#getLinksByRule(h, r)) >= 0
  ); 
  // unique links
  axiom (forall h:HeapType, r: String, i,j:int :: 
    ( (0<=i && i<Seq#Length(NTransientLinkSet#getLinksByRule(h,r))) && 
	  (i+1<=j && j<Seq#Length(NTransientLinkSet#getLinksByRule(h,r)) ) ==>
		Seq#Index(NTransientLinkSet#getLinksByRule(h, r),i) != Seq#Index(NTransientLinkSet#getLinksByRule(h, r),j)
  ));
  // unique target elements
  axiom (forall h:HeapType, r: String, i,j:int :: 
    ( (0<=i && i<Seq#Length(NTransientLinkSet#getLinksByRule(h,r))) && 
	  (i+1<=j && j<Seq#Length(NTransientLinkSet#getLinksByRule(h,r)) ) ==>
		getTarsBySrcs(Seq#Singleton(Map#Elements(read(h, Seq#Index(NTransientLinkSet#getLinksByRule(h, r),i), TransientLink#source))[_s])) != getTarsBySrcs(Seq#Singleton(Map#Elements(read(h, Seq#Index(NTransientLinkSet#getLinksByRule(h, r),j), TransientLink#source))[_s]))
  ));
  // all links's src and target are paired
  axiom (forall h:HeapType, r: String, i: int:: 0<=i &&i <Seq#Length(NTransientLinkSet#getLinksByRule(h,r)) ==>			
			getTarsBySrcs(Seq#Singleton(Map#Elements(h[Seq#Index(NTransientLinkSet#getLinksByRule(h,r),i), TransientLink#source])[_s])) == 
			Map#Elements(h[Seq#Index(NTransientLinkSet#getLinksByRule(h,r),i), TransientLink#target])[_t]
		);
		
//--------------------------------
//-------- Helper Function -------
//--------------------------------

function top(Seq BoxType): BoxType;
  axiom (forall stk: Seq BoxType :: top(stk) == Seq#Index(stk, Seq#Length(stk)-1));

function isSrcRef(ref) : bool;
  axiom (forall o: ref :: (dtype(o)==ER$ERSchema || dtype(o) == ER$ERAttribute || dtype(o) == ER$Entity) <==> isSrcRef(o));
  
function getSrcLink(ref): ref;
  axiom (forall o1,o2:ref :: o1 == o2 && isSrcRef(o1) ==> (getSrcLink(o1) == getSrcLink(o2) && dtype(getSrcLink(o1)) == Native$TransientLink ));
  
axiom (forall o1,o2: ref :: o1 == o2 ==> dtype(o1) == dtype(o2));


procedure OCL#Object#Equal<T> (stk: Seq BoxType, o1: T, o2: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	o1 == o2
  ));  



// ---------------------------------------------------------------
// -- OCL: Boolean, 5 operations             ---------------------
// ---------------------------------------------------------------


procedure OCL#Boolean#Not (stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 1;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(!($Unbox(Seq#Index(stk,Seq#Length(stk)-1)):bool)));  

procedure OCL#Boolean#And (stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	($Unbox(Seq#Index(stk,Seq#Length(stk)-2)):bool) && 
	($Unbox(Seq#Index(stk,Seq#Length(stk)-1)):bool)
  ));  
 
procedure OCL#Boolean#Or (stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	($Unbox(Seq#Index(stk,Seq#Length(stk)-2)):bool) || 
	($Unbox(Seq#Index(stk,Seq#Length(stk)-1)):bool)
  ));

procedure OCL#Boolean#Xor (stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	(($Unbox(Seq#Index(stk,Seq#Length(stk)-2)):bool) || ($Unbox(Seq#Index(stk,Seq#Length(stk)-1)):bool)) &&
	!(($Unbox(Seq#Index(stk,Seq#Length(stk)-2)):bool) && ($Unbox(Seq#Index(stk,Seq#Length(stk)-1)):bool))
  ));    

procedure OCL#Boolean#Implies (stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	!($Unbox(Seq#Index(stk,Seq#Length(stk)-2)):bool) ||
	($Unbox(Seq#Index(stk,Seq#Length(stk)-1)):bool)
  ));  



// ---------------------------------------------------------------
// -- OCL: Set, 8 operations                 ---------------------
// ---------------------------------------------------------------
// need to mention T, so make the stack operand s1, s2 explicit
procedure OCL#Set#Union<T> (stk: Seq BoxType, s1: Set T, s2: Set T ) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Set#Union(s1, s2)
  ));   

procedure OCL#Set#Intersection<T> (stk: Seq BoxType, s1: Set T, s2: Set T ) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Set#Intersection(s1, s2)
  ));  

procedure OCL#Set#Including<T> (stk: Seq BoxType, s: Set T, e: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Set#UnionOne(s, e)
  )); 

procedure OCL#Set#Excluding<T> (stk: Seq BoxType, s1: Set T, s2: Set T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Set#Difference(s1, s2)
  )); 

// todo: similar to excluding but the s2 can be any of the collection type, case analysis needed.  
procedure OCL#Set#Difference<T, X> (stk: Seq BoxType, s1: Set T, s2: X) returns (newStk: Seq BoxType);

procedure OCL#Set#SymetricDifference<T> (stk: Seq BoxType, s1: Set T, s2: Set T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Set#Difference(Set#Union(s1, s2), Set#Intersection(s1,s2))
  )); 
  
procedure OCL#Set#asSet<T> (stk: Seq BoxType, s1: Set T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 1;
  ensures newStk == stk;

// todo: turn the input set into a sequence, pop, then put the seq on top of the result stack.  
procedure OCL#Set#asSeq<T> (stk: Seq BoxType, s1:Set T) returns (newStk: Seq BoxType);
 

// ---------------------------------------------------------------
// -- OCL: OrderSet, 3 operations            ---------------------
// ---------------------------------------------------------------
// OrderSet are modelled as Sequence.
// except the 3 operations defined below, other operations are the same as defined on Seq.
procedure OCL#OrderSet#Append<T> (stk: Seq BoxType, s1: Seq T, e: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures Seq#Contains(s1, e) ==> (newStk == Seq#Take(stk, Seq#Length(stk)-1)); // contained e, pop e out of stk. 
  ensures !Seq#Contains(s1, e) ==> (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Seq#Build(s1, e)
  ))); 
  
procedure OCL#OrderSet#Prepend<T> (stk: Seq BoxType, s1: Seq T, e: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures Seq#Contains(s1, e) ==> (newStk == Seq#Take(stk, Seq#Length(stk)-1)); // contained e, pop e out of stk. 
  ensures !Seq#Contains(s1, e) ==> (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Seq#Append(Seq#Singleton(e), s1)
  ))); 


// insert e(-1) into rank n(-2) of s1(-3).  
procedure OCL#OrderSet#InsertAt<T> (stk: Seq BoxType, s1: Seq T, n: int, e: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 3;
  requires n <= Seq#Length(s1);
  ensures Seq#Contains(s1, e) ==> (newStk == Seq#Take(stk, Seq#Length(stk)-2)); // contained e, pop e out of stk. 
  ensures (!Seq#Contains(s1, e) && n<Seq#Length(s1) )==> (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-3), $Box(
	Seq#Append(Seq#Build(Seq#Take(s1,n),e), Seq#Drop(s1,n))
  ))); 
  ensures (!Seq#Contains(s1, e) && n==Seq#Length(s1) )==> (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-3), $Box(
	Seq#Build(s1, e)
  ))); 
  
// ---------------------------------------------------------------
// -- OCL: Sequence, 10 operations           ---------------------
// ---------------------------------------------------------------
procedure OCL#Seq#InsertAt<T> (stk: Seq BoxType, s1: Seq T, n: int, e: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 3;
  requires n <= Seq#Length(s1);
  ensures ( n<Seq#Length(s1) )==> (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-3), $Box(
	Seq#Append(Seq#Build(Seq#Take(s1,n),e), Seq#Drop(s1,n))
  ))); 
  ensures ( n==Seq#Length(s1) )==> (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-3), $Box(
	Seq#Build(s1, e)
  ))); 

procedure OCL#Seq#At<T> (stk: Seq BoxType, s1: Seq T, n: int) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures ( n<Seq#Length(s1) )==> (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Seq#Index(s1,n)
  ))); 
  
procedure OCL#Seq#SubSequence<T> (stk: Seq BoxType, s1: Seq T, lo: int, hi: int) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 3;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-3), $Box(
	Seq#Drop(Seq#Take(s1,hi),lo)
  )));   


procedure OCL#Seq#Append<T> (stk: Seq BoxType, s1: Seq T, e: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Seq#Build(s1, e)
  ))); 
  
procedure OCL#Seq#Prepend<T> (stk: Seq BoxType, s1: Seq T, e: T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Seq#Append(Seq#Singleton(e), s1)
  ))); 
  
// as it is implemented, the same as the Seq#Append.
procedure OCL#Seq#Including<T> (stk: Seq BoxType, s1: Seq T, e: T) returns (newStk: Seq BoxType);



procedure OCL#Seq#AsSeq<T> (stk: Seq BoxType, s1: Seq T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 1;
  ensures newStk == stk;

// acutally, s2 can be any of the collection type, case analysis needed here  
procedure OCL#Seq#Union<T> (stk: Seq BoxType, s1: Seq T, s2: Seq T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=2;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	Seq#Append(s1, s2)
  ))); 

procedure OCL#Seq#First<T> (stk: Seq BoxType, s1: Seq T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=1;
  requires s1!=Seq#Empty();
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(
	Seq#Index(s1,0)
  ))); 

procedure OCL#Seq#Last<T> (stk: Seq BoxType, s1: Seq T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=1;
  requires s1!=Seq#Empty();
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(
	Seq#Index(s1,Seq#Length(s1)-1)
  ))); 
  
procedure OCL#Seq#indexOf<T>(stk: Seq BoxType, s1: Seq T, e: T) returns (newStk: Seq BoxType);
procedure OCL#Seq#Excluding<T> (stk: Seq BoxType, s1: Seq T, e: T) returns (newStk: Seq BoxType);
procedure OCL#Seq#Flatten<T> (stk: Seq BoxType, s1: Seq T) returns (newStk: Seq BoxType);

// ---------------------------------------------------------------
// -- OCL: Bag, 2 operations                 ---------------------
// ---------------------------------------------------------------
procedure OCL#Bag#AsBag<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 1;
  ensures newStk == stk;

procedure OCL#Bag#Including<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);


  
procedure OCL#Bag#Excluding<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);  


  
procedure OCL#Bag#Flatten<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);  



// ---------------------------------------------------------------
// -- OCL: Integer, X operations             ---------------------
// ---------------------------------------------------------------
