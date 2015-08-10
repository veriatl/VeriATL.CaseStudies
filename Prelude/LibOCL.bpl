// ---------------------------------------------------------------
// Axiom of FieldOfDecl, 
// ---------------------------------------------------------------

axiom (forall<T> cl : ClassName, nm: NameFamily :: 
   {FieldOfDecl(cl, nm): Field T}
   /*DeclType(FieldOfDecl(cl, nm): Field T) == cl && */ 
   DeclName(FieldOfDecl(cl, nm): Field T) == nm);

   

   
// ---------------------------------------------------------------
// OCL: String 
// We assume each string is a sequence of int.
// each charactor has a integer representation (ASCII), e.g. 'A' = 65, 'a' = 97
// ---------------------------------------------------------------

type String = Seq Char;
type Char = int;


function String#Size(String): int;
  axiom (forall s: String :: Seq#Length(s) == String#Size(s));

function String#Concate(src:String,surfix:String): String;
  axiom (forall src, surfix: String :: Seq#Equal(String#Concate(src, surfix), Seq#Append(src, surfix)));


function String#ToUpper(String): String;
  axiom (forall s: String :: { Seq#Length(String#ToUpper(s)) }
	Seq#Length(String#ToUpper(s)) == Seq#Length(s));
  axiom (forall s: String, i: int :: { Seq#Index(String#ToUpper(s),i) }
	(0 <= i && i < Seq#Length(s) ==> 
		((97 <= Seq#Index(s,i) && Seq#Index(s,i) <= 122 ==> Seq#Index(s,i) == Seq#Index(String#ToUpper(s),i) + 22) &&
		 (97 > Seq#Index(s,i) || Seq#Index(s,i) > 122 ==> Seq#Index(s,i) == Seq#Index(String#ToUpper(s),i))) 
	) 
  );
  
function String#ToLower(String): String;
  axiom (forall s: String :: { Seq#Length(String#ToLower(s)) }
	Seq#Length(String#ToLower(s)) == Seq#Length(s));
  axiom (forall s: String, i: int :: { Seq#Index(String#ToLower(s),i) }
	(0 <= i && i < Seq#Length(s) ==> 
		((65 <= Seq#Index(s,i) && Seq#Index(s,i) <= 90 ==> Seq#Index(s,i) == Seq#Index(String#ToLower(s),i) - 22) &&
		 (65 > Seq#Index(s,i) || Seq#Index(s,i) > 90 ==> Seq#Index(s,i) == Seq#Index(String#ToLower(s),i))) 
	) 
  );


function String#StartWith(src: String, prefix: String): bool;
  axiom (forall s: String, pf: String :: { String#StartWith(s,pf) }
	String#StartWith(s,pf) <==> 
		(forall i: int :: { Seq#Index(s,i) } { Seq#Index(pf,i) }
			0 <= i && i < Seq#Length(pf) ==> Seq#Index(s,i) == Seq#Index(pf,i))
  );

function String#EndWith(src: String, surfix: String): bool;
  axiom (forall s: String, sf: String :: { String#EndWith(s,sf) }
	String#EndWith(s,sf) <==> 
		(forall i: int :: { Seq#Index(s,i) } { Seq#Index(sf,i) }
			0 <= i && i < Seq#Length(sf) ==> Seq#Index(s,i+Seq#Length(s)-Seq#Length(sf)) == Seq#Index(sf,i))
  );  

function String#Substring(s: String, lower: int, upper: int): String;
  axiom (forall s: String, l: int, u: int ::
	String#Substring(s,l,u) == Seq#Drop(Seq#Take(s,u),l)
  );



// ---------------------------------------------------------------
// OCL: Set Extension
// ---------------------------------------------------------------
  

function Set#DifferenceOne<T>(Set T, T): Set T;
//TODO: Double check
  axiom (forall<T> a: Set T, x: T, o: T :: { Set#DifferenceOne(a,x)[o] }
    Set#DifferenceOne(a,x)[o] <==> o!=x && a[o]);	
  axiom (forall<T> a: Set T, x: T :: { Set#DifferenceOne(a, x) }
    !Set#DifferenceOne(a, x)[x]);

function Set#Includes<T>(Set T, T): bool;  
  axiom (forall<T> a: Set T, x: T :: { Set#Includes(a, x) }
    Set#Includes(a, x) <==> a[x]);
  
function Set#Excludes<T>(Set T, T): bool;
  axiom (forall<T> a: Set T, x: T :: { Set#Excludes(a, x) }
    Set#Excludes(a, x) <==> !a[x]);
  
function Set#isEmpty<T>(Set T, T): bool;
  axiom (forall<T> a: Set T, x: T :: { Set#isEmpty(a, x) }
    Set#isEmpty(a, x) <==> (Set#Equal(a, Set#Empty())));
  
function Set#notEmpty<T>(Set T, T): bool;  
  axiom (forall<T> a: Set T, x: T :: { Set#notEmpty(a, x) }
    Set#notEmpty(a, x) <==> (!Set#Equal(a, Set#Empty())));

// ---------------------------------------------------------------
// OCL: Bag Extension
// ---------------------------------------------------------------

function MultiSet#DifferenceOne<T>(MultiSet T, T): MultiSet T;
// pure containment axiom 
axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#DifferenceOne(a,x)[o] }
  0 < MultiSet#DifferenceOne(a,x)[o] <==> o != x && 0 < a[o]);
// del-ing decreases count by one
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#DifferenceOne(a, x) }
  a[x] > 0 ==> MultiSet#DifferenceOne(a, x)[x] == a[x] - 1);
// other elements unchanged
axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#DifferenceOne(a, x), a[y] }
  x != y ==> a[y] == MultiSet#DifferenceOne(a, x)[y]);
  
  
function MultiSet#Includes<T>(MultiSet T, T): bool;  
  axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Includes(a, x) }
    MultiSet#Includes(a, x) <==> (a[x]>0));
  
function MultiSet#Excludes<T>(MultiSet T, T): bool;
  axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Excludes(a, x) }
    MultiSet#Excludes(a, x) <==> (a[x]==0));
  
function MultiSet#isEmpty<T>(MultiSet T, T): bool;
  axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#isEmpty(a, x) }
    MultiSet#isEmpty(a, x) <==> (MultiSet#Equal(a, MultiSet#Empty())));
  
function MultiSet#notEmpty<T>(MultiSet T, T): bool;  
  axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#notEmpty(a, x) }
    MultiSet#notEmpty(a, x) <==> (!MultiSet#Equal(a, MultiSet#Empty())));  
  
// ---------------------------------------------------------------
// OCL: Seq Extension
// ---------------------------------------------------------------

function Seq#Prepend<T>(Seq T, T): Seq T;  
  axiom (forall<T> a: Seq T, x: T :: { Seq#Prepend(a, x) }
    Seq#Equal(Seq#Prepend(a, x), Seq#Append(Seq#Singleton(x), a))); 
	
function Seq#First<T>(Seq T): T;  
  axiom (forall<T> a: Seq T :: { Seq#First(a) }
  a != Seq#Empty() ==> (Seq#First(a) == Seq#Index(a,0)) ); 
  
function Seq#Last<T>(Seq T): T;  
  axiom (forall<T> a: Seq T :: { Seq#Last(a) }
  a != Seq#Empty() ==> (Seq#Last(a) == Seq#Index(a,Seq#Length(a)-1)) );   
  
function Seq#insertAt<T>(Seq T, int, T): Seq T;
  axiom (forall<T> a: Seq T, n: int, x: T :: { Seq#insertAt(a, n, x) }
    n<Seq#Length(a) ==> 
	  Seq#Equal(Seq#insertAt(a, n, x), Seq#Append(Seq#Build(Seq#Take(a,n),x), Seq#Drop(a,n))));
  axiom (forall<T> a: Seq T, n: int, x: T :: { Seq#insertAt(a, n, x) }
    n==Seq#Length(a) ==> 
	  Seq#Equal(Seq#insertAt(a, n, x), Seq#Build(a, x))); 	  
  
function Seq#subSequence<T>(Seq T, int, int): Seq T;
  axiom (forall<T> a: Seq T, lo: int, hi: int :: { Seq#subSequence(a, lo, hi) }
    Seq#Equal(Seq#subSequence(a,lo,hi), Seq#Drop(Seq#Take(a,hi),lo))); 
  
function Seq#NotContains<T>(Seq T, T): bool;
  axiom (forall<T> a: Seq T, x: T :: { Seq#NotContains(a, x) }
    Seq#NotContains(a, x) <==> !Seq#Contains(a,x));
  
function Seq#isEmpty<T>(Seq T, T): bool;
  axiom (forall<T> a: Seq T, x: T :: { Seq#isEmpty(a, x) }
    Seq#isEmpty(a, x) <==> (Seq#Equal(a, Seq#Empty())));
  
function Seq#notEmpty<T>(Seq T, T): bool;  
  axiom (forall<T> a: Seq T, x: T :: { Seq#notEmpty(a, x) }
    Seq#notEmpty(a, x) <==> (!Seq#Equal(a, Seq#Empty()))); 

// ---------------------------------------------------------------
// OCL: OrderedSet
// ---------------------------------------------------------------

  
// ---------------------------------------------------------------
// OCL: Sequence - Generic Iterators, 
// see 'testLibOCL.bpl' for example of its application
// TODO: consider refactoring
// ---------------------------------------------------------------
function Iterator#One<T>(s: Seq T, h: HeapType, f:[T,HeapType]bool): bool;
	axiom  (forall<T> s: Seq T, h: HeapType, f:[T,HeapType]bool :: { Iterator#One(s,h,f) } 
		Iterator#One(s,h,f) <==> Seq#Length(Iterator#Select(0,Seq#Length(s)-1,s,h,f)) == 1);
		
function Iterator#Any<T>(s: Seq T, h: HeapType, f:[T,HeapType]bool): T;
	axiom  (forall<T> s: Seq T, h: HeapType, f:[T,HeapType]bool :: 
		Iterator#Any(s,h,f) == null <==> 
			(forall i: int :: 0<=i && i<Seq#Length(s) ==> !f[Seq#Index(s,i),h]));
	axiom  (forall<T> s: Seq T, h: HeapType, f:[T,HeapType]bool :: 
		Iterator#Any(s,h,f) != null <==> 
			f[Iterator#Any(s,h,f),h] && Seq#Contains(s, Iterator#Any(s,h,f)));
			
function Iterator#Collect<T,R>(s: Seq T, h: HeapType, f:[T,HeapType]R): Seq R;
	axiom (forall<T,R> s: Seq T, h: HeapType, f:[T,HeapType]R :: { Iterator#Collect(s,h,f) } 
		Seq#Length(s) == Seq#Length(Iterator#Collect(s,h,f))); 
	axiom (forall<T,R> s: Seq T, h: HeapType, f:[T,HeapType]R, i: int :: {Seq#Index(Iterator#Collect(s,h,f),i)}
		0<=i && i<Seq#Length(s) ==> f[Seq#Index(s,i),h] == Seq#Index(Iterator#Collect(s,h,f),i));


function Iterator#Reject<T>(lo: int, hi: int, s: Seq T, h: HeapType, f:[T,HeapType]bool): Seq T;
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Reject(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,lo), h] ==>
		Iterator#Reject(lo,hi,s,h,f) == Seq#Append(Seq#Singleton(Seq#Index(s,lo)),Iterator#Reject(lo+1,hi,s,h,f))	
	);	
	axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Reject(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,lo), h] ==>
		Iterator#Reject(lo,hi,s,h,f) == Iterator#Reject(lo+1,hi,s,h,f)
	);
	axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Reject(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,hi-1), h]==>
		Iterator#Reject(lo,hi,s,h,f) == Seq#Append(Iterator#Reject(lo,hi-1,s,h,f), Seq#Singleton(Seq#Index(s,hi-1)))
	); 
	axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Reject(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,hi-1), h] ==>
		Iterator#Reject(lo,hi,s,h,f) == Iterator#Reject(lo,hi-1,s,h,f)
	);
	axiom (forall<T> mid:int, lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Reject(lo,mid,s,h,f), Iterator#Reject(lo,hi,s,h,f)} {Iterator#Reject(lo,mid,s,h,f), Iterator#Reject(mid,hi,s,h,f)}
		lo<=mid && mid<=hi ==>
		Iterator#Reject(lo,hi,s,h,f) == Seq#Append(Iterator#Reject(lo,mid,s,h,f),Iterator#Reject(mid,hi,s,h,f))
	);
	axiom (forall<T> i:int, lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Seq#Index(Iterator#Reject(lo,hi,s,h,f),i)}
		0<=i && i<Seq#Length(Iterator#Reject(lo,hi,s,h,f)) ==> !f[Seq#Index(Iterator#Reject(lo,hi,s,h,f),i), h]
	);
	
	
function Iterator#Select<T>(lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool): Seq T;
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Select(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,lo), h] ==>
		Iterator#Select(lo,hi,s,h,f) == Seq#Append(Seq#Singleton(Seq#Index(s,lo)),Iterator#Select(lo+1,hi,s,h,f))	
	);
	axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Select(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,lo), h] ==>
		Iterator#Select(lo,hi,s,h,f) == Iterator#Select(lo+1,hi,s,h,f)
	);
    axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Select(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,hi-1), h]==>
		Iterator#Select(lo,hi,s,h,f) == Seq#Append(Iterator#Select(lo,hi-1,s,h,f), Seq#Singleton(Seq#Index(s,hi-1)))
	); 
	axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Select(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,hi-1), h] ==>
		Iterator#Select(lo,hi,s,h,f) == Iterator#Select(lo,hi-1,s,h,f)
	);
	axiom (forall<T> mid:int, lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Select(lo,mid,s,h,f), Iterator#Select(lo,hi,s,h,f)} {Iterator#Select(lo,mid,s,h,f), Iterator#Select(mid,hi,s,h,f)}
		lo<=mid && mid<=hi ==>
		Iterator#Select(lo,hi,s,h,f) == Seq#Append(Iterator#Select(lo,mid,s,h,f),Iterator#Select(mid,hi,s,h,f))
	);
	axiom (forall<T> i:int, lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Seq#Index(Iterator#Select(lo,hi,s,h,f),i)}
		0<=i && i<Seq#Length(Iterator#Select(lo,hi,s,h,f)) ==> f[Seq#Index(Iterator#Select(lo,hi,s,h,f),i), h]
	);

	
function Iterator#Forall<T>(lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool): bool;
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Forall(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,lo), h] ==>
		(Iterator#Forall(lo,hi,s,h,f) <==> Iterator#Forall(lo+1,hi,s,h,f))	
	);
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Forall(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,lo), h] ==>
		!Iterator#Forall(lo,hi,s,h,f) 
	);
	axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Forall(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,hi-1), h]==>
		(Iterator#Forall(lo,hi,s,h,f) <==> Iterator#Forall(lo,hi-1,s,h,f))	
	); 
	axiom (forall<T> lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Forall(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,hi-1), h] ==>
		!Iterator#Forall(lo,hi,s,h,f) 
	);
	axiom (forall<T> mid:int, lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Forall(lo,mid,s,h,f), Iterator#Forall(lo,hi,s,h,f)} {Iterator#Forall(lo,mid,s,h,f), Iterator#Forall(mid,hi,s,h,f)}
		lo<=mid && mid<=hi ==>
		(Iterator#Forall(lo,hi,s,h,f) <==> (Iterator#Forall(lo,mid,s,h,f) && Iterator#Forall(mid,hi,s,h,f)))
	);
	
function Iterator#Exists<T>(lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool): bool;
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Exists(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,lo), h] ==>
		Iterator#Exists(lo,hi,s,h,f)
	);
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Exists(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,lo), h] ==>
		(Iterator#Exists(lo,hi,s,h,f) <==> Iterator#Exists(lo+1,hi,s,h,f))
	);
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Exists(lo,hi,s,h,f)}
		lo<hi && f[Seq#Index(s,hi-1), h] ==>
		Iterator#Exists(lo,hi,s,h,f)
	);
	axiom (forall<T> lo: int, hi: int, s: Seq T, h:HeapType, f:[T, HeapType]bool :: {Iterator#Exists(lo,hi,s,h,f)}
		lo<hi && !f[Seq#Index(s,hi-1), h] ==>
		(Iterator#Exists(lo,hi,s,h,f) <==> Iterator#Exists(lo,hi-1,s,h,f))
	);
	axiom (forall<T> mid:int, lo: int, hi: int, s: Seq T, h: HeapType, f:[T, HeapType]bool :: {Iterator#Exists(lo,mid,s,h,f), Iterator#Exists(lo,hi,s,h,f)} {Iterator#Exists(lo,mid,s,h,f), Iterator#Exists(mid,hi,s,h,f)}
		lo<=mid && mid<=hi ==>
		(Iterator#Exists(lo,hi,s,h,f) <==> (Iterator#Exists(lo,mid,s,h,f) && Iterator#Exists(mid,hi,s,h,f)))
	);
	

function Iterator#isUnique<T,R>(s: Seq T, h: HeapType, f:[T, HeapType]R): bool;
	axiom (forall<T,R> s: Seq T, h: HeapType, f:[T, HeapType]R :: {Iterator#isUnique(s,h,f)}
		Iterator#isUnique(s,h,f) <==> (forall i,j: int :: 0<=i && i<j && j <Seq#Length(s) ==> f[Seq#Index(s,i),h]!=f[Seq#Index(s,j),h])
	);



// ---------------------------------------------------------------
// -- OCL: Integer, X operations             ---------------------
// ---------------------------------------------------------------

procedure OCLAny#IsUndefined(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=1;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(
	$Unbox(Seq#Index(stk,Seq#Length(stk)-1)) == null
  )));
  
  
procedure OCLAny#Not(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=1;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(
	!($Unbox(Seq#Index(stk,Seq#Length(stk)-1)): bool)
  )));

procedure OCLAny#And(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=2;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	($Unbox(Seq#Index(stk,Seq#Length(stk)-2)): bool) &&
	($Unbox(Seq#Index(stk,Seq#Length(stk)-1)): bool)
  )));

procedure OCLAny#Equal<T>(stk: Seq BoxType,o1:T,o2:T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=2;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	o1 == o2
  )));
  
procedure OCLAny#IsTypeof(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=2;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	dtype($Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref) == $Unbox(Seq#Index(stk,Seq#Length(stk)-1)): ClassName
  )));  
  
procedure OCLAny#IsKindof(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk)>=2;
  ensures (newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(
	dtype($Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref) <: $Unbox(Seq#Index(stk,Seq#Length(stk)-1)): ClassName
  )));  
  
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
  



// ---------------------------------------------------------------
// -- OCL: Bag, 2 operations                 ---------------------
// ---------------------------------------------------------------
procedure OCL#Bag#AsBag<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 1;
  ensures newStk == stk;

procedure OCL#Bag#Including<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);


  
procedure OCL#Bag#Excluding<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);  


  
procedure OCL#Bag#Flatten<T> (stk: Seq BoxType, b: MultiSet T) returns (newStk: Seq BoxType);  

