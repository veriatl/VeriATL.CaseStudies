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
