   
procedure testBoolean () returns ()
{
var localStk : Seq BoxType;

localStk := OpCode#Aux#InitStk();
localStk := Seq#Build(localStk, $Box(false));
call localStk := OCL#Boolean#Not(localStk);
assert $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1));		// stk: true

localStk := Seq#Build(localStk, $Box(true));		// stk: true::true
call localStk := OCL#Boolean#Implies(localStk);
assert Seq#Length(localStk) == 1;
assert $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1));	
}

procedure testSet () returns ()
{
var localStk : Seq BoxType;
var set : Set int;
// test including
localStk := OpCode#Aux#InitStk();
localStk := Seq#Build(localStk, $Box(Set#Singleton(1)));
localStk := Seq#Build(localStk, $Box(2));
call localStk := OCL#Set#Including(localStk, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-2)):Set int, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1)):int);
assert Seq#Length(localStk) == 1;
set := $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1));		// stk: {1,2}

// test SymetricDifference
localStk := Seq#Build(localStk, $Box(Set#Singleton(1)));
localStk := Seq#Build(localStk, $Box(3));
call localStk := OCL#Set#Including(localStk, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-2)):Set int, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1)):int);										// stk: {1,2}::{1,3}
call localStk := OCL#Set#SymetricDifference(localStk, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-2)):Set int, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1)):Set int);								// stk: {2,3}
set := $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1));
assert !set[1];

}  

procedure testSeq () returns ()
{
var localStk : Seq BoxType;
var seq : Seq int;
// test Append
localStk := OpCode#Aux#InitStk();
localStk := Seq#Build(localStk, $Box(Seq#Singleton(1)));
localStk := Seq#Build(localStk, $Box(1));
call localStk := OCL#OrderSet#Append(localStk, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-2)):Seq int, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1)):int);
seq := $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1));		// stk: {1}
assert Seq#Index(Seq#Singleton(1),0) == 1;						// needed for present the element existence in the seq.
assert Seq#Length(seq) == 1;

//test insertAt
call localStk := OpCode#Pop(localStk);
localStk := Seq#Build(localStk, $Box(Seq#Append(Seq#Append(Seq#Singleton(1), 
														   Seq#Singleton(2)),
												Seq#Singleton(3))));
localStk := Seq#Build(localStk, $Box(2));		// index to be insert
localStk := Seq#Build(localStk, $Box(4));		// elem
call localStk := OCL#OrderSet#InsertAt(localStk, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-3)):Seq int, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-2)):int, $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1)):int);
seq := $Unbox(Seq#Index(localStk,Seq#Length(localStk)-1));	
assert Seq#Index(seq,2) == 4;	
assert Seq#Index(seq,3) == 3;					// stk: {1,2,4,3}

}  