procedure RS2RS_matchAllTest() returns ();
  requires (forall rs1: ref :: rs1!=null && read($srcHeap, rs1, alloc) && dtype(rs1) <: HSM$RegularState 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(rs1)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(rs1)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall rs1: ref ::
rs1!=null && read($srcHeap, rs1, alloc) && dtype(rs1) <: HSM$RegularState 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(rs1)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(rs1)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(rs1))) <: FSM$RegularState);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$RegularState) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$RegularState && $f==alloc )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);

  
implementation RS2RS_matchAllTest () returns ()
{

var stk: Seq BoxType;
var $i: int;
var rs1: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var obj#11: ref;
var obj#23: ref;
stk := OpCode#Aux#InitStk();

call stk := OpCode#Push(stk, _RegularState);
call stk := OpCode#Push(stk, _HSM);
call stk := OpCode#Findme(stk);
call stk := OpCode#Push(stk, _IN);
call stk, obj#4 := LIB#AllInstanceFrom(stk, $srcHeap);
obj#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
$i:=0;
call stk := OpCode#Pop(stk);
while($i<Seq#Length(obj#4))
	  invariant $i<=Seq#Length(obj#4);
	  invariant (forall _rs1: ref ::
		_rs1!=null && read($srcHeap, _rs1, alloc) && dtype(_rs1) <: HSM$RegularState ==> Seq#Contains(obj#4,_rs1));
	  invariant (forall i: int:: 0<=i &&i <$i ==>
			true ==>
			(
				Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) <: HSM$RegularState ==> 
					getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i))), alloc)
					&& dtype(getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))) <: FSM$RegularState
			)
		);
	  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) <: FSM$RegularState && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$RegularState && $f==alloc)));
      free invariant $HeapSucc(old($tarHeap), $tarHeap);
      free invariant $HeapSucc(old($linkHeap), $linkHeap);
{ 
	stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $i)));
	call stk, rs1 := OpCode#Store(stk);
	call stk := OpCode#GetASM(stk);
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	assert read($linkHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
	assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: System.reserved;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($linkHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$links): Field (Set ref))));
	call stk := OpCode#Push(stk, _TransientLink);
	call stk := OpCode#Push(stk, _#native);
	assert Seq#Length(stk) >= 2;
	havoc obj#11;
	assume obj#11!= null && !read($linkHeap, obj#11, alloc) && dtype(obj#11) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
	$linkHeap := update($linkHeap, obj#11, alloc, true);
	assume $IsGoodHeap($linkHeap);
	assume $HeapSucc(old($linkHeap), $linkHeap);
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#11));

	call stk := OpCode#Dup(stk);
	call stk := OpCode#Push(stk, _RS2RS);
	call stk := NTransientLink#setRule(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	call stk := OpCode#Dup(stk);
	call stk := OpCode#Push(stk, _rs1);
	call stk := OpCode#Load(stk, rs1);
	call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	call stk := OpCode#Dup(stk);
	call stk := OpCode#Push(stk, _rs2);
	call stk := OpCode#Push(stk, _RegularState);
	call stk := OpCode#Push(stk, _FSM);
	assert Seq#Length(stk) >= 2;
	havoc obj#23;
	assume obj#23!= null && !read($tarHeap, obj#23, alloc) && dtype(obj#23) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
	$tarHeap := update($tarHeap, obj#23, alloc, true);
	assume $IsGoodHeap($tarHeap);
	assume $HeapSucc(old($tarHeap), $tarHeap);
	assume getTarsBySrcs(Seq#Singleton(rs1)) == obj#23;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#23));

	call stk := NTransientLink#addTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	call stk := OpCode#Pusht(stk);
	stk := Seq#Take(stk, Seq#Length(stk)-3);
	$i := $i+1;
}

}
