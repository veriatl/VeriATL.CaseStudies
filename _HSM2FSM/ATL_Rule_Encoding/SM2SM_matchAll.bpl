procedure SM2SM_matchAllTest() returns ();
  requires (forall sm1: ref :: sm1!=null && read($srcHeap, sm1, alloc) && dtype(sm1) <: HSM$StateMachine 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(sm1)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(sm1)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall sm1: ref ::
sm1!=null && read($srcHeap, sm1, alloc) && dtype(sm1) <: HSM$StateMachine 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(sm1)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(sm1)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(sm1))) <: FSM$StateMachine);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$StateMachine) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$StateMachine && $f==alloc )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);

function printGuard_SM2SM(hp: HeapType, sm1: ref): bool
{  true  }
  

implementation SM2SM_matchAllTest() returns ()
{

var stk: Seq BoxType;
var $newCol: ref;
var sm1: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var $counter#5: int;
var obj#11: ref;
var obj#23: ref;
stk := OpCode#Aux#InitStk();

call stk := OpCode#Push(stk, _StateMachine);
call stk := OpCode#Push(stk, _HSM);
call stk := OpCode#Findme(stk);
call stk := OpCode#Push(stk, _IN);
call stk, obj#4 := LIB#AllInstanceFrom(stk, $srcHeap);
obj#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
$counter#5:=0;
call stk := OpCode#Pop(stk);
while($counter#5<Seq#Length(obj#4)) 
invariant $counter#5 <= Seq#Length(obj#4);
invariant (forall _sm1: ref :: _sm1 != null && read($srcHeap, _sm1, alloc) && dtype(_sm1) <: HSM$StateMachine ==> Seq#Contains(obj#4,_sm1));
invariant (forall _$counter#5: int :: 0<= _$counter#5 && _$counter#5< $counter#5 ==> true ==> (Seq#Index(obj#4,_$counter#5)!=null && read($srcHeap, Seq#Index(obj#4,_$counter#5), alloc) && dtype(Seq#Index(obj#4,_$counter#5)) <: HSM$StateMachine ==>printGuard_SM2SM($srcHeap,Seq#Index(obj#4,_$counter#5)) ==> getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,_$counter#5))) != null &&read($tarHeap, getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,_$counter#5))), alloc) && dtype(getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,_$counter#5)))) <: FSM$StateMachine));
invariant (forall<alpha> $o : ref, $f: Field alpha :: ($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || ((dtype($o) <: FSM$StateMachine) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$StateMachine && $f==alloc )));
{ stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $counter#5)));
call stk, sm1 := OpCode#Store(stk);
call stk := OpCode#GetASM(stk);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($linkHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),ASM.links)));
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
call stk := OpCode#Push(stk, _SM2SM);
call stk := NTransientLink#setRule(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _sm1);
call stk := OpCode#Load(stk, sm1);
call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _sm2);
call stk := OpCode#Push(stk, _StateMachine);
call stk := OpCode#Push(stk, _FSM);
assert Seq#Length(stk) >= 2;
havoc obj#23;
assume obj#23!= null && !read($tarHeap, obj#23, alloc) && dtype(obj#23) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
$tarHeap := update($tarHeap, obj#23, alloc, true);
assume $IsGoodHeap($tarHeap);
assume $HeapSucc(old($tarHeap), $tarHeap);
assume getTarsBySrcs(Seq#Singleton(sm1)) == obj#23;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#23));

call stk := NTransientLink#addTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Pusht(stk);
stk := Seq#Take(stk, Seq#Length(stk)-3);
$counter#5 := $counter#5+1;
}

}
