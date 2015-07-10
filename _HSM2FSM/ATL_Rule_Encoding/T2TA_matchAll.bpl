procedure T2TA_matchAllTest() returns ();
  requires (forall t1: ref :: t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 ==>
 !(dtype(read($srcHeap, t1, HSM$Transition.source)) == HSM$CompositeState) && !(dtype(read($srcHeap, t1, HSM$Transition.target)) == HSM$CompositeState)  ==>
getTarsBySrcs(Seq#Singleton(t1)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(t1)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall t1: ref ::
t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 ==>
 !(dtype(read($srcHeap, t1, HSM$Transition.source)) == HSM$CompositeState) && !(dtype(read($srcHeap, t1, HSM$Transition.target)) == HSM$CompositeState)  ==>
getTarsBySrcs(Seq#Singleton(t1)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(t1)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(t1))) <: FSM$Transition);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$Transition) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && $f==alloc )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);
  
implementation T2TA_matchAllTest () returns ()
{

	var stk: Seq BoxType;
	var $i: int;
	var t1: ref;	//slot: 1
	var self: ref;	//slot: 0
	var obj#4: Seq ref;
	var cond#23: bool;
	var obj#28: ref;
	var obj#40: ref;
	stk := OpCode#Aux#InitStk();

	call stk := OpCode#Push(stk, _Transition);
	call stk := OpCode#Push(stk, _HSM);
	call stk := OpCode#Findme(stk);
	call stk := OpCode#Push(stk, _IN);
	call stk, obj#4 := LIB#AllInstanceFrom(stk, $srcHeap);
	obj#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
	$i:=0;
	call stk := OpCode#Pop(stk);
	while($i<Seq#Length(obj#4))
	  invariant $i<=Seq#Length(obj#4);
	  invariant (forall _t1: ref ::
		_t1!=null && read($srcHeap, _t1, alloc) && dtype(_t1) <: HSM$Transition ==> Seq#Contains(obj#4,_t1));
	  invariant (forall i: int:: 0<=i &&i <$i ==>
			true ==>
			(
				Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) <: HSM$Transition ==> 
				 !(dtype(read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.source)) == HSM$CompositeState) && !(dtype(read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.target)) == HSM$CompositeState)  ==>
					getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i))), alloc)
					&& dtype(getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))) <: FSM$Transition
			)
		);
	  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$Transition) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && $f==alloc )));
      free invariant $HeapSucc(old($tarHeap), $tarHeap);
      free invariant $HeapSucc(old($linkHeap), $linkHeap);
	{ 
stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $i)));
call stk, t1 := OpCode#Store(stk);
call stk := OpCode#Load(stk, t1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$source): Field (ref))));
call stk := OpCode#Push(stk, _CompositeState);
call stk := OpCode#Push(stk, _HSM);
call stk := OpCode#Findme(stk);
call stk := OCLAny#IsTypeof(stk);
call stk := OCLAny#Not(stk);
call stk := OpCode#Load(stk, t1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$target): Field (ref))));
call stk := OpCode#Push(stk, _CompositeState);
call stk := OpCode#Push(stk, _HSM);
assert ($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) == _CompositeState;
call stk := OpCode#Findme(stk);
call stk := OCLAny#IsTypeof(stk);
call stk := OCLAny#Not(stk);
call stk := OCLAny#And(stk);
call stk := OCL#Boolean#Not(stk);
cond#23 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
call stk := OpCode#Pop(stk);
if(cond#23){goto label_44;}
label_24:
call stk := OpCode#GetASM(stk);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($linkHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($linkHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$links): Field (Set ref))));
call stk := OpCode#Push(stk, _TransientLink);
call stk := OpCode#Push(stk, _#native);
assert Seq#Length(stk) >= 2;
havoc obj#28;
assume obj#28!= null && !read($linkHeap, obj#28, alloc) && dtype(obj#28) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
$linkHeap := update($linkHeap, obj#28, alloc, true);
assume $IsGoodHeap($linkHeap);
assume $HeapSucc(old($linkHeap), $linkHeap);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#28));

call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _T2TA);
call stk := NTransientLink#setRule(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _t1);
call stk := OpCode#Load(stk, t1);
call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _t2);
call stk := OpCode#Push(stk, _Transition);
call stk := OpCode#Push(stk, _FSM);
assert Seq#Length(stk) >= 2;
havoc obj#40;
assume obj#40!= null && !read($tarHeap, obj#40, alloc) && dtype(obj#40) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
$tarHeap := update($tarHeap, obj#40, alloc, true);
assume $IsGoodHeap($tarHeap);
assume $HeapSucc(old($tarHeap), $tarHeap);
assume getTarsBySrcs(Seq#Singleton(t1)) == obj#40;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#40));

call stk := NTransientLink#addTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Pusht(stk);
stk := Seq#Take(stk, Seq#Length(stk)-3);
label_44:
$i := $i+1;
	}

}
