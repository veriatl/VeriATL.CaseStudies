procedure IS2RS_matchAllTest() returns ();
  requires (forall is1: ref :: is1!=null && read($srcHeap, is1, alloc) && dtype(is1) <: HSM$InitialState 
 ==>
 !(read($srcHeap, is1, HSM$AbstractState.compositeState)==null)  ==>
getTarsBySrcs(Seq#Singleton(is1)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(is1)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall is1: ref ::
is1!=null && read($srcHeap, is1, alloc) && dtype(is1) <: HSM$InitialState 
 ==>
 !(read($srcHeap, is1, HSM$AbstractState.compositeState)==null)  ==>
getTarsBySrcs(Seq#Singleton(is1)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(is1)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(is1))) <: FSM$RegularState);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$RegularState) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$InitialState && $f==alloc )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);
  
implementation IS2RS_matchAllTest () returns ()
{

var stk: Seq BoxType;
var $i: int;
var is1: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var cond#12: bool;
var obj#17: ref;
var obj#29: ref;
stk := OpCode#Aux#InitStk();

call stk := OpCode#Push(stk, _InitialState);
call stk := OpCode#Push(stk, _HSM);
call stk := OpCode#Findme(stk);
call stk := OpCode#Push(stk, _IN);
call stk, obj#4 := LIB#AllInstanceFrom(stk, $srcHeap);
obj#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
$i:=0;
call stk := OpCode#Pop(stk);
while($i<Seq#Length(obj#4))
	  invariant $i<=Seq#Length(obj#4);
	  invariant (forall _is1: ref ::
		_is1!=null && read($srcHeap, _is1, alloc) && dtype(_is1) <: HSM$InitialState ==> Seq#Contains(obj#4,_is1));
	  invariant (forall i: int:: 0<=i &&i <$i ==>
			true ==>
			(
				Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) <: HSM$InitialState ==> 
					!(read($srcHeap, Seq#Index(obj#4,i), HSM$AbstractState.compositeState)==null)  ==>
					getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i))), alloc)
					&& dtype(getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))) <: FSM$RegularState
			)
		);
	  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$RegularState) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$InitialState && $f==alloc )));
      free invariant $HeapSucc(old($tarHeap), $tarHeap);
      free invariant $HeapSucc(old($linkHeap), $linkHeap);
{ 
stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $i)));
call stk, is1 := OpCode#Store(stk);
call stk := OpCode#Load(stk, is1);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$compositeState): Field (ref))));
call stk := OCLAny#IsUndefined(stk);
call stk := OCLAny#Not(stk);
call stk := OCL#Boolean#Not(stk);
cond#12 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
call stk := OpCode#Pop(stk);
if(cond#12){goto label_33;}
label_13:
call stk := OpCode#GetASM(stk);
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($linkHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($linkHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$links): Field (Set ref))));
call stk := OpCode#Push(stk, _TransientLink);
call stk := OpCode#Push(stk, _#native);
assert Seq#Length(stk) >= 2;
havoc obj#17;
assume obj#17!= null && !read($linkHeap, obj#17, alloc) && dtype(obj#17) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
$linkHeap := update($linkHeap, obj#17, alloc, true);
assume $IsGoodHeap($linkHeap);
assume $HeapSucc(old($linkHeap), $linkHeap);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#17));

call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _IS2RS);
call stk := NTransientLink#setRule(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _is1);
call stk := OpCode#Load(stk, is1);
call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _is2);
call stk := OpCode#Push(stk, _RegularState);
call stk := OpCode#Push(stk, _FSM);
assert Seq#Length(stk) >= 2;
havoc obj#29;
assume obj#29!= null && !read($tarHeap, obj#29, alloc) && dtype(obj#29) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
$tarHeap := update($tarHeap, obj#29, alloc, true);
assume $IsGoodHeap($tarHeap);
assume $HeapSucc(old($tarHeap), $tarHeap);
assume getTarsBySrcs(Seq#Singleton(is1)) == obj#29;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#29));

call stk := NTransientLink#addTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Pusht(stk);
stk := Seq#Take(stk, Seq#Length(stk)-3);
label_33:
$i := $i+1;
}

}
