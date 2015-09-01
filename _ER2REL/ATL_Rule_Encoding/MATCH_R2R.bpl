/*
rule R2R { 
  from s : ER!Relship to t : REL!Relation ( name  <- s.name )}
*/

function printGuard_R2R(hp: HeapType, s: ref): bool
{  true  }

procedure R2R_matchAllTest() returns ();
  requires (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$Relship 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(s)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall s: ref ::
s!=null && read($srcHeap, s, alloc) && dtype(s) <: ER$Relship 
 ==>
 true  ==>
getTarsBySrcs(Seq#Singleton(s)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)
&& dtype(getTarsBySrcs(Seq#Singleton(s))) <: REL$Relation);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: REL$Relation) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$Relship && $f==alloc )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);


implementation R2R_matchAllTest() returns ()
{

var stk: Seq BoxType;
var $newCol: ref;
var s: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var $counter#5: int;
var obj#11: ref;
var obj#23: ref;
stk := OpCode#Aux#InitStk();

call stk := OpCode#Push(stk, _Relship);
call stk := OpCode#Push(stk, _ER);
call stk := OpCode#Findme(stk);
call stk := OpCode#Push(stk, _IN);
call stk, obj#4 := LIB#AllInstanceFrom(stk, $srcHeap);
obj#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
$counter#5:=0;
call stk := OpCode#Pop(stk);
while($counter#5<Seq#Length(obj#4)) 
invariant $counter#5 <= Seq#Length(obj#4);
invariant (forall _s: ref :: _s != null && read($srcHeap, _s, alloc) && dtype(_s) <: ER$Relship ==> Seq#Contains(obj#4,_s));
invariant (forall _$counter#5: int :: 0<= _$counter#5 && _$counter#5< $counter#5 ==> true ==> (Seq#Index(obj#4,_$counter#5)!=null && read($srcHeap, Seq#Index(obj#4,_$counter#5), alloc) && dtype(Seq#Index(obj#4,_$counter#5)) <: ER$Relship ==>printGuard_R2R($srcHeap,Seq#Index(obj#4,_$counter#5)) ==> getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,_$counter#5))) != null &&read($tarHeap, getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,_$counter#5))), alloc) && dtype(getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,_$counter#5)))) <: REL$Relation));
invariant (forall<alpha> $o : ref, $f: Field alpha :: ($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || ((dtype($o) <: REL$Relation) && Seq#Length(getTarsBySrcs_inverse($o)) == 1 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: ER$Relship && $f==alloc )));
{ stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $counter#5)));
call stk, s := OpCode#Store(stk);
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
call stk := OpCode#Push(stk, _R2R);
call stk := NTransientLink#setRule(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _s);
call stk := OpCode#Load(stk, s);
call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Dup(stk);
call stk := OpCode#Push(stk, _t);
call stk := OpCode#Push(stk, _Relation);
call stk := OpCode#Push(stk, _REL);
assert Seq#Length(stk) >= 2;
havoc obj#23;
assume obj#23!= null && !read($tarHeap, obj#23, alloc) && dtype(obj#23) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
$tarHeap := update($tarHeap, obj#23, alloc, true);
assume $IsGoodHeap($tarHeap);
assume $HeapSucc(old($tarHeap), $tarHeap);
assume getTarsBySrcs(Seq#Singleton(s)) == obj#23;
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#23));

call stk := NTransientLink#addTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
call stk := OpCode#Pusht(stk);
stk := Seq#Take(stk, Seq#Length(stk)-3);
$counter#5 := $counter#5+1;
}

}




	
