
var $tempHeap : HeapType;

const unique _TransientLink : String;
const unique _#native : String;
const unique _Sequence : String;

const unique class._System.Integer: ClassName;
const unique class._System.Boolean: ClassName;
const unique class._System.String: ClassName;

function toRef<T>(x: T): ref;
  axiom (forall i: int :: dtype(toRef(i)) == class._System.Integer);
  axiom (forall b: bool :: dtype(toRef(b)) == class._System.Boolean);
  axiom (forall s: String :: dtype(toRef(s)) == class._System.String);

function unRef<T>(x: ref): T;
  axiom (forall i: int :: unRef(toRef(i)) == i);
  axiom (forall i: bool :: unRef(toRef(i)) == i);
  axiom (forall i: String :: unRef(toRef(i)) == i);

function isResolved(x: ref): bool;  
  
procedure NTransientLink#getTargetFromSource
	(stk:Seq BoxType, src: ref)
returns
	(newStk:Seq BoxType);
requires Seq#Length(stk) >= 1; 
ensures Seq#Length(stk) == Seq#Length(newStk);
ensures Seq#Equal(
	Seq#Take(stk, Seq#Length(stk)-1),
	Seq#Take(newStk, Seq#Length(newStk)-1)
);
ensures $Unbox(Seq#Index(newStk, Seq#Length(newStk)-1)) == getTarsBySrcs(Seq#Singleton(src));
	


function NTransientLink#getLinkBySourceElement#Spec(links: Set ref, src: ref): ref;

procedure Collection#Including
  (stk: Seq BoxType) 
returns
  (newStk: Seq BoxType);
requires dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2))) == class._System.array;
modifies $tempHeap;
ensures newStk == Seq#Take(stk, Seq#Length(stk)-2);
ensures dtype($Unbox(Seq#Index(newStk, Seq#Length(newStk)-1))) == dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-2)));
ensures Seq#FromArray($tempHeap, $Unbox(Seq#Index(newStk, Seq#Length(newStk)-1))) == 
			Seq#Build(
				Seq#FromArray(old($tempHeap), $Unbox(Seq#Index(stk, Seq#Length(stk)-2))),
				Seq#Index(stk, Seq#Length(stk)-1));
ensures (forall<alpha> $o: ref, $f: Field alpha ::  
	$o != $Unbox(Seq#Index(newStk, Seq#Length(newStk)-1)) ==> 
		read($tempHeap, $o, $f) == read(old($tempHeap), $o, $f));
	
procedure NTransientLink#getLinkBySourceElement
	(stk:Seq BoxType, links: Set ref, src: ref)
returns
	(newStk:Seq BoxType);
requires Seq#Length(stk) >= 2; 
ensures Seq#Length(stk) == Seq#Length(newStk)+1;
ensures Seq#Equal(
	Seq#Take(stk, Seq#Length(stk)-2),
	Seq#Take(newStk, Seq#Length(newStk)-1)
);
ensures $Unbox(Seq#Index(newStk, Seq#Length(newStk)-1)) == NTransientLink#getLinkBySourceElement#Spec(links, src);


procedure __resolve__(this: ref, obj: ref) returns (r: ref)
modifies $tempHeap;
ensures dtype(obj) != class._System.array && NTransientLink#getLinkBySourceElement#Spec(read($linkHeap,Asm,ASM.links), obj) == null
==> r == obj;
ensures dtype(obj) != class._System.array && !(NTransientLink#getLinkBySourceElement#Spec(read($linkHeap,Asm,ASM.links), obj) == null || !read($linkHeap, NTransientLink#getLinkBySourceElement#Spec(read($linkHeap,Asm,ASM.links), obj), alloc))
==> r == getTarsBySrcs(Seq#Singleton(obj));
ensures dtype(obj) == class._System.array ==> dtype(r) == class._System.array ;
ensures dtype(obj) == class._System.array ==> Seq#Length(Seq#FromArray($srcHeap, obj)) == Seq#Length(Seq#FromArray($tempHeap, r));
ensures dtype(obj) == class._System.array ==> 
	(forall __i: int :: 0<=__i && __i<Seq#Length(Seq#FromArray($srcHeap, obj)) ==>
		isResolved($Unbox(Seq#Index(Seq#FromArray($srcHeap, obj),__i))));
ensures dtype(obj) != class._System.array && !(NTransientLink#getLinkBySourceElement#Spec(read($linkHeap,Asm,ASM.links), obj) == null || !read($linkHeap, NTransientLink#getLinkBySourceElement#Spec(read($linkHeap,Asm,ASM.links), obj), alloc))
==> (old($tempHeap) == $tempHeap);
{

var stk: Seq BoxType;
var e: BoxType;	//slot: 2
var value: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#22: Seq BoxType;
var obj#26: ref;
var $counter#23: int;

var obj#20: ref;
var cond#4: bool;
var cond#11: bool;

var _heap: HeapType;
var _col: ref;


self := this;
value := obj;

stk := OpCode#Aux#InitStk();

// 0:	load 1 
call stk := OpCode#Load(stk, value);
// 1:	getasm 
call stk := OpCode#GetASM(stk);
// 2:	get col 
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(class._System.array));
// 3:	call J.oclIsKindOf(J):B 
call stk := OCLAny#IsTypeof(stk);
// 4:	if 18 
cond#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
call stk := OpCode#Pop(stk);
if(cond#4){goto label_18;}
// 5:	getasm 
call stk := OpCode#GetASM(stk);
// 6:	get links 
assert Seq#Length(stk) >= 1;
assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
assert read($linkHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($linkHeap,Asm,ASM.links)));
// 7:	load 1 
call stk := OpCode#Load(stk, value);
// 8:	call NTransientLinkSet;.getLinkBySourceElement(S):QNTransientLink; 
call stk := NTransientLink#getLinkBySourceElement(
	stk,
	$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
	$Unbox(Seq#Index(stk, Seq#Length(stk)-1))
);
// 9:	dup 
call stk := OpCode#Dup(stk);
// 10:	call J.oclIsUndefined():B 
call stk := OCLAny#IsUndefined(stk,$linkHeap);
// 11:	if 15 
cond#11 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
call stk := OpCode#Pop(stk);
if(cond#11){goto label_15;}
// 12:	load 1 
call stk := OpCode#Load(stk, value);
// 13:	call NTransientLink;.getTargetFromSource(J):J 
call stk := NTransientLink#getTargetFromSource(
	stk,
	$Unbox(Seq#Index(stk, Seq#Length(stk)-1))
);
// 14:	goto 17 
goto label_17;
label_15:
// 15:	pop 
call stk := OpCode#Pop(stk);
// 16:	load 1 
call stk := OpCode#Load(stk, value);
label_17:
// 17:	goto 30 
goto label_30;
label_18:
// 18:	push Sequence 
call stk := OpCode#Push(stk, _Sequence);
// 19:	push #native 
call stk := OpCode#Push(stk, _#native);
// 20:	new 
assert Seq#Length(stk) >= 2;
havoc obj#20;
assume obj#20!= null && !read($tempHeap, obj#20, alloc) && dtype(obj#20) == class._System.array;
$tempHeap := update($tempHeap, obj#20, alloc, true);
assume $IsGoodHeap($tempHeap);
assume $HeapSucc(old($tempHeap), $tempHeap);
assume Seq#Length(Seq#FromArray($tempHeap, obj#20)) == 0;

stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#20));
// 21:	load 1 
call stk := OpCode#Load(stk, value);
// 22:	iterate 
obj#22 := Seq#FromArray($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));

$counter#23:=0;
call stk := OpCode#Pop(stk);

while($counter#23<Seq#Length(obj#22)) 
invariant $counter#23<=Seq#Length(obj#22);
invariant dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) == class._System.array;
invariant Seq#Length(Seq#FromArray($tempHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)))) == $counter#23;
invariant (forall __i: int :: 0<=__i && __i<$counter#23 ==>
		isResolved($Unbox(Seq#Index(obj#22, __i))));
invariant (forall __i: int :: 0<=__i && __i<$counter#23 ==>
	$Unbox(Seq#Index(Seq#FromArray($tempHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1))), __i))
		== getTarsBySrcs(Seq#Singleton($Unbox(Seq#Index(obj#22, __i)))));
{
	stk := Seq#Build(stk, $Box(Seq#Index(obj#22, $counter#23)));	
	// hack: assume every element in the array is ref and not array.
	assume !(NTransientLink#getLinkBySourceElement#Spec(read($linkHeap,Asm,ASM.links), $Unbox(Seq#Index(obj#22, $counter#23))) == null || !read($linkHeap, NTransientLink#getLinkBySourceElement#Spec(read($linkHeap,Asm,ASM.links), $Unbox(Seq#Index(obj#22, $counter#23))), alloc));
	assume dtype($Unbox(Seq#Index(obj#22, $counter#23))) != class._System.array;
	// 23:	store 2 
	call stk, e := OpCode#Store(stk);	
	// 24:	getasm 
	call stk := OpCode#GetASM(stk);
	// 25:	load 2 
	call stk := OpCode#Load(stk, e);	
	// 26:	call A.__resolve__(J):J 
	_heap := $tempHeap;		
	call obj#26 := __resolve__(this, $Unbox(e));
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#26));
	assume isResolved($Unbox(e));		
	// 27:	call QJ.including(J):QJ 
	call stk := Collection#Including(stk);
	// 28:	enditerate 
	$counter#23 := $counter#23+1;
	

}
// 29:	call QJ.flatten():QJ 
label_30:
	r := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
}