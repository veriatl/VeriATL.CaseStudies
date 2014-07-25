/*
rule R2R { 
from 
	s : ER!Relship 
to 
	t : REL!Relation 
	( name  <- s.name, 
	  schema <- s.schema  )
}

*/
procedure __matchR2R () returns ()
  requires (forall o1: ref :: 
    typeof(o1) == ER$Relship && Heap[o1, alloc] &&
	true ==> 
	!(Heap[o1,proc]) 
  );
  modifies Heap;
  ensures (forall o1: ref:: typeof(o1) == ER$Relship && old(Heap[o1, alloc]) ==>
			true ==>
			Heap[getSrcLink(o1), alloc] &&
			Heap[getSrcLink(o1), TransientLink#rule] == _R2R && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_s] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_s] == o1 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$Relation 
		);
{

var localStack: Seq BoxType;
var $i: int;
var s: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var obj#11: ref;
var obj#23: ref;
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#Push(localStack, _Relship);
call localStack := OpCode#Push(localStack, _ER);
call localStack := OpCode#Findme(localStack);
call localStack := OpCode#Push(localStack, _IN);
call localStack, obj#4 := LIB#AllInstanceFrom(localStack, old(Heap));
obj#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#4))
  invariant $i<=Seq#Length(obj#4);
  invariant (forall i: int:: 0<=i &&i <$i ==>
		(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$Relship),o) ==>
			true ==>
			(
				Heap[getSrcLink(Seq#Index(obj#4,i)), alloc] &&
				Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#rule] == _R2R && 
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_s] &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_s] == Seq#Index(obj#4,i) &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t] &&
				Heap[Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t], alloc] &&
				typeof(Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t]) == REL$Relation 
			)
		));

{ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#4, $i)));
call localStack, s := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _TransientLink);
call localStack := OpCode#Push(localStack, _#native);
havoc obj#11;
assume !Heap[obj#11, alloc];
call localStack := OpCode#New(localStack, obj#11);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _R2R);
call localStack := NTransientLink#setRule(localStack);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _s);
call localStack := OpCode#Load(localStack, s);
call localStack := NTransientLink#addSourceElement(localStack);
assume getSrcLink(s) == obj#11;
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _t);
call localStack := OpCode#Push(localStack, _Relation);
call localStack := OpCode#Push(localStack, _REL);
havoc obj#23;
assume !Heap[obj#23, alloc];
call localStack := OpCode#New(localStack, obj#23);
call localStack := NTransientLink#addTargetElement(localStack);
call localStack := OpCode#Pusht(localStack);
localStack := Seq#Take(localStack, Seq#Length(localStack)-3);
Heap := update(Heap, Seq#Index(obj#4,$i), proc, true);
$i := $i+1;
}

assert (forall o1: ref:: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$Relship),o1) ==>
			true ==>
			Heap[getSrcLink(o1), alloc] &&
			Heap[getSrcLink(o1), TransientLink#rule] == _R2R && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_s] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_s] == o1 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$Relation 
		);


}