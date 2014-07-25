/*
rule EA2A { 
from 
	att : ER!ERAttribute, 
	ent : ER!Entity 
	(att.entity = ent)
to t : REL!RELAttribute 
	( name <- att.name, 
	  isKey <- att.isKey, 
	  relation <- ent ) 
}
 */


  
procedure __matchEA2A () returns ();
  requires (forall o1, o2: ref :: 
    typeof(o1) == ER$ERAttribute && Heap[o1, alloc] &&
	typeof(o2) == ER$Entity && Heap[o2, alloc] &&
	Heap[o1, ERAttribute.entity] == o2 ==> 
	!(Heap[o1,proc] || Heap[o2,proc]) 
  );
  modifies Heap;
  ensures (forall o1: ref:: typeof(o1) == ER$ERAttribute && old(Heap[o1, alloc]) ==>
		(forall o2: ref :: typeof(o2) == ER$Entity && old(Heap)[o2, alloc] ==> 
			Heap[o1, ERAttribute.entity]==o2 ==>
			Heap[getSrcLink(o1), alloc] &&
			getSrcLink(o1) == getSrcLink(o2) &&
			Heap[getSrcLink(o1), TransientLink#rule] == _EA2A && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_att] &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_ent] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_att] == o1 &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_ent] == o2 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELAttribute 
		));


implementation __matchEA2A () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var $j: int;
var att: ref;	//slot: 1
var ent: ref;	//slot: 2
var self: ref;	//slot: 0
var obj#4: Seq ref;
var obj#11: Seq ref;
var cond#19: bool;
var obj#24: ref;
var obj#40: ref;

localStack := OpCode#Aux#InitStk();

call localStack := OpCode#Push(localStack, _ERAttribute);
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
		(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$Entity),o) ==>
			Heap[Seq#Index(obj#4,i), ERAttribute.entity]==o ==>
			(
				Heap[getSrcLink(Seq#Index(obj#4,i)), alloc] &&
				getSrcLink(Seq#Index(obj#4,i)) == getSrcLink(o) &&
				Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#rule] == _EA2A && 
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_ent] &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] == Seq#Index(obj#4,i) &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_ent] == o &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t] &&
				Heap[Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t], alloc] &&
				typeof(Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t]) == REL$RELAttribute 
			)
		));
{ 
	localStack := Seq#Build(localStack, $Box(Seq#Index(obj#4, $i)));
	call localStack, att := OpCode#Store(localStack);
	call localStack := OpCode#Push(localStack, _Entity);
	call localStack := OpCode#Push(localStack, _ER);
	call localStack := OpCode#Findme(localStack);
	call localStack := OpCode#Push(localStack, _IN);
	call localStack, obj#11 := LIB#AllInstanceFrom(localStack, old(Heap));
	obj#11 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
	$j:=0;
	call localStack := OpCode#Pop(localStack);

	
	while($j<Seq#Length(obj#11))
	  invariant $j<=Seq#Length(obj#11);
	  invariant (forall j: int :: 0<=j &&j < $j ==> 
		Heap[Seq#Index(obj#4,$i), ERAttribute.entity]==Seq#Index(obj#11,j) ==>
		Heap[Seq#Index(obj#11,j), proc]
	  );
	  // important one
	  invariant (forall j: int :: 0<=j &&j < $j ==> 
		Heap[Seq#Index(obj#4,$i), ERAttribute.entity]==Seq#Index(obj#11,j) ==>
			(
				Heap[getSrcLink(Seq#Index(obj#4,$i)), alloc] &&
				getSrcLink(Seq#Index(obj#4,$i)) == getSrcLink(Seq#Index(obj#11,j)) &&
				Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#rule] == _EA2A && 
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_att] &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_ent] &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_att] == Seq#Index(obj#4,$i) &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_ent] == Seq#Index(obj#11,j) &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#target])[_t] &&
				Heap[Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#target])[_t], alloc] &&
				typeof(Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#target])[_t]) == REL$RELAttribute 
				
			)
		);
	  // bridge invariant from outer loop
	  invariant (forall i: int:: 0<=i &&i <$i ==>
		(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$Entity),o) ==>
			Heap[Seq#Index(obj#4,i), ERAttribute.entity]==o ==>
			(
				Heap[getSrcLink(Seq#Index(obj#4,i)), alloc] &&
				getSrcLink(Seq#Index(obj#4,i)) == getSrcLink(o) &&
				Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#rule] == _EA2A && 
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_ent] &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] == Seq#Index(obj#4,i) &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_ent] == o &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t] &&
				Heap[Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t], alloc] &&
				typeof(Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t]) == REL$RELAttribute 
			)
		));
	{ 
		localStack := Seq#Build(localStack, $Box(Seq#Index(obj#11, $j)));
		call localStack, ent := OpCode#Store(localStack);
		call localStack := OpCode#Load(localStack, att);
		call localStack := OpCode#Get(localStack,_Field$entity);
		
		// assert $Unbox(top(localStack)) == Heap[att, ERAttribute.entity];
		
		call localStack := OpCode#Load(localStack, ent);
		call localStack := OCL#Object#Equal(localStack, $Unbox(Seq#Index(localStack,Seq#Length(localStack)-2)): ref, $Unbox(Seq#Index(localStack,Seq#Length(localStack)-1)): ref);
		call localStack := OCL#Boolean#Not(localStack);
		cond#19 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
		call localStack := OpCode#Pop(localStack);
		goto label_20, label_44;
		label_20:
			assume !cond#19;

			// assert Heap[att, ERAttribute.entity] == ent;
			
			call localStack := OpCode#GetASM(localStack);
			call localStack := OpCode#Get(localStack,_Field$links);
			call localStack := OpCode#Push(localStack, _TransientLink);
			call localStack := OpCode#Push(localStack, _#native);
			havoc obj#24;
			assume !Heap[obj#24, alloc];
			call localStack := OpCode#New(localStack, obj#24);
			call localStack := OpCode#Dup(localStack);
			call localStack := OpCode#Push(localStack, _EA2A);
			call localStack := NTransientLink#setRule(localStack);
			call localStack := OpCode#Dup(localStack);
			call localStack := OpCode#Push(localStack, _att);
			call localStack := OpCode#Load(localStack, att);
			call localStack := NTransientLink#addSourceElement(localStack);
			assume getSrcLink(att) == obj#24;
			assert Map#Elements(Heap[obj#24, TransientLink#source])[_att] == att; 
			call localStack := OpCode#Dup(localStack);
			call localStack := OpCode#Push(localStack, _ent);
			call localStack := OpCode#Load(localStack, ent);
			call localStack := NTransientLink#addSourceElement(localStack);
			assume getSrcLink(ent) == obj#24;
			assert Map#Elements(Heap[obj#24, TransientLink#source])[_att] == att; 
			call localStack := OpCode#Dup(localStack);
			call localStack := OpCode#Push(localStack, _t);
			call localStack := OpCode#Push(localStack, _RELAttribute);
			call localStack := OpCode#Push(localStack, _REL);
			havoc obj#40;
			assume !Heap[obj#40, alloc];
			call localStack := OpCode#New(localStack, obj#40);
			call localStack := NTransientLink#addTargetElement(localStack);
			call localStack := OpCode#Pusht(localStack);
			localStack := Seq#Take(localStack, Seq#Length(localStack)-3);
			Heap := update(Heap, Seq#Index(obj#4,$i), proc, true);
			Heap := update(Heap, Seq#Index(obj#11,$j), proc, true);
			goto done;
		label_44:
			assume cond#19; 
			goto done;
			
		done:
			$j := $j+1;
		// TODO seems work without proper block transformation for if statment.
	}

	$i := $i+1;
	
}


assert (forall o1: ref:: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$ERAttribute),o1) ==>
		(forall o2: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$Entity),o2) ==>
			Heap[o1, ERAttribute.entity]==o2 ==>
			Heap[getSrcLink(o1), alloc] &&
			getSrcLink(o1) == getSrcLink(o2) &&
			Heap[getSrcLink(o1), TransientLink#rule] == _EA2A && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_att] &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_ent] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_att] == o1 &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_ent] == o2 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELAttribute 
		));
			
// assert (forall o1: ref:: typeof(o1) == ER$ERAttribute && old(Heap[o1, alloc]) ==>
		// (forall o2: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$Entity),o2) ==>
			// Heap[o1, ERAttribute.entity]==o2 ==>
			// Heap[getSrcLink(o1), alloc] &&
			// getSrcLink(o1) == getSrcLink(o2) &&
			// Heap[getSrcLink(o1), TransientLink#rule] == _EA2A && 
			// Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_att] &&
			// Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_ent] &&
			// Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_att] == o1 &&
			// Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_ent] == o2 &&
			// Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			// Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			// typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELAttribute 
		// ));

assert (forall o1: ref:: typeof(o1) == ER$ERAttribute && old(Heap[o1, alloc]) ==>
		(forall o2: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$Entity),o2) ==> 
			typeof(o2) == ER$Entity && old(Heap)[o2, alloc] ==> 
			Heap[o1, ERAttribute.entity]==o2 ==>
			Heap[getSrcLink(o1), alloc] &&
			getSrcLink(o1) == getSrcLink(o2) &&
			Heap[getSrcLink(o1), TransientLink#rule] == _EA2A && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_att] &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_ent] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_att] == o1 &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_ent] == o2 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELAttribute 
		));


	
			
			
}



  