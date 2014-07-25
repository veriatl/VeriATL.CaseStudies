/*
rule RA2AK { from att : ER!ERAttribute, rse : ER!RelshipEnd 
	           ( att.entity = rse.entity and att.isKey = true )
	to   t : REL!RELAttribute 
	         ( name <- att.name, isKey <- att.isKey, relation <- rse.relship )}
*/

procedure __matchRA2AK () returns ()
  requires (forall o1, o2: ref :: 
    typeof(o1) == ER$ERAttribute && Heap[o1, alloc] &&
	typeof(o2) == ER$RelshipEnd && Heap[o2, alloc] &&
	(Heap[o1, ERAttribute.entity] == Heap[o2, RelshipEnd.entity] && Heap[o1, ERAttribute.isKey]) ==> 
	!(Heap[o1,proc] || Heap[o2,proc]) 
  );
  modifies Heap;
  ensures (forall o1: ref:: typeof(o1) == ER$ERAttribute && old(Heap[o1, alloc]) ==>
		(forall o2: ref :: typeof(o2) == ER$RelshipEnd && old(Heap)[o2, alloc] ==> 
			(Heap[o1, ERAttribute.entity]==Heap[o2, RelshipEnd.entity] && Heap[o1, ERAttribute.isKey]) ==>
			Heap[getSrcLink(o1), alloc] &&
			getSrcLink(o1) == getSrcLink(o2) &&
			Heap[getSrcLink(o1), TransientLink#rule] == _RA2AK && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_att] &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_rse] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_att] == o1 &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_rse] == o2 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELAttribute 
		));
{

	var localStack: Seq BoxType;
	var $i: int;
	var $j: int;
	var att: ref;	//slot: 1
	var rse: ref;	//slot: 2
	var self: ref;	//slot: 0
	var obj#4: Seq ref;
	var obj#11: Seq ref;
	var cond#25: bool;
	var obj#30: ref;
	var obj#46: ref;
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
		(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$RelshipEnd),o) ==>
			(Heap[Seq#Index(obj#4,i), ERAttribute.entity]==Heap[o, RelshipEnd.entity] && Heap[Seq#Index(obj#4,i), ERAttribute.isKey]) ==>
			(
				Heap[getSrcLink(Seq#Index(obj#4,i)), alloc] &&
				getSrcLink(Seq#Index(obj#4,i)) == getSrcLink(o) &&
				Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#rule] == _RA2AK && 
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_rse] &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] == Seq#Index(obj#4,i) &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_rse] == o &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t] &&
				Heap[Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t], alloc] &&
				typeof(Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t]) == REL$RELAttribute 
			)
		));
	{ 
		localStack := Seq#Build(localStack, $Box(Seq#Index(obj#4, $i)));
		call localStack, att := OpCode#Store(localStack);
		call localStack := OpCode#Push(localStack, _RelshipEnd);
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
			(Heap[Seq#Index(obj#4,$i), ERAttribute.entity]==Heap[Seq#Index(obj#11,j), RelshipEnd.entity] && Heap[Seq#Index(obj#4,$i), ERAttribute.isKey]) ==>
			Heap[Seq#Index(obj#11,j), proc]
		  );
			// important one
		  invariant (forall j: int :: 0<=j &&j < $j ==> 
			(Heap[Seq#Index(obj#4,$i), ERAttribute.entity]==Heap[Seq#Index(obj#11,j), RelshipEnd.entity] && Heap[Seq#Index(obj#4,$i), ERAttribute.isKey]) ==>
			(
				Heap[getSrcLink(Seq#Index(obj#4,$i)), alloc] &&
				getSrcLink(Seq#Index(obj#4,$i)) == getSrcLink(Seq#Index(obj#11,j)) &&
				Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#rule] == _RA2AK && 
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_att] &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_rse] &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_att] == Seq#Index(obj#4,$i) &&
				Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#source])[_rse] == Seq#Index(obj#11,j) &&
				Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#target])[_t] &&
				Heap[Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#target])[_t], alloc] &&
				typeof(Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,$i)), TransientLink#target])[_t]) == REL$RELAttribute 
				
			)
		  );
		  invariant (forall i: int:: 0<=i &&i <$i ==>
			(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$RelshipEnd),o) ==>
				(Heap[Seq#Index(obj#4,i), ERAttribute.entity]==Heap[o, RelshipEnd.entity] && Heap[Seq#Index(obj#4,i), ERAttribute.isKey]) ==>
				(
					Heap[getSrcLink(Seq#Index(obj#4,i)), alloc] &&
					getSrcLink(Seq#Index(obj#4,i)) == getSrcLink(o) &&
					Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#rule] == _RA2AK && 
					Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] &&
					Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_rse] &&
					Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_att] == Seq#Index(obj#4,i) &&
					Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#source])[_rse] == o &&
					Map#Domain(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t] &&
					Heap[Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t], alloc] &&
					typeof(Map#Elements(Heap[getSrcLink(Seq#Index(obj#4,i)), TransientLink#target])[_t]) == REL$RELAttribute 
				)
			));
		{ 
			localStack := Seq#Build(localStack, $Box(Seq#Index(obj#11, $j)));
			call localStack, rse := OpCode#Store(localStack);
			call localStack := OpCode#Load(localStack, att);
			call localStack := OpCode#Get(localStack,_Field$entity);
			call localStack := OpCode#Load(localStack, rse);
			call localStack := OpCode#Get(localStack,_Field$entity);
			call localStack := OCL#Object#Equal(localStack, $Unbox(Seq#Index(localStack,Seq#Length(localStack)-2)): ref, $Unbox(Seq#Index(localStack,Seq#Length(localStack)-1)): ref);
			call localStack := OpCode#Load(localStack, att);
			call localStack := OpCode#Get(localStack,_Field$isKey);
			call localStack := OpCode#Pusht(localStack);
			call localStack := OCL#Object#Equal(localStack, $Unbox(Seq#Index(localStack,Seq#Length(localStack)-2)): bool, $Unbox(Seq#Index(localStack,Seq#Length(localStack)-1)): bool);
			call localStack := OCL#Boolean#And(localStack);
			call localStack := OCL#Boolean#Not(localStack);
			cond#25 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
			call localStack := OpCode#Pop(localStack);
			goto label_26, label_50;
			label_26:
				assume !cond#25;
				call localStack := OpCode#GetASM(localStack);
				call localStack := OpCode#Get(localStack,_Field$links);
				call localStack := OpCode#Push(localStack, _TransientLink);
				call localStack := OpCode#Push(localStack, _#native);
				havoc obj#30;
				assume !Heap[obj#30, alloc];
				call localStack := OpCode#New(localStack, obj#30);
				call localStack := OpCode#Dup(localStack);
				call localStack := OpCode#Push(localStack, _RA2AK);
				call localStack := NTransientLink#setRule(localStack);
				call localStack := OpCode#Dup(localStack);
				call localStack := OpCode#Push(localStack, _att);
				call localStack := OpCode#Load(localStack, att);
				call localStack := NTransientLink#addSourceElement(localStack);
					assume getSrcLink(att) == obj#30;
				call localStack := OpCode#Dup(localStack);
				call localStack := OpCode#Push(localStack, _rse);
				call localStack := OpCode#Load(localStack, rse);
				call localStack := NTransientLink#addSourceElement(localStack);
					assume getSrcLink(rse) == obj#30;
				call localStack := OpCode#Dup(localStack);
				call localStack := OpCode#Push(localStack, _t);
				call localStack := OpCode#Push(localStack, _RELAttribute);
				call localStack := OpCode#Push(localStack, _REL);
				havoc obj#46;
				assume !Heap[obj#46, alloc];
				call localStack := OpCode#New(localStack, obj#46);
				call localStack := NTransientLink#addTargetElement(localStack);
				call localStack := OpCode#Pusht(localStack);
				localStack := Seq#Take(localStack, Seq#Length(localStack)-3);
				Heap := update(Heap, Seq#Index(obj#4,$i), proc, true);
				Heap := update(Heap, Seq#Index(obj#11,$j), proc, true);
				goto done;
			label_50:
				assume cond#25;
				goto done;
			done:
				$j := $j+1;
		}
	$i := $i+1;
	}

	
assert (forall o1: ref:: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$ERAttribute),o1) ==>
		(forall o2: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$RelshipEnd),o2) ==>
			(Heap[o1, ERAttribute.entity]==Heap[o2, RelshipEnd.entity] && Heap[o1, ERAttribute.isKey]) ==>
			Heap[getSrcLink(o1), alloc] &&
			getSrcLink(o1) == getSrcLink(o2) &&
			Heap[getSrcLink(o1), TransientLink#rule] == _RA2AK && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_att] &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_rse] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_att] == o1 &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_rse] == o2 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELAttribute 
		));
			


assert (forall o1: ref:: typeof(o1) == ER$ERAttribute && old(Heap[o1, alloc]) ==>
		(forall o2: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old(Heap),ER$RelshipEnd),o2) ==> 
			typeof(o2) == ER$RelshipEnd && old(Heap)[o2, alloc] ==> 
			(Heap[o1, ERAttribute.entity]==Heap[o2, RelshipEnd.entity] && Heap[o1, ERAttribute.isKey]) ==>
			Heap[getSrcLink(o1), alloc] &&
			getSrcLink(o1) == getSrcLink(o2) &&
			Heap[getSrcLink(o1), TransientLink#rule] == _RA2AK && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_att] &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_rse] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_att] == o1 &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_rse] == o2 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELAttribute 
		));
}