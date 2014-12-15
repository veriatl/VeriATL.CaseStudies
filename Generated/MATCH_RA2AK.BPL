/*
rule RA2AK { from att : ER!ERAttribute, rse : ER!RelshipEnd 
	           ( att.entity = rse.entity and att.isKey = true )
	to   t : REL!RELAttribute 
	         ( name <- att.name, isKey <- att.isKey, relation <- rse.relship )}
*/

procedure RA2AK_match();
requires (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			(forall rse: ref :: rse!=null && read($srcHeap, rse, alloc) && dtype(rse) == ER$RelshipEnd ==> 
				($srcHeap[att, ERAttribute.entity] == $srcHeap[rse, RelshipEnd.entity] && $srcHeap[att, ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse))==null || !read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), alloc)));
modifies $tarHeap,$linkHeap;
ensures (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			 (forall rse: ref :: rse!=null && read($srcHeap, rse, alloc) && dtype(rse) == ER$RelshipEnd ==> 
				($srcHeap[att, ERAttribute.entity] == $srcHeap[rse, RelshipEnd.entity] && $srcHeap[att, ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse))!=null && read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)), alloc)));
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$RelshipEnd && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

implementation RA2AK_match () returns ()
{
var stk: Seq BoxType;
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

stk := OpCode#Aux#InitStk();

call stk := OpCode#Push(stk, _ERAttribute);
call stk := OpCode#Push(stk, _ER);
call stk := OpCode#Findme(stk);
call stk := OpCode#Push(stk, _IN);
call stk, obj#4 := LIB#AllInstanceFrom(stk, old($srcHeap));

obj#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
$i:=0;
call stk := OpCode#Pop(stk);

while($i<Seq#Length(obj#4))
  invariant $i<=Seq#Length(obj#4);
  invariant (forall i: int:: 0<=i &&i <$i ==>			
		Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) == ER$ERAttribute		
  );
  invariant (forall i: int:: 0<=i &&i <$i ==>			
			Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) == ER$ERAttribute ==>
			(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$RelshipEnd),o) ==>		
			o!=null && read($srcHeap, o, alloc) && dtype(o) == ER$RelshipEnd	==>
				($srcHeap[Seq#Index(obj#4,i), ERAttribute.entity] == $srcHeap[o, RelshipEnd.entity] && $srcHeap[Seq#Index(obj#4,i), ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o)), alloc)
			));
  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$RelshipEnd && $f==alloc)));
{ 
	stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $i)));
	call stk, att := OpCode#Store(stk);
	call stk := OpCode#Push(stk, _RelshipEnd);
	call stk := OpCode#Push(stk, _ER);
	call stk := OpCode#Findme(stk);
	call stk := OpCode#Push(stk, _IN);
	call stk, obj#11 := LIB#AllInstanceFrom(stk, old($srcHeap));
	obj#11 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
	$j:=0;
	call stk := OpCode#Pop(stk);

	
	while($j<Seq#Length(obj#11))
	  invariant $j<=Seq#Length(obj#11);
	  invariant (forall j: int:: 0<=j &&j <$j ==>			
		Seq#Index(obj#11,j)!=null && read($srcHeap, Seq#Index(obj#11,j), alloc) && dtype(Seq#Index(obj#11,j)) == ER$RelshipEnd		
	  );
	  invariant (forall j: int:: 0<=j &&j <$j ==>			
			Seq#Index(obj#11,j)!=null && read($srcHeap, Seq#Index(obj#11,j), alloc) && dtype(Seq#Index(obj#11,j)) == ER$RelshipEnd	==>
				($srcHeap[Seq#Index(obj#4,$i), ERAttribute.entity] == $srcHeap[Seq#Index(obj#11,j), RelshipEnd.entity] && $srcHeap[Seq#Index(obj#4,$i), ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)))!=null && read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j))), alloc)
			);
	  invariant (forall i: int:: 0<=i &&i <$i ==>			
			Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) == ER$ERAttribute ==>
			(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$RelshipEnd),o) ==>		
			o!=null && read($srcHeap, o, alloc) && dtype(o) == ER$RelshipEnd ==>
				($srcHeap[Seq#Index(obj#4,i), ERAttribute.entity] == $srcHeap[o, RelshipEnd.entity] && $srcHeap[Seq#Index(obj#4,i), ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o)), alloc)
			));
	  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$RelshipEnd && $f==alloc)));
	{ 
		stk := Seq#Build(stk, $Box(Seq#Index(obj#11, $j)));
		call stk, rse := OpCode#Store(stk);
		

		/* filter starts */
		
		call stk := OpCode#Load(stk, att);
		assert Seq#Length(stk) >= 1;
		assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
		stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$entity): Field (ref)]));
			
		//assert $Unbox(top(stk)) == $srcHeap[att, ERAttribute.entity];
		
		call stk := OpCode#Load(stk, rse);
		assert Seq#Length(stk) >= 1;
		assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
		stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$entity): Field (ref)]));
			
		//assert $Unbox(top(stk)) == $srcHeap[rse, RelshipEnd.entity];
		
		call stk := OCL#Object#Equal(stk, $Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref, $Unbox(Seq#Index(stk,Seq#Length(stk)-1)): ref);
		
		call stk := OpCode#Load(stk, att);
		assert Seq#Length(stk) >= 1;
		assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
		stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$isKey): Field (bool)]));
		
		call stk := OpCode#Pusht(stk);
		call stk := OCL#Object#Equal(stk, $Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref, $Unbox(Seq#Index(stk,Seq#Length(stk)-1)): ref);
		
		call stk := OCL#Boolean#And(stk);
		call stk := OCL#Boolean#Not(stk);
			

		cond#25 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
		call stk := OpCode#Pop(stk);
		
		/* filter ends */
		
		goto label_26, label_50;
		label_26:
			assume !cond#25;

			//assert $srcHeap[att, ERAttribute.relship] == rse;
			
			call stk := OpCode#GetASM(stk);
			
			assert Seq#Length(stk) >= 1;
			assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
			stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($linkHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$links): Field (Set ref)]));
			
			call stk := OpCode#Push(stk, _TransientLink);
			call stk := OpCode#Push(stk, _#native);
			
			// new
			assert Seq#Length(stk) >= 2;
			havoc obj#30;
			assume obj#30 != null && !read($linkHeap, obj#30, alloc) && dtype(obj#30) == 
			classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
							($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
			$linkHeap := update($linkHeap, obj#30, alloc, true);
			assume $IsGoodHeap($linkHeap);
			assume $HeapSucc(old($linkHeap), $linkHeap);
			stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#30));
			
			
			call stk := OpCode#Dup(stk);
			call stk := OpCode#Push(stk, _EA2A);
			
			call stk := NTransientLink#setRule
			(stk, 
			$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
			$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
			
			call stk := OpCode#Dup(stk);
			call stk := OpCode#Push(stk, _att);
			call stk := OpCode#Load(stk, att);
			
			call stk := NTransientLink#addSourceElement
			(stk, 
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-3)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));

			call stk := OpCode#Dup(stk);
			call stk := OpCode#Push(stk, _rse);
			call stk := OpCode#Load(stk, rse);
			
			call stk := NTransientLink#addSourceElement
			(stk, 
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-3)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));

			call stk := OpCode#Dup(stk);
			call stk := OpCode#Push(stk, _t);
			call stk := OpCode#Push(stk, _RELAttribute);
			call stk := OpCode#Push(stk, _REL);

			// new
			assert Seq#Length(stk) >= 2;
			havoc obj#46;
			assume obj#46 != null && !read($tarHeap, obj#46, alloc) && dtype(obj#46) == 
			classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
							($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
			$tarHeap := update($tarHeap, obj#46, alloc, true);
			assume $IsGoodHeap($tarHeap);
			assume $HeapSucc(old($tarHeap), $tarHeap);
			assume getTarsBySrcs(Seq#Build(Seq#Singleton(att),rse)) == obj#46;
			stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#46));
			
			
			call stk := NTransientLink#addTargetElement
			(stk, 
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-3)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
			
			
			call stk := OpCode#Pusht(stk);
			stk := Seq#Take(stk, Seq#Length(stk)-3);
			goto done;
		label_50:
			assume cond#25; 
			goto done;
			
		done:
			$j := $j+1;
		
		
		
	}

	$i := $i+1;
	
}

assert (forall p: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$ERAttribute),p) ==>			
			p!=null && read($srcHeap, p, alloc) && dtype(p) == ER$ERAttribute ==>
			(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$RelshipEnd),o) ==>		
			o!=null && read($srcHeap, o, alloc) && dtype(o) == ER$RelshipEnd	==>
				($srcHeap[p, ERAttribute.entity] == $srcHeap[o, RelshipEnd.entity] && $srcHeap[p, ERAttribute.isKey]) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(p),o))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(p),o)), alloc)
			));

}