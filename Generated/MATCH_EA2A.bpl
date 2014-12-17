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



procedure EA2A_match();
requires (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			(forall ent: ref :: ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
				$srcHeap[att, ERAttribute.entity] == ent ==>
				getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent))==null || !read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), alloc)));
modifies $tarHeap,$linkHeap;
ensures (forall att: ref :: att!=null && read($srcHeap, att, alloc) && dtype(att) == ER$ERAttribute ==> 
			 (forall ent: ref :: ent!=null && read($srcHeap, ent, alloc) && dtype(ent) == ER$Entity ==> 
				$srcHeap[att, ERAttribute.entity] == ent ==>
				getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent))!=null && read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)), alloc)));
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Entity && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

implementation EA2A_match () returns ()
{
var stk: Seq BoxType;
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
			(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$Entity),o) ==>		
			o!=null && read($srcHeap, o, alloc) && dtype(o) == ER$Entity	==>
				$srcHeap[Seq#Index(obj#4,i), ERAttribute.entity] == o ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o)), alloc)
			));
  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Entity && $f==alloc)));
{ 
	stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $i)));
	call stk, att := OpCode#Store(stk);
	call stk := OpCode#Push(stk, _Entity);
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
		Seq#Index(obj#11,j)!=null && read($srcHeap, Seq#Index(obj#11,j), alloc) && dtype(Seq#Index(obj#11,j)) == ER$Entity		
	  );
	  invariant (forall j: int:: 0<=j &&j <$j ==>			
			Seq#Index(obj#11,j)!=null && read($srcHeap, Seq#Index(obj#11,j), alloc) && dtype(Seq#Index(obj#11,j)) == ER$Entity	==>
				$srcHeap[Seq#Index(obj#4,$i), ERAttribute.entity] == Seq#Index(obj#11,j) ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j))), alloc)
			);
	  invariant (forall i: int:: 0<=i &&i <$i ==>			
			Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) == ER$ERAttribute ==>
			(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$Entity),o) ==>		
			o!=null && read($srcHeap, o, alloc) && dtype(o) == ER$Entity	==>
				$srcHeap[Seq#Index(obj#4,i), ERAttribute.entity] == o ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),o)), alloc)
			));
	  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERAttribute && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) == ER$Entity && $f==alloc)));
	{ 
		stk := Seq#Build(stk, $Box(Seq#Index(obj#11, $j)));
		call stk, ent := OpCode#Store(stk);
		call stk := OpCode#Load(stk, att);

		
		assert Seq#Length(stk) >= 1;
		assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
		stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($srcHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$entity): Field (ref)]));
			
		//assert $Unbox(top(stk)) == $srcHeap[att, ERAttribute.entity];
		
		call stk := OpCode#Load(stk, ent);
		call stk := OCL#Object#Equal(stk, $Unbox(Seq#Index(stk,Seq#Length(stk)-2)): ref, $Unbox(Seq#Index(stk,Seq#Length(stk)-1)): ref);
		call stk := OCL#Boolean#Not(stk);
		cond#19 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
		call stk := OpCode#Pop(stk);
		goto label_20, label_44;
		label_20:
			assume !cond#19;

			//assert $srcHeap[att, ERAttribute.entity] == ent;
			
			call stk := OpCode#GetASM(stk);
			
			assert Seq#Length(stk) >= 1;
			assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
			stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($linkHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$links): Field (Set ref)]));
			
			call stk := OpCode#Push(stk, _TransientLink);
			call stk := OpCode#Push(stk, _#native);
			
			// new
			assert Seq#Length(stk) >= 2;
			havoc obj#24;
			assume obj#24 != null && !read($linkHeap, obj#24, alloc) && dtype(obj#24) == 
			classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
							($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
			$linkHeap := update($linkHeap, obj#24, alloc, true);
			assume $IsGoodHeap($linkHeap);
			assume $HeapSucc(old($linkHeap), $linkHeap);
			stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#24));
			
			
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
			call stk := OpCode#Push(stk, _ent);
			call stk := OpCode#Load(stk, ent);
			
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
			havoc obj#40;
			assume obj#40 != null && !read($tarHeap, obj#40, alloc) && dtype(obj#40) == 
			classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
							($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
			$tarHeap := update($tarHeap, obj#40, alloc, true);
			assume $IsGoodHeap($tarHeap);
			assume $HeapSucc(old($tarHeap), $tarHeap);
			assume getTarsBySrcs(Seq#Build(Seq#Singleton(att),ent)) == obj#40;
			stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#40));
			
			
			call stk := NTransientLink#addTargetElement
			(stk, 
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-3)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
			 $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
			
			
			call stk := OpCode#Pusht(stk);
			stk := Seq#Take(stk, Seq#Length(stk)-3);
			goto done;
		label_44:
			assume cond#19; 
			goto done;
			
		done:
			$j := $j+1;
		
		
		
	}

	$i := $i+1;
	
}

assert (forall p: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$ERAttribute),p) ==>			
			p!=null && read($srcHeap, p, alloc) && dtype(p) == ER$ERAttribute ==>
			(forall o: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),ER$Entity),o) ==>		
			o!=null && read($srcHeap, o, alloc) && dtype(o) == ER$Entity	==>
				$srcHeap[p, ERAttribute.entity] == o ==>
					getTarsBySrcs(Seq#Build(Seq#Singleton(p),o))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Singleton(p),o)), alloc)
			));

}


