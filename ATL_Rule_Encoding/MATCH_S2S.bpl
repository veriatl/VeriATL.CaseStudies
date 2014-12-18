/*
rule S2S { 
  from s : ER!ERSchema to t : REL!RELSchema ( name  <- s.name, relations <-s.entities, relations <-s.relships)}
*/



procedure S2S_match();
requires (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$ERSchema ==> 
		getTarsBySrcs(Seq#Singleton(s))==null || !read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc));
modifies $tarHeap,$linkHeap;
ensures (forall s: ref :: s!=null && read($srcHeap, s, alloc) && dtype(s) == ER$ERSchema ==> 
		getTarsBySrcs(Seq#Singleton(s))!=null 
		&& read($tarHeap, getTarsBySrcs(Seq#Singleton(s)), alloc)
		&& dtype(getTarsBySrcs(Seq#Singleton(s))) == REL$RELSchema
		);
ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELSchema && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERSchema && $f==alloc)));
free ensures $HeapSucc(old($tarHeap), $tarHeap);
free ensures $HeapSucc(old($linkHeap), $linkHeap);
free ensures surj_tar_model($srcHeap, $tarHeap);

implementation S2S_match () returns ()
{

var stk: Seq BoxType;
var $i: int;
var s: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var obj#11: ref;
var obj#23: ref;


stk := OpCode#Aux#InitStk();


call stk := OpCode#Push(stk, _ERSchema);
call stk := OpCode#Push(stk, _ER);
call stk := OpCode#Findme(stk);
call stk := OpCode#Push(stk, _IN);
call stk, obj#4 := LIB#AllInstanceFrom(stk, $srcHeap);


assert (forall i: ref :: i!=null && read($srcHeap, i, alloc) && dtype(i) == ER$ERSchema ==> Seq#Contains(obj#4,i)); // test contaiment of allinstance function




$i:=0;
call stk := OpCode#Pop(stk);
while($i<Seq#Length(obj#4))
  invariant $i<=Seq#Length(obj#4);
  invariant (forall i: int:: 0<=i &&i <$i ==>
			true ==>
			(
				Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) == ER$ERSchema ==> 
					getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))!=null 
					&& read($tarHeap, getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i))), alloc)
					&& dtype(getTarsBySrcs(Seq#Singleton(Seq#Index(obj#4,i)))) == REL$RELSchema
			)
		);
  invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null || read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) || (dtype($o) == REL$RELSchema && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) == ER$ERSchema && $f==alloc)));
  free invariant $HeapSucc(old($tarHeap), $tarHeap);
  free invariant $HeapSucc(old($linkHeap), $linkHeap);
{ 
	
	stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $i)));
	call stk, s := OpCode#Store(stk);
	
	// placed just after the condition check.

	
	call stk := OpCode#GetASM(stk);
	
	assert Seq#Length(stk) >= 1;
	assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box($linkHeap[$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$links): Field (Set ref)]));

	
	
	
	
	call stk := OpCode#Push(stk, _TransientLink);
	call stk := OpCode#Push(stk, _#native);

	assert Seq#Length(stk) >= 2;
	havoc obj#11;
    assume obj#11 != null && !read($linkHeap, obj#11, alloc) && dtype(obj#11) == 
	classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
					($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
	$linkHeap := update($linkHeap, obj#11, alloc, true);
	assume $IsGoodHeap($linkHeap);
	assume $HeapSucc(old($linkHeap), $linkHeap);
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#11));

	call stk := OpCode#Dup(stk);
	call stk := OpCode#Push(stk, _S2S);
	
	call stk := NTransientLink#setRule
	(stk, 
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));

	call stk := OpCode#Dup(stk);
	call stk := OpCode#Push(stk, _s);
	call stk := OpCode#Load(stk, s);
	
	call stk := NTransientLink#addSourceElement
	(stk, 
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-3)),
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));

	call stk := OpCode#Dup(stk);
	call stk := OpCode#Push(stk, _t);
	call stk := OpCode#Push(stk, _RELSchema);
	call stk := OpCode#Push(stk, _REL);
	
	assert Seq#Length(stk) >= 2;
	havoc obj#23;
    assume obj#23 != null && !read($tarHeap, obj#23, alloc) && dtype(obj#23) == 
	classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
					($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
	$tarHeap := update($tarHeap, obj#23, alloc, true);
	assume $IsGoodHeap($tarHeap);
	assume $HeapSucc(old($tarHeap), $tarHeap);
	assume getTarsBySrcs(Seq#Singleton(s)) == obj#23;
	stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#23));
	
	
	
	
	call stk := NTransientLink#addTargetElement
	(stk, 
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-3)),
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-2)),
	 $Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
	
	assert $linkHeap[obj#11, TransientLink#rule] == _S2S;
	assert Map#Elements($linkHeap[obj#11, TransientLink#target])[_t] == obj#23;
	assert Map#Elements($linkHeap[obj#11, TransientLink#source])[_s] == s;
	
	
	call stk := OpCode#Pusht(stk);
	stk := Seq#Take(stk, Seq#Length(stk)-3);
	$i := $i+1;
	
	assert $HeapSucc(old($tarHeap), $tarHeap);
	assert $HeapSucc(old($linkHeap), $linkHeap);


	
}
}



