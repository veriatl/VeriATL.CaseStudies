procedure T2TB_matchAllTest() returns ();
  requires (forall t1,src,trg,c: ref :: t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)) ==null || !read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)), alloc)); 
  modifies $tarHeap,$linkHeap;
// Rule Outcome
  ensures (forall t1,src,trg,c: ref ::
t1!=null && read($srcHeap, t1, alloc) && dtype(t1) <: HSM$Transition 
 && src!=null && read($srcHeap, src, alloc) && dtype(src) <: HSM$CompositeState 
 && trg!=null && read($srcHeap, trg, alloc) && dtype(trg) <: HSM$AbstractState 
 && c!=null && read($srcHeap, c, alloc) && dtype(c) <: HSM$AbstractState 
 ==>
 read($srcHeap, t1, HSM$Transition.source) == src && read($srcHeap, t1, HSM$Transition.target) == trg && read($srcHeap, c, HSM$AbstractState.compositeState) == src && !(dtype(trg) == HSM$CompositeState)  ==>
getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)) !=null 
&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)), alloc)
&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c))) <: FSM$Transition);
// Frame Condition
  ensures (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$Transition) && Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && $f==alloc )));
  free ensures $HeapSucc(old($tarHeap), $tarHeap);
  free ensures $HeapSucc(old($linkHeap), $linkHeap);
  free ensures surj_tar_model($srcHeap, $tarHeap);
  
implementation T2TB_matchAllTest () returns ()
{

var stk: Seq BoxType;
var $i: int;
var $j: int;
var $k: int;
var $l: int;
var t1: ref;	//slot: 1
var src: ref;	//slot: 2
var trg: ref;	//slot: 3
var c: ref;	//slot: 4
var self: ref;	//slot: 0
var obj#4: Seq ref;
var obj#11: Seq ref;
var obj#18: Seq ref;
var obj#25: Seq ref;
var cond#50: bool;
var obj#55: ref;
var obj#79: ref;
stk := OpCode#Aux#InitStk();

call stk := OpCode#Push(stk, _Transition);
call stk := OpCode#Push(stk, _HSM);
call stk := OpCode#Findme(stk);
call stk := OpCode#Push(stk, _IN);
call stk, obj#4 := LIB#AllInstanceFrom(stk, $srcHeap);
obj#4 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
$i:=0;
$j:=0;
$k:=0;
$l:=0;
call stk := OpCode#Pop(stk);
while($i<Seq#Length(obj#4))
 invariant $i<=Seq#Length(obj#4);
 invariant (forall _t1: ref ::
	_t1!=null && read($srcHeap, _t1, alloc) && dtype(_t1) <: HSM$Transition ==> Seq#Contains(obj#4,_t1));
 invariant (forall i: int:: 0<=i &&i <$i ==>
  true ==>(
    Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) <: HSM$Transition ==> 
	  (forall __src, __trg, __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$CompositeState),__src) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__trg) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.source) == __src 
		 && read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.target) == __trg 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == __src 
		 && !(dtype(__trg) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))) <: FSM$Transition
		)
));
 invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$Transition) && Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && $f==alloc )));

{ 
	stk := Seq#Build(stk, $Box(Seq#Index(obj#4, $i)));
	call stk, t1 := OpCode#Store(stk);
	call stk := OpCode#Push(stk, _CompositeState);
	call stk := OpCode#Push(stk, _HSM);
	call stk := OpCode#Findme(stk);
	call stk := OpCode#Push(stk, _IN);
	call stk, obj#11 := LIB#AllInstanceFrom(stk, $srcHeap);
	obj#11 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
	$j:=0;
	call stk := OpCode#Pop(stk);
	while($j<Seq#Length(obj#11))
	 invariant $j<=Seq#Length(obj#11);
	 invariant (forall _t1: ref ::
	_t1!=null && read($srcHeap, _t1, alloc) && dtype(_t1) <: HSM$Transition ==> Seq#Contains(obj#4,_t1));
	 invariant (forall _src: ref ::
	_src!=null && read($srcHeap, _src, alloc) && dtype(_src) <: HSM$CompositeState ==> Seq#Contains(obj#11,_src));
	 invariant (forall j: int:: 0<=j &&j <$j ==>
  true ==>(
    Seq#Index(obj#11,j)!=null && read($srcHeap, Seq#Index(obj#11,j), alloc) && dtype(Seq#Index(obj#11,j)) <: HSM$CompositeState ==> 
	  (forall __trg, __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__trg) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.source) == Seq#Index(obj#11,j) 
		 && read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.target) == __trg 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == Seq#Index(obj#11,j) 
		 && !(dtype(__trg) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c))) <: FSM$Transition
		)
));
	   invariant (forall i: int:: 0<=i &&i <$i ==>
  true ==>(
    Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) <: HSM$Transition ==> 
	  (forall __src, __trg, __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$CompositeState),__src) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__trg) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.source) == __src 
		 && read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.target) == __trg 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == __src 
		 && !(dtype(__trg) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))) <: FSM$Transition
		)
));
	 invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$Transition) && Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && $f==alloc )));	
	{ 
		stk := Seq#Build(stk, $Box(Seq#Index(obj#11, $j)));
		call stk, src := OpCode#Store(stk);
		call stk := OpCode#Push(stk, _AbstractState);
		call stk := OpCode#Push(stk, _HSM);
		call stk := OpCode#Findme(stk);
		call stk := OpCode#Push(stk, _IN);
		call stk, obj#18 := LIB#AllInstanceFrom(stk, $srcHeap);
		obj#18 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
		$k:=0;
		call stk := OpCode#Pop(stk);
		while($k<Seq#Length(obj#18))
 invariant $k<=Seq#Length(obj#18);
 invariant (forall _t1: ref ::
	_t1!=null && read($srcHeap, _t1, alloc) && dtype(_t1) <: HSM$Transition ==> Seq#Contains(obj#4,_t1));
 invariant (forall _src: ref ::
	_src!=null && read($srcHeap, _src, alloc) && dtype(_src) <: HSM$CompositeState ==> Seq#Contains(obj#11,_src));
 invariant (forall _trg: ref ::
	_trg!=null && read($srcHeap, _trg, alloc) && dtype(_trg) <: HSM$AbstractState ==> Seq#Contains(obj#18,_trg));
 invariant (forall k: int:: 0<=k &&k <$k ==>
  true ==>(
    Seq#Index(obj#18,k)!=null && read($srcHeap, Seq#Index(obj#18,k), alloc) && dtype(Seq#Index(obj#18,k)) <: HSM$AbstractState ==> 
	  (forall __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.source) == Seq#Index(obj#11,$j) 
		 && read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.target) == Seq#Index(obj#18,k) 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == Seq#Index(obj#11,$j) 
		 && !(dtype(Seq#Index(obj#18,k)) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,k)),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,k)),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,k)),__c))) <: FSM$Transition
		)
));
 invariant (forall j: int:: 0<=j &&j <$j ==>
  true ==>(
    Seq#Index(obj#11,j)!=null && read($srcHeap, Seq#Index(obj#11,j), alloc) && dtype(Seq#Index(obj#11,j)) <: HSM$CompositeState ==> 
	  (forall __trg, __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__trg) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.source) == Seq#Index(obj#11,j) 
		 && read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.target) == __trg 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == Seq#Index(obj#11,j) 
		 && !(dtype(__trg) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c))) <: FSM$Transition
		)
));
 invariant (forall i: int:: 0<=i &&i <$i ==>
  true ==>(
    Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) <: HSM$Transition ==> 
	  (forall __src, __trg, __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$CompositeState),__src) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__trg) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.source) == __src 
		 && read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.target) == __trg 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == __src 
		 && !(dtype(__trg) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))) <: FSM$Transition
		)
));
 invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$Transition) && Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && $f==alloc )));	
		{ 
			stk := Seq#Build(stk, $Box(Seq#Index(obj#18, $k)));
			call stk, trg := OpCode#Store(stk);
			call stk := OpCode#Push(stk, _AbstractState);
			call stk := OpCode#Push(stk, _HSM);
			call stk := OpCode#Findme(stk);
			call stk := OpCode#Push(stk, _IN);
			call stk, obj#25 := LIB#AllInstanceFrom(stk, $srcHeap);
			obj#25 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
			$l:=0;
			call stk := OpCode#Pop(stk);
			while($l<Seq#Length(obj#25))
 invariant $l<=Seq#Length(obj#25);
 invariant (forall _t1: ref ::
	_t1!=null && read($srcHeap, _t1, alloc) && dtype(_t1) <: HSM$Transition ==> Seq#Contains(obj#4,_t1));
 invariant (forall _src: ref ::
	_src!=null && read($srcHeap, _src, alloc) && dtype(_src) <: HSM$CompositeState ==> Seq#Contains(obj#11,_src));
 invariant (forall _trg: ref ::
	_trg!=null && read($srcHeap, _trg, alloc) && dtype(_trg) <: HSM$AbstractState ==> Seq#Contains(obj#18,_trg));
 invariant (forall _c: ref ::
	_c!=null && read($srcHeap, _c, alloc) && dtype(_c) <: HSM$AbstractState ==> Seq#Contains(obj#25,_c));
 invariant (forall l: int:: 0<=l &&l <$l ==>
  true ==>(
    Seq#Index(obj#25,l)!=null && read($srcHeap, Seq#Index(obj#25,l), alloc) && dtype(Seq#Index(obj#25,l)) <: HSM$AbstractState ==> 		
	 read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.source) == Seq#Index(obj#11,$j) 
  && read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.target) == Seq#Index(obj#18,$k) 
  && read($srcHeap, Seq#Index(obj#25,l), HSM$AbstractState.compositeState) == Seq#Index(obj#11,$j) 
  && !(dtype(Seq#Index(obj#18,$k)) == HSM$CompositeState)  ==>
	getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,$k)),Seq#Index(obj#25,l)))!=null 
	&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,$k)),Seq#Index(obj#25,l))), alloc)
	&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,$k)),Seq#Index(obj#25,l)))) <: FSM$Transition	
));
 invariant (forall k: int:: 0<=k &&k <$k ==>
  true ==>(
    Seq#Index(obj#18,k)!=null && read($srcHeap, Seq#Index(obj#18,k), alloc) && dtype(Seq#Index(obj#18,k)) <: HSM$AbstractState ==> 
	  (forall __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.source) == Seq#Index(obj#11,$j) 
		 && read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.target) == Seq#Index(obj#18,k) 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == Seq#Index(obj#11,$j) 
		 && !(dtype(Seq#Index(obj#18,k)) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,k)),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,k)),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,$j)),Seq#Index(obj#18,k)),__c))) <: FSM$Transition
		)
));
 invariant (forall j: int:: 0<=j &&j <$j ==>
  true ==>(
    Seq#Index(obj#11,j)!=null && read($srcHeap, Seq#Index(obj#11,j), alloc) && dtype(Seq#Index(obj#11,j)) <: HSM$CompositeState ==> 
	  (forall __trg, __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__trg) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.source) == Seq#Index(obj#11,j) 
		 && read($srcHeap, Seq#Index(obj#4,$i), HSM$Transition.target) == __trg 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == Seq#Index(obj#11,j) 
		 && !(dtype(__trg) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,$i)),Seq#Index(obj#11,j)),__trg),__c))) <: FSM$Transition
		)
));
 invariant (forall i: int:: 0<=i &&i <$i ==>
  true ==>(
    Seq#Index(obj#4,i)!=null && read($srcHeap, Seq#Index(obj#4,i), alloc) && dtype(Seq#Index(obj#4,i)) <: HSM$Transition ==> 
	  (forall __src, __trg, __c: ref :: Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$CompositeState),__src) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__trg) && Seq#Contains(Fun#LIB#AllInstanceFrom(old($srcHeap),HSM$AbstractState),__c) ==>		
		 read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.source) == __src 
		 && read($srcHeap, Seq#Index(obj#4,i), HSM$Transition.target) == __trg 
		 && read($srcHeap, __c, HSM$AbstractState.compositeState) == __src 
		 && !(dtype(__trg) == HSM$CompositeState)  ==>
			getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))!=null 
			&& read($tarHeap, getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c)), alloc)
			&& dtype(getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(Seq#Index(obj#4,i)),__src),__trg),__c))) <: FSM$Transition
		)
));
 invariant (forall<alpha> $o : ref, $f: Field alpha ::
	($o == null 
	|| read($tarHeap, $o, $f) == read(old($tarHeap), $o, $f) 
	|| ((dtype($o) <: FSM$Transition) && Seq#Length(getTarsBySrcs_inverse($o)) == 4 && dtype(Seq#Index(getTarsBySrcs_inverse($o), 0)) <: HSM$Transition && dtype(Seq#Index(getTarsBySrcs_inverse($o), 1)) <: HSM$CompositeState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 2)) <: HSM$AbstractState && dtype(Seq#Index(getTarsBySrcs_inverse($o), 3)) <: HSM$AbstractState && $f==alloc )));				
			{ 
				stk := Seq#Build(stk, $Box(Seq#Index(obj#25, $l)));
				call stk, c := OpCode#Store(stk);
				call stk := OpCode#Load(stk, t1);
				assert Seq#Length(stk) >= 1;
				assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
				assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
				assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: HSM$Transition;
				stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$source): Field (ref))));
				call stk := OpCode#Load(stk, src);
				call stk := OCLAny#Equal(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)):ref,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)):ref);
				call stk := OpCode#Load(stk, t1);
				assert Seq#Length(stk) >= 1;
				assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
				assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
				assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: HSM$Transition;
				stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$target): Field (ref))));
				call stk := OpCode#Load(stk, trg);
				call stk := OCLAny#Equal(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)):ref,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)):ref);
				call stk := OCLAny#And(stk);
				call stk := OpCode#Load(stk, c);
				assert Seq#Length(stk) >= 1;
				assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
				assert read($srcHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
				assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: HSM$AbstractState;
				stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($srcHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)), HSM$AbstractState.compositeState)));
				call stk := OpCode#Load(stk, src);
				
				call stk := OCLAny#Equal(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)):ref,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)):ref);
				call stk := OCLAny#And(stk);
				call stk := OpCode#Load(stk, trg);
				call stk := OpCode#Push(stk, _CompositeState);
				call stk := OpCode#Push(stk, _HSM);
				call stk := OpCode#Findme(stk);
				call stk := OCLAny#IsTypeof(stk);
				call stk := OCLAny#Not(stk);
				call stk := OCLAny#And(stk);
				call stk := OCL#Boolean#Not(stk);
				
				
				cond#50 := $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
				call stk := OpCode#Pop(stk);
				goto label_51, label_83;
				label_51:
					assume !cond#50;
					call stk := OpCode#GetASM(stk);
					assert Seq#Length(stk) >= 1;
					assert $Unbox(Seq#Index(stk, Seq#Length(stk)-1)) != null;
					assert read($linkHeap, $Unbox(Seq#Index(stk, Seq#Length(stk)-1)),alloc);
					assert dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))) <: System.reserved;
					stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), $Box(read($linkHeap,$Unbox(Seq#Index(stk, Seq#Length(stk)-1)),FieldOfDecl(dtype($Unbox(Seq#Index(stk, Seq#Length(stk)-1))), _Field$links): Field (Set ref))));
					call stk := OpCode#Push(stk, _TransientLink);
					call stk := OpCode#Push(stk, _#native);
					assert Seq#Length(stk) >= 2;
					havoc obj#55;
					assume obj#55!= null && !read($linkHeap, obj#55, alloc) && dtype(obj#55) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
					$linkHeap := update($linkHeap, obj#55, alloc, true);
					assume $IsGoodHeap($linkHeap);
					assume $HeapSucc(old($linkHeap), $linkHeap);
					stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#55));

					call stk := OpCode#Dup(stk);
					call stk := OpCode#Push(stk, _T2TB);
					call stk := NTransientLink#setRule(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
					call stk := OpCode#Dup(stk);
					call stk := OpCode#Push(stk, _t1);
					call stk := OpCode#Load(stk, t1);
					call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
					call stk := OpCode#Dup(stk);
					call stk := OpCode#Push(stk, _src);
					call stk := OpCode#Load(stk, src);
					call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
					call stk := OpCode#Dup(stk);
					call stk := OpCode#Push(stk, _trg);
					call stk := OpCode#Load(stk, trg);
					call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
					call stk := OpCode#Dup(stk);
					call stk := OpCode#Push(stk, _c);
					call stk := OpCode#Load(stk, c);
					call stk := NTransientLink#addSourceElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
					call stk := OpCode#Dup(stk);
					call stk := OpCode#Push(stk, _t2);
					call stk := OpCode#Push(stk, _Transition);
					call stk := OpCode#Push(stk, _FSM);
					assert Seq#Length(stk) >= 2;
					havoc obj#79;
					assume obj#79!= null && !read($tarHeap, obj#79, alloc) && dtype(obj#79) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String),($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
					$tarHeap := update($tarHeap, obj#79, alloc, true);
					assume $IsGoodHeap($tarHeap);
					assume $HeapSucc(old($tarHeap), $tarHeap);
					assume getTarsBySrcs(Seq#Build(Seq#Build(Seq#Build(Seq#Singleton(t1),src),trg),c)) == obj#79;
					stk := Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj#79));
					call stk := NTransientLink#addTargetElement(stk,$Unbox(Seq#Index(stk, Seq#Length(stk)-3)),$Unbox(Seq#Index(stk, Seq#Length(stk)-2)),$Unbox(Seq#Index(stk, Seq#Length(stk)-1)));
					call stk := OpCode#Pusht(stk);
					stk := Seq#Take(stk, Seq#Length(stk)-3);
					goto label_end;
				label_83:
					assume cond#50;
					goto label_end;
				label_end:
					$l := $l+1;
					
			}
			$k := $k+1;
		}
		$j := $j+1;
	}
	$i := $i+1;
}

}