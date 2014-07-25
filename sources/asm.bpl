17
procedure main () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var self: ref;	//slot: 0
var obj#3: ref;
var obj#10: ref;
var obj#19: ref;
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Push(localStack, _OclParametrizedType);
call localStack := OpCode#Push(localStack, _#native);
havoc obj#3;
assume !Heap[obj#3, alloc];
call localStack := OpCode#New(localStack, obj#3);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _Collection);
// call J.setName(S):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _OclSimpleType);
call localStack := OpCode#Push(localStack, _#native);
havoc obj#10;
assume !Heap[obj#10, alloc];
call localStack := OpCode#New(localStack, obj#10);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _OclAny);
// call J.setName(S):V();
// call J.setElementType(J):V();
call localStack := OpCode#Set(localStack, _Field$col, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Push(localStack, _TransientLinkSet);
call localStack := OpCode#Push(localStack, _#native);
havoc obj#19;
assume !Heap[obj#19, alloc];
call localStack := OpCode#New(localStack, obj#19);
call localStack := OpCode#Set(localStack, _Field$links, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#GetASM(localStack);
// call A.__matcher__():V();
call localStack := OpCode#GetASM(localStack);
// call A.__exec__():V();

}
procedure __resolve__ () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var e: ref;	//slot: 2
var self: ref;	//slot: 0
var value: ref;	//slot: 1
var cond#4: bool;
var cond#11: bool;
var obj#20: ref;
var obj#21: Seq ref;
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#Load(localStack, value);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$col);
// call localStack := J.oclIsKindOf(J):B(localStack);
cond#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
call localStack := OpCode#Pop(localStack);
goto label_5, label_18;
label_5:
assume !cond#4;
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Load(localStack, value);
// call localStack := NTransientLinkSet;.getLinkBySourceElement(S):QNTransientLink;(localStack);
call localStack := OpCode#Dup(localStack);
// call localStack := J.oclIsUndefined():B(localStack);
cond#11 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
call localStack := OpCode#Pop(localStack);
goto label_12, label_15;
label_12:
assume !cond#11;
call localStack := OpCode#Load(localStack, value);
// call localStack := NTransientLink;.getTargetFromSource(J):J(localStack);
goto label_17;
label_15:
assume cond#11;
call localStack := OpCode#Pop(localStack);
call localStack := OpCode#Load(localStack, value);
label_17:
goto label_30;
label_18:
assume cond#4;
call localStack := OpCode#Push(localStack, _Sequence);
call localStack := OpCode#Push(localStack, _#native);
havoc obj#20;
assume !Heap[obj#20, alloc];
call localStack := OpCode#New(localStack, obj#20);
call localStack := OpCode#Load(localStack, value);
obj#21 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#21)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#21, $i)));
call localStack, e := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, e);
// call localStack := A.__resolve__(J):J(localStack);
// call localStack := QJ.including(J):QJ(localStack);
$i := $i+1;
}
// call localStack := QJ.flatten():QJ(localStack);
label_30:

}
procedure resolveTemp () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var self: ref;	//slot: 0
var value: ref;	//slot: 1
var name: ref;	//slot: 2
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Load(localStack, value);
// call localStack := NTransientLinkSet;.getLinkBySourceElement(S):QNTransientLink;(localStack);
call localStack := OpCode#Load(localStack, value);
call localStack := OpCode#Load(localStack, name);
// call localStack := NTransientLink;.getNamedTargetFromSource(JS):J(localStack);

}
procedure __matcher__ () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var self: ref;	//slot: 0
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#GetASM(localStack);
// call A.__matchS2S():V();
call localStack := OpCode#GetASM(localStack);
// call A.__matchE2R():V();
call localStack := OpCode#GetASM(localStack);
// call A.__matchR2R():V();
call localStack := OpCode#GetASM(localStack);
// call A.__matchEA2A():V();
call localStack := OpCode#GetASM(localStack);
// call A.__match():V();
call localStack := OpCode#GetASM(localStack);
// call A.__matchRA2AK():V();

}
procedure __exec__ () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var e: ref;	//slot: 1
var e: ref;	//slot: 1
var e: ref;	//slot: 1
var e: ref;	//slot: 1
var e: ref;	//slot: 1
var e: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#3: Seq ref;
var obj#13: Seq ref;
var obj#23: Seq ref;
var obj#33: Seq ref;
var obj#43: Seq ref;
var obj#53: Seq ref;
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _S2S);
// call localStack := NTransientLinkSet;.getLinksByRule(S):QNTransientLink;(localStack);
obj#3 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#3)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#3, $i)));
call localStack, e := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, e);
// call A.__applyS2S(NTransientLink;):V();
$i := $i+1;
}
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _E2R);
// call localStack := NTransientLinkSet;.getLinksByRule(S):QNTransientLink;(localStack);
obj#13 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#13)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#13, $i)));
call localStack, e := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, e);
// call A.__applyE2R(NTransientLink;):V();
$i := $i+1;
}
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _R2R);
// call localStack := NTransientLinkSet;.getLinksByRule(S):QNTransientLink;(localStack);
obj#23 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#23)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#23, $i)));
call localStack, e := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, e);
// call A.__applyR2R(NTransientLink;):V();
$i := $i+1;
}
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _EA2A);
// call localStack := NTransientLinkSet;.getLinksByRule(S):QNTransientLink;(localStack);
obj#33 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#33)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#33, $i)));
call localStack, e := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, e);
// call A.__applyEA2A(NTransientLink;):V();
$i := $i+1;
}
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _RA2A);
// call localStack := NTransientLinkSet;.getLinksByRule(S):QNTransientLink;(localStack);
obj#43 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#43)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#43, $i)));
call localStack, e := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, e);
// call A.__applyRA2A(NTransientLink;):V();
$i := $i+1;
}
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _RA2AK);
// call localStack := NTransientLinkSet;.getLinksByRule(S):QNTransientLink;(localStack);
obj#53 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#53)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#53, $i)));
call localStack, e := OpCode#Store(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, e);
// call A.__applyRA2AK(NTransientLink;):V();
$i := $i+1;
}

}
procedure __matchS2S () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var s: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var obj#11: ref;
var obj#23: ref;
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#Push(localStack, _ERSchema);
call localStack := OpCode#Push(localStack, _ER);
call localStack := OpCode#Findme(localStack);
call localStack := OpCode#Push(localStack, _IN);
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#4)){ 
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
call localStack := OpCode#Push(localStack, _S2S);
// call NTransientLink;.setRule(MATL!Rule;):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _s);
call localStack := OpCode#Load(localStack, s);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _t);
call localStack := OpCode#Push(localStack, _RELSchema);
call localStack := OpCode#Push(localStack, _REL);
havoc obj#23;
assume !Heap[obj#23, alloc];
call localStack := OpCode#New(localStack, obj#23);
// call NTransientLink;.addTargetElement(SJ):V();
call localStack := OpCode#Pusht(localStack);
// call NTransientLinkSet;.addLink2(NTransientLink;B):V();
$i := $i+1;
}

}
procedure __applyS2S () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var t: ref;	//slot: 3
var s: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
localStack := OpCode#Aux#InitStk();
link := in;

call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _s);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, s := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
// call localStack := NTransientLink;.getTargetElement(S):J(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Pop(localStack);

}
procedure __matchE2R () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var s: ref;	//slot: 1
var self: ref;	//slot: 0
var obj#4: Seq ref;
var obj#11: ref;
var obj#23: ref;
localStack := OpCode#Aux#InitStk();

call localStack := OpCode#Push(localStack, _Entity);
call localStack := OpCode#Push(localStack, _ER);
call localStack := OpCode#Findme(localStack);
call localStack := OpCode#Push(localStack, _IN);
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#4)){ 
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
call localStack := OpCode#Push(localStack, _E2R);
// call NTransientLink;.setRule(MATL!Rule;):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _s);
call localStack := OpCode#Load(localStack, s);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _t);
call localStack := OpCode#Push(localStack, _Relation);
call localStack := OpCode#Push(localStack, _REL);
havoc obj#23;
assume !Heap[obj#23, alloc];
call localStack := OpCode#New(localStack, obj#23);
// call NTransientLink;.addTargetElement(SJ):V();
call localStack := OpCode#Pusht(localStack);
// call NTransientLinkSet;.addLink2(NTransientLink;B):V();
$i := $i+1;
}

}
procedure __applyE2R () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var t: ref;	//slot: 3
var s: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
localStack := OpCode#Aux#InitStk();
link := in;

call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _s);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, s := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
// call localStack := NTransientLink;.getTargetElement(S):J(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, s);
call localStack := OpCode#Get(localStack,_Field$name);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$name, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, s);
call localStack := OpCode#Get(localStack,_Field$schema);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$schema, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

}
procedure __matchR2R () returns ()
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
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#4)){ 
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
// call NTransientLink;.setRule(MATL!Rule;):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _s);
call localStack := OpCode#Load(localStack, s);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _t);
call localStack := OpCode#Push(localStack, _Relation);
call localStack := OpCode#Push(localStack, _REL);
havoc obj#23;
assume !Heap[obj#23, alloc];
call localStack := OpCode#New(localStack, obj#23);
// call NTransientLink;.addTargetElement(SJ):V();
call localStack := OpCode#Pusht(localStack);
// call NTransientLinkSet;.addLink2(NTransientLink;B):V();
$i := $i+1;
}

}
procedure __applyR2R () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var t: ref;	//slot: 3
var s: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1
localStack := OpCode#Aux#InitStk();
link := in;

call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _s);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, s := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
// call localStack := NTransientLink;.getTargetElement(S):J(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, s);
call localStack := OpCode#Get(localStack,_Field$name);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$name, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, s);
call localStack := OpCode#Get(localStack,_Field$schema);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$schema, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

}
procedure __matchEA2A () returns ()
{

var localStack: Seq BoxType;
var $i: int;
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
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#4)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#4, $i)));
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Push(localStack, _Entity);
call localStack := OpCode#Push(localStack, _ER);
call localStack := OpCode#Findme(localStack);
call localStack := OpCode#Push(localStack, _IN);
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#11 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#11)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#11, $i)));
call localStack, ent := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$entity);
call localStack := OpCode#Load(localStack, ent);
// call localStack := J.=(J):J(localStack);
// call localStack := B.not():B(localStack);
cond#19 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
call localStack := OpCode#Pop(localStack);
goto label_20, label_44;
label_20:
assume !cond#19;
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _TransientLink);
call localStack := OpCode#Push(localStack, _#native);
havoc obj#24;
assume !Heap[obj#24, alloc];
call localStack := OpCode#New(localStack, obj#24);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _EA2A);
// call NTransientLink;.setRule(MATL!Rule;):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _att);
call localStack := OpCode#Load(localStack, att);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _ent);
call localStack := OpCode#Load(localStack, ent);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _t);
call localStack := OpCode#Push(localStack, _RELAttribute);
call localStack := OpCode#Push(localStack, _REL);
havoc obj#40;
assume !Heap[obj#40, alloc];
call localStack := OpCode#New(localStack, obj#40);
// call NTransientLink;.addTargetElement(SJ):V();
call localStack := OpCode#Pusht(localStack);
// call NTransientLinkSet;.addLink2(NTransientLink;B):V();
label_44:
assume cond#19;
$i := $i+1;
}
$i := $i+1;
}

}
procedure __applyEA2A () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var t: ref;	//slot: 4
var att: ref;	//slot: 2
var ent: ref;	//slot: 3
var self: ref;	//slot: 0
var link: ref;	//slot: 1
localStack := OpCode#Aux#InitStk();
link := in;

call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _att);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _ent);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, ent := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
// call localStack := NTransientLink;.getTargetElement(S):J(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$name);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$name, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$isKey);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$isKey, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, ent);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$relation, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

}
procedure __matchRA2A () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var att: ref;	//slot: 1
var rs: ref;	//slot: 2
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
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#4)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#4, $i)));
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Push(localStack, _Relship);
call localStack := OpCode#Push(localStack, _ER);
call localStack := OpCode#Findme(localStack);
call localStack := OpCode#Push(localStack, _IN);
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#11 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#11)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#11, $i)));
call localStack, rs := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$relship);
call localStack := OpCode#Load(localStack, rs);
// call localStack := J.=(J):J(localStack);
// call localStack := B.not():B(localStack);
cond#19 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
call localStack := OpCode#Pop(localStack);
goto label_20, label_44;
label_20:
assume !cond#19;
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Get(localStack,_Field$links);
call localStack := OpCode#Push(localStack, _TransientLink);
call localStack := OpCode#Push(localStack, _#native);
havoc obj#24;
assume !Heap[obj#24, alloc];
call localStack := OpCode#New(localStack, obj#24);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _RA2A);
// call NTransientLink;.setRule(MATL!Rule;):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _att);
call localStack := OpCode#Load(localStack, att);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _rs);
call localStack := OpCode#Load(localStack, rs);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _t);
call localStack := OpCode#Push(localStack, _RELAttribute);
call localStack := OpCode#Push(localStack, _REL);
havoc obj#40;
assume !Heap[obj#40, alloc];
call localStack := OpCode#New(localStack, obj#40);
// call NTransientLink;.addTargetElement(SJ):V();
call localStack := OpCode#Pusht(localStack);
// call NTransientLinkSet;.addLink2(NTransientLink;B):V();
label_44:
assume cond#19;
$i := $i+1;
}
$i := $i+1;
}

}
procedure __applyRA2A () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var t: ref;	//slot: 4
var att: ref;	//slot: 2
var rs: ref;	//slot: 3
var self: ref;	//slot: 0
var link: ref;	//slot: 1
localStack := OpCode#Aux#InitStk();
link := in;

call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _att);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _rs);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, rs := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
// call localStack := NTransientLink;.getTargetElement(S):J(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$name);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$name, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$isKey);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$isKey, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, rs);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$relation, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

}
procedure __matchRA2AK () returns ()
{

var localStack: Seq BoxType;
var $i: int;
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
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#4 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#4)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#4, $i)));
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Push(localStack, _RelshipEnd);
call localStack := OpCode#Push(localStack, _ER);
call localStack := OpCode#Findme(localStack);
call localStack := OpCode#Push(localStack, _IN);
// call localStack := MMOF!Classifier;.allInstancesFrom(S):QJ(localStack);
obj#11 := $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1));
$i:=0;
call localStack := OpCode#Pop(localStack);
while($i<Seq#Length(obj#11)){ 
localStack := Seq#Build(localStack, $Box(Seq#Index(obj#11, $i)));
call localStack, rse := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$entity);
call localStack := OpCode#Load(localStack, rse);
call localStack := OpCode#Get(localStack,_Field$entity);
// call localStack := J.=(J):J(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$isKey);
call localStack := OpCode#Pusht(localStack);
// call localStack := J.=(J):J(localStack);
// call localStack := J.and(J):J(localStack);
// call localStack := B.not():B(localStack);
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
// call NTransientLink;.setRule(MATL!Rule;):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _att);
call localStack := OpCode#Load(localStack, att);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _rse);
call localStack := OpCode#Load(localStack, rse);
// call NTransientLink;.addSourceElement(SJ):V();
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#Push(localStack, _t);
call localStack := OpCode#Push(localStack, _RELAttribute);
call localStack := OpCode#Push(localStack, _REL);
havoc obj#46;
assume !Heap[obj#46, alloc];
call localStack := OpCode#New(localStack, obj#46);
// call NTransientLink;.addTargetElement(SJ):V();
call localStack := OpCode#Pusht(localStack);
// call NTransientLinkSet;.addLink2(NTransientLink;B):V();
label_50:
assume cond#25;
$i := $i+1;
}
$i := $i+1;
}

}
procedure __applyRA2AK () returns ()
{

var localStack: Seq BoxType;
var $i: int;
var t: ref;	//slot: 4
var att: ref;	//slot: 2
var rse: ref;	//slot: 3
var self: ref;	//slot: 0
var link: ref;	//slot: 1
localStack := OpCode#Aux#InitStk();
link := in;

call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _att);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _rse);
// call localStack := NTransientLink;.getSourceElement(S):J(localStack);
call localStack, rse := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
// call localStack := NTransientLink;.getTargetElement(S):J(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$name);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$name, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$isKey);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$isKey, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, rse);
call localStack := OpCode#Get(localStack,_Field$relship);
// call localStack := A.__resolve__(J):J(localStack);
call localStack := OpCode#Set(localStack, _Field$relation, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

}
