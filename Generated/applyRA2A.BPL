/*
rule RA2A { from att : ER!ERAttribute, rs  : ER!Relship ( att.relship = rs )
	        to t : REL!RELAttribute
			       ( name <- att.name, isKey <- att.isKey, relation <- rs ) }

*/
procedure __applyRA2A (in: ref) returns ()
  requires Heap[in, TransientLink#rule]==_RA2A;  
  requires Heap[in, alloc] == true;
  requires typeof(in) == Native$TransientLink;
  requires Map#Domain(Heap[in, TransientLink#source])[_att];
  requires Map#Domain(Heap[in, TransientLink#source])[_rs];
  requires Map#Domain(Heap[in, TransientLink#target])[_t];
  requires typeof(Map#Elements(Heap[in, TransientLink#source])[_att]) == ER$ERAttribute;
  requires typeof(Map#Elements(Heap[in, TransientLink#source])[_rs]) == ER$Relship;
  requires typeof(Map#Elements(Heap[in, TransientLink#target])[_t]) == REL$RELAttribute;
  modifies Heap;
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], RELAttribute.name] == 
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Heap[Map#Elements(Heap[in, TransientLink#source])[_att], ERAttribute.name]));
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], RELAttribute.isKey] == 
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Heap[Map#Elements(Heap[in, TransientLink#source])[_att], ERAttribute.isKey]));
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], RELAttribute.relation] == 
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Map#Elements(Heap[in, TransientLink#source])[_rs]));
  ensures (forall<alpha> o: ref, f:Field alpha :: 
	(old(Heap[o, f]) == Heap[o, f]) ||
	(o == Map#Elements(Heap[in, TransientLink#target])[_t] && f == RELAttribute.name) ||
	(o == Map#Elements(Heap[in, TransientLink#target])[_t] && f == RELAttribute.isKey) ||
	(o == Map#Elements(Heap[in, TransientLink#target])[_t] && f == RELAttribute.relation) 
  
  );
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
call localStack := NTransientLink#getSourceElement(localStack);
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _rs);
call localStack := NTransientLink#getSourceElement(localStack);
call localStack, rs := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
call localStack := NTransientLink#getTargetElement(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$name);
call localStack := ASM#Resolve(localStack, old(Heap), $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1)): String);
call localStack := OpCode#Set(localStack, _Field$name, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, att);
call localStack := OpCode#Get(localStack,_Field$isKey);
call localStack := ASM#Resolve(localStack, old(Heap), $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1)): bool);
call localStack := OpCode#Set(localStack, _Field$isKey, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, rs);
call localStack := ASM#Resolve(localStack, old(Heap), $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1)): ref);
call localStack := OpCode#Set(localStack, _Field$relation, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

assert Heap[t, RELAttribute.relation] == $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Map#Elements(Heap[in, TransientLink#source])[_rs]));
}