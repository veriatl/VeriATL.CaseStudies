/*
rule RA2AK { from att : ER!ERAttribute, rse : ER!RelshipEnd 
	           ( att.entity = rse.entity and att.isKey = true )
	to   t : REL!RELAttribute 
	         ( name <- att.name, isKey <- att.isKey, relation <- rse.relship )}

*/
procedure __applyRA2AK (in: ref) returns ()
requires Heap[in, TransientLink#rule]==_RA2AK;  
  requires Heap[in, alloc] == true;
  requires typeof(in) == Native$TransientLink;
  requires Map#Domain(Heap[in, TransientLink#source])[_att];
  requires Map#Domain(Heap[in, TransientLink#source])[_rse];
  requires Map#Domain(Heap[in, TransientLink#target])[_t];
  requires typeof(Map#Elements(Heap[in, TransientLink#source])[_att]) == ER$ERAttribute;
  requires typeof(Map#Elements(Heap[in, TransientLink#source])[_rse]) == ER$RelshipEnd;
  requires typeof(Map#Elements(Heap[in, TransientLink#target])[_t]) == REL$RELAttribute;
  modifies Heap;
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], RELAttribute.name] == 
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Heap[Map#Elements(Heap[in, TransientLink#source])[_att], ERAttribute.name]));
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], RELAttribute.isKey] == 
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Heap[Map#Elements(Heap[in, TransientLink#source])[_att], ERAttribute.isKey]));
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], RELAttribute.relation] ==  
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Heap[Map#Elements(Heap[in, TransientLink#source])[_rse], RelshipEnd.relship]));
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
var rse: ref;	//slot: 3
var self: ref;	//slot: 0
var link: ref;	//slot: 1
localStack := OpCode#Aux#InitStk();
link := in;

call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _att);
call localStack := NTransientLink#getSourceElement(localStack);
call localStack, att := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _rse);
call localStack := NTransientLink#getSourceElement(localStack);
call localStack, rse := OpCode#Store(localStack);
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
call localStack := OpCode#Load(localStack, rse);
call localStack := OpCode#Get(localStack,_Field$relship);
call localStack := ASM#Resolve(localStack, old(Heap), $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1)): ref);
call localStack := OpCode#Set(localStack, _Field$relation, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

}