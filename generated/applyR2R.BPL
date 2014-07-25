/*
rule R2R { from s : ER!Relship 
           to t : REL!Relation ( name  <- s.name, schema <- s.schema  ) }

*/
procedure __applyR2R (in: ref) returns ()
  requires Heap[in, TransientLink#rule]==_R2R;  
  requires Heap[in, alloc] == true;
  requires typeof(in) == Native$TransientLink;
  requires Map#Domain(Heap[in, TransientLink#source])[_s];
  requires Map#Domain(Heap[in, TransientLink#target])[_t];
  requires typeof(Map#Elements(Heap[in, TransientLink#source])[_s]) == ER$Relship;
  requires typeof(Map#Elements(Heap[in, TransientLink#target])[_t]) == REL$Relation;
  modifies Heap;
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], Relation.name] == 
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Heap[Map#Elements(Heap[in, TransientLink#source])[_s], Relship.name]));
  ensures Heap[Map#Elements(Heap[in, TransientLink#target])[_t], Relation.schema] == 
  $Unbox(ASM#Resolve#Sem(Asm, old(Heap), Heap[Map#Elements(Heap[in, TransientLink#source])[_s], Relship.schema]));
  ensures (forall<alpha> o: ref, f:Field alpha :: 
	(old(Heap[o, f]) == Heap[o, f]) ||
	(o == Map#Elements(Heap[in, TransientLink#target])[_t] && f == Relation.name) ||
	(o == Map#Elements(Heap[in, TransientLink#target])[_t] && f == Relation.schema) 
  
  );
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
call localStack := NTransientLink#getSourceElement(localStack);
call localStack, s := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
call localStack := NTransientLink#getTargetElement(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, s);
call localStack := OpCode#Get(localStack,_Field$name);
call localStack := ASM#Resolve(localStack, old(Heap), $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1)): String);
call localStack := OpCode#Set(localStack, _Field$name, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Dup(localStack);
call localStack := OpCode#GetASM(localStack);
call localStack := OpCode#Load(localStack, s);
call localStack := OpCode#Get(localStack,_Field$schema);
call localStack := ASM#Resolve(localStack, old(Heap), $Unbox(Seq#Index(localStack, Seq#Length(localStack)-1)): ref);
call localStack := OpCode#Set(localStack, _Field$schema, ($Unbox(Seq#Index(localStack, Seq#Length(localStack)-1))));
call localStack := OpCode#Pop(localStack);

}