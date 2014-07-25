// -----------------------------------------------------------------
// -- Operational Correctness Verification of ASM   ----------------
// -- Apply operation of S2S rule ----------------------------------
// -----------------------------------------------------------------

procedure __applyS2S(in: ref) returns();
  requires Heap[in, TransientLink#rule]==_S2S;  
  requires Heap[in, alloc] == true;
  requires typeof(in) == Native$TransientLink;
  requires Map#Domain(Heap[in, TransientLink#source])[_s];
  requires Map#Domain(Heap[in, TransientLink#target])[_t];
  requires typeof(Map#Elements(Heap[in, TransientLink#source])[_s]) == ER$ERSchema;
  requires typeof(Map#Elements(Heap[in, TransientLink#target])[_t]) == REL$RELSchema;
  
implementation __applyS2S (in:ref) returns ()
{

var localStack: Seq BoxType;
var t: ref;	//slot: 3
var s: ref;	//slot: 2
var self: ref;	//slot: 0
var link: ref;	//slot: 1

localStack := OpCode#Aux#InitStk(); 
link := in;		//copy parameter
  
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _s);
call localStack := NTransientLink#getSourceElement(localStack);
call localStack, s := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, link);
call localStack := OpCode#Push(localStack, _t);
call localStack := NTransientLink#getTargetElement(localStack);
call localStack, t := OpCode#Store(localStack);
call localStack := OpCode#Load(localStack, t);
call localStack := OpCode#Pop(localStack);

}