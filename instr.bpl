// -----------------------------------------------------
// -- Proof System for ASM Instruction Set -------------
// -----------------------------------------------------
  
  
function OpCode#Aux#InitStk(): Seq BoxType;
  axiom OpCode#Aux#InitStk() == (Seq#Empty(): Seq BoxType);
 
//Instr: push  
procedure OpCode#Push(stk: Seq BoxType, s: String) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(s));

  
//Instr: pushi  
procedure OpCode#Pushi(stk: Seq BoxType, i: int) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(i));  
  
//Instr: pushf  
procedure OpCode#Pushf(stk: Seq BoxType) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(false));

//Instr: pusht
procedure OpCode#Pusht(stk: Seq BoxType) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(true));
  
//Instr: pop 
procedure OpCode#Pop(stk: Seq BoxType) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-1);
  
//Instr: store, 123
procedure OpCode#Store<T>(stk: Seq BoxType) returns(newStk: Seq BoxType, topVal: T);
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-1);
  ensures topVal == $Unbox(Seq#Index(stk, Seq#Length(stk)-1));
  
//Instr: load
procedure OpCode#Load<T>(stk: Seq BoxType, v: T) returns (newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(v));
 
//Instr: Swap
procedure OpCode#Swap(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1)), Seq#Index(stk, Seq#Length(stk)-2));
 
//Instr: Dup
procedure OpCode#Dup(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 1;
  ensures newStk == Seq#Build(stk, Seq#Index(stk, Seq#Length(stk)-1));
 
//Instr: Dup_x1
procedure OpCode#DupX1(stk: Seq BoxType) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Build(Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), Seq#Index(stk, Seq#Length(stk)-1)), Seq#Index(stk, Seq#Length(stk)-2)), Seq#Index(stk, Seq#Length(stk)-1));

  
//Instr: New, 
// locStk[len-1] == mmName
// locStk[len-2] == className
// with the following stmt in appropriate place:
//  var obj;
//
//  havoc obj;
//  assume !Heap[obj, alloc];
procedure OpCode#New(stk: Seq BoxType, obj: ref) returns (newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  requires !Heap[obj, alloc];
  modifies Heap;
  ensures Heap[obj, alloc];
  ensures (forall<alpha> o: ref, f:Field alpha :: 
	(old(Heap[o, f]) == Heap[o, f]) || 
	(o == obj && f == alloc) 
  );
  ensures typeof(obj) == classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
										 ($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)];
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), $Box(obj));

// Instr: get  
// E.g. when people have instr like 'get name'
//	var name: String	-- This information is from metamodel.
//	fieldType is then instansiate to 'String', so getFieldByName(TName, alpha) is instansiate to String, which return 'field String'.
// So, we require the operands of get to have some of naming mechanism, e.g. FieldType#name. They should pre-precessed in type.bpl, by processing the metamodel.
procedure OpCode#Get<alpha>(stk: Seq BoxType, fieldName: alpha) returns(newStk: Seq BoxType);  
  requires Seq#Length(stk) >= 1;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-1), 
					$Box(Heap[ $Unbox(Seq#Index(stk, Seq#Length(stk)-1)), 
								getFieldByName(typeof($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): ref), fieldName)]));
  

//Instr: set  
procedure OpCode#Set<alpha>(stk: Seq BoxType, fieldName: alpha, val: alpha) returns(newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  modifies Heap;
  ensures newStk == Seq#Take(stk, Seq#Length(stk)-2);
  ensures Heap[($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): ref), getFieldByName(typeof($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): ref),fieldName)] == val;
  ensures (forall<gama> o: ref, f:Field gama :: 
	(old(Heap[o, f]) == Heap[o, f]) || 
		(o == ($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): ref) && 
		 f == getFieldByName(typeof($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): ref),fieldName))); 

   
// Instr: findme
procedure OpCode#Findme(stk: Seq BoxType) returns(newStk: Seq BoxType);
  requires Seq#Length(stk) >= 2;
  ensures newStk == Seq#Build(Seq#Take(stk, Seq#Length(stk)-2), 
							  $Box(classifierTable[($Unbox(Seq#Index(stk, Seq#Length(stk)-1)): String), 
												   ($Unbox(Seq#Index(stk, Seq#Length(stk)-2)): String)]));

// Instr: getASM  
procedure OpCode#GetASM(stk: Seq BoxType) returns(newStk: Seq BoxType);
  ensures newStk == Seq#Build(stk, $Box(Asm));
  