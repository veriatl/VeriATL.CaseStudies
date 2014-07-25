/* 
Modified ER2REL ATL TRANSFORMATION

Description: We seeded an rule conflict in the ER2REL ATL transformation, and use VeriATL to detect it. The seeded rule is a duplicate of S2S rule with an dummy filter on the source pattern. Thus, it will cause the source pattern being matched by both the S2S and S2S_SEEDED rule, which causes the runtime exception. In this case, VeriATL reports the following output to help the user detect rule conflict:
-------------------------------- Boogie Output  -----------------------------------------
match_exp.bpl(28,2): Error BP5002: A precondition for this call might not hold.
match_exp.bpl(60,3): Related location: This is the precondition that might not hold.
Execution trace:
    match_exp.bpl(20,2): anon0
-----------------------------------------------------------------------------------------	
*/

/*
ATL Transformation Specification:
rule S2S { from s : ER!ERSchema to t : REL!RELSchema }
rule S2S_SEEDED { from s : ER!ERSchema (Seeded_Filter(s)) to t : REL!RELSchema }

*/

function Seeded_Filter(o: ref): bool
{ o == null }

procedure driver() returns()
modifies Heap;
{
 call init();
 call __matchS2S();
 call __matchS2S_SEEDED();
}  

procedure init() returns ();
  ensures (forall o: ref :: isSrcRef(o) ==> !Heap[o, proc]);

  
procedure __matchS2S () returns ();
  requires (forall o1: ref :: 
    typeof(o1) == ER$ERSchema && Heap[o1, alloc] &&
	true ==> 
	!(Heap[o1,proc]) 
  );
  modifies Heap;
  ensures (forall o1: ref:: typeof(o1) == ER$ERSchema && old(Heap[o1, alloc]) ==>
			true ==>
			Heap[getSrcLink(o1), alloc] &&
			Heap[getSrcLink(o1), TransientLink#rule] == _S2S && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_s] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_s] == o1 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELSchema
		);
  ensures (forall<alpha> o: ref, f: Field alpha :: 
    (Heap[o, f] == old(Heap[o, f])) || 
	(typeof(o) == Native$TransientLink) ||
	(typeof(o) == REL$RELSchema) ||
	(typeof(o) == ER$ERSchema && f == proc)
  );
  
procedure __matchS2S_SEEDED () returns ();
  requires (forall o1: ref :: 
    typeof(o1) == ER$ERSchema && Heap[o1, alloc] && Seeded_Filter(o1) ==> 
	!(Heap[o1,proc]) 
  );
  modifies Heap;
  ensures (forall o1: ref:: typeof(o1) == ER$ERSchema && old(Heap[o1, alloc]) 
			&& Seeded_Filter(o1) ==>
			Heap[getSrcLink(o1), alloc] &&
			Heap[getSrcLink(o1), TransientLink#rule] == _S2S && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_s] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_s] == o1 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELSchema
		);
  ensures (forall<alpha> o: ref, f: Field alpha :: 
    (Heap[o, f] == old(Heap[o, f])) || 
	(typeof(o) == Native$TransientLink) ||
	(typeof(o) == REL$RELSchema) ||
	(typeof(o) == ER$ERSchema && Seeded_Filter(o) && f == proc)
  );
  
/*
we also show that if the rules do not conflict, the verification should succeed. This is demonstrated by the following variation of ER2REL ATL specification:

rule S2S_SEEDED { from s : ER!ERSchema (Seeded_Filter(s))to t : REL!RELSchema }
rule S2S_SEEDED2 { from s : ER!ERSchema (not Seeded_Filter(s)) to t : REL!RELSchema }

*/

procedure driver2() returns()
modifies Heap;
{
 call init();
 call __matchS2S_SEEDED2();
 call __matchS2S_SEEDED();
}  

procedure __matchS2S_SEEDED2 () returns ();
  requires (forall o1: ref :: 
    typeof(o1) == ER$ERSchema && Heap[o1, alloc] && !Seeded_Filter(o1) ==> 
	!(Heap[o1,proc]) 
  );
  modifies Heap;
  ensures (forall o1: ref:: typeof(o1) == ER$ERSchema && old(Heap[o1, alloc]) 
			&& !Seeded_Filter(o1) ==>
			Heap[getSrcLink(o1), alloc] &&
			Heap[getSrcLink(o1), TransientLink#rule] == _S2S && 
			Map#Domain(Heap[getSrcLink(o1), TransientLink#source])[_s] &&
			Map#Elements(Heap[getSrcLink(o1), TransientLink#source])[_s] == o1 &&
			Map#Domain(Heap[getSrcLink(o1), TransientLink#target])[_t] &&
			Heap[Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t], alloc] &&
			typeof(Map#Elements(Heap[getSrcLink(o1), TransientLink#target])[_t]) == REL$RELSchema
		);
  ensures (forall<alpha> o: ref, f: Field alpha :: 
    (Heap[o, f] == old(Heap[o, f])) || 
	(typeof(o) == Native$TransientLink) ||
	(typeof(o) == REL$RELSchema) ||
	(typeof(o) == ER$ERSchema && !Seeded_Filter(o) && f == proc)
  );