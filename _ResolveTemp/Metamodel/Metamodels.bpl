


const unique Class$A: ClassName extends  complete;
const unique Class$A.name: Field String;

const unique Class$ARef: ClassName extends  complete;
const unique Class$ARef.ref: Field ref;
const unique Class$ARef.name: Field String;

const unique Class$Package: ClassName extends  complete;


const unique Clazz$B: ClassName extends  complete;
const unique Clazz$B.annotation: Field ref;
const unique Clazz$B.name: Field String;

const unique Clazz$Annotation: ClassName extends  complete;
const unique Clazz$Annotation.tag: Field String;

const unique Clazz$BRef: ClassName extends  complete;
const unique Clazz$BRef.ref: Field ref;
const unique Clazz$BRef.name: Field String;







  
  
  
// ---------------------------------------------------------------
// -- Auxulary Type/Data Structure Modelling ---------------------
// ---------------------------------------------------------------

const unique _0: String;

const classifierTable : [String, String] ClassName;




// ASM-specific
const unique Asm: ref;
  axiom Asm != null;
const unique ASM#Links : Field (Set ref);
const unique Native$TransientLink: ClassName;

const unique _#native: String;
const unique _TransientLink: String;

	// see org.eclipse.m2m.atl.engine.emfvm.lib.TransientLink
const unique TransientLink#source: Field (Map String ref);
const unique TransientLink#target: Field (Map String ref);
const unique TransientLink#rule: Field String;
  axiom classifierTable[_#native, _TransientLink] == Native$TransientLink;
  
function surj_tar_model($s: HeapType, $t: HeapType): bool
{ (forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == Clazz$BRef ==>
		(exists $i: ref :: dtype($i) <: Class$ARef && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o)) 
&&(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == Clazz$B ==>
		(exists $i: ref :: dtype($i) <: Class$A && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o)) 
	
}