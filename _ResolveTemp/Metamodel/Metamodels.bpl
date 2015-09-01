


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





  
function surj_tar_model($s: HeapType, $t: HeapType): bool
{ (forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == Clazz$BRef ==>
		(exists $i: ref :: dtype($i) <: Class$ARef && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o)) 
&&(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == Clazz$B ==>
		(exists $i: ref :: dtype($i) <: Class$A && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o)) 
	
}