// ------------------------------------------------------------
// -- Source Metamodel Modelling ------------------------------
// ------------------------------------------------------------
const unique ER$Entity: ClassName extends complete;
const unique ER$Relship: ClassName extends complete;
const unique ER$ERSchema: ClassName extends complete;
const unique ER$ERAttribute: ClassName extends complete;
const unique ER$RelshipEnd: ClassName extends complete;

const unique ERSchema.name: Field String;

const unique Entity.name: Field String;
const unique Relship.name: Field String;
const unique RelshipEnd.name: Field String;
const unique ERAttribute.name: Field String;
const unique ERAttribute.isKey: Field bool;


const unique ERSchema.entities: Field ref;		// typeof(ref) == ER!Entity forall ref in Set ref
const unique Entity.schema: Field ref;					// typeof(ref) == ER!ERSchema

const unique ERSchema.relships: Field ref;		// typeof(ref) == ER!Relship forall ref in Set ref
const unique Relship.schema: Field ref;					// typeof(ref) == ER!ERSchema

const unique Entity.ends: Field ref;				// typeof(ref) == ER!RelshipEnd
const unique RelshipEnd.entity: Field ref;				// typeof(ref) == ER!Entity
const unique Entity.attrs: Field ref;				// typeof(ref) == ER!ERAttribute
const unique ERAttribute.entity: Field ref;				// typeof(ref) == ER!entity

const unique Relship.attrs: Field ref;			// typeof(ref) == ER!ERAttribute
const unique RelshipEnd.relship: Field ref;				// typeof(ref) == ER!Relship
const unique Relship.ends: Field ref;				// typeof(ref) == ER!RelshipEnd
const unique ERAttribute.relship: Field ref;			// typeof(ref) == ER!Relship

// ------------------------------------------------------------
// -- Target Metamodel Modelling ------------------------------
// ------------------------------------------------------------
const unique REL$RELAttribute: ClassName extends complete;
const unique REL$Relation: ClassName extends complete;
const unique REL$RELSchema: ClassName extends complete;

const unique RELSchema.name: Field String;

const unique Relation.name: Field String;
const unique RELAttribute.name: Field String;
const unique RELAttribute.isKey: Field bool;

const unique RELSchema.relations: Field ref;
const unique Relation.schema: Field ref;

const unique Relation.attrs: Field ref;
const unique RELAttribute.relation: Field ref;

// ---------------------------------------------------------------
// -- Auxulary String for Metamodels ----------------------
// ---------------------------------------------------------------

// the const string declared in this part are referred in ASM for the string of field
const unique _Field$name: NameFamily;
const unique _Field$isKey: NameFamily;
const unique _Field$relship: NameFamily;
const unique _Field$relation: NameFamily;
const unique _Field$entity: NameFamily;
const unique _Field$schema: NameFamily;
const unique _Field$attrs: NameFamily;

const unique _Field$entities: NameFamily;
const unique _Field$relships: NameFamily;

const unique _Field$relations: NameFamily;


const unique _Field$links: NameFamily;

// the const string declared in this part are referred in ASM for the string of rule's entity
const unique _att: String;
const unique _rse: String;
const unique _rs: String;
const unique _t: String;


const unique _ER: String;
const unique _REL: String;

const unique _Entity: String;
const unique _Relship: String;
const unique _ERAttribute: String;
const unique _RelshipEnd: String;
const unique _ERSchema: String;

const unique _RELSchema: String;
const unique _RELAttribute: String;
const unique _Relation: String;

const unique _IN: String;

const unique _S2S: String;
const unique _EA2A: String;
const unique _R2R: String;
const unique _RA2A: String;
const unique _RA2AK: String;
const unique _E2R: String;

const unique _s: String;
const unique _ent: String;

const unique _TransientLink: String;
const unique _#native: String;







// ---------------------------------------------------------------
// -- Auxulary Type/Data Structure Modelling ---------------------
// ---------------------------------------------------------------





// ASM-specific
const unique Asm: ref;
  axiom Asm != null;
const unique ASM#Links : Field (Set ref);
const unique Native$TransientLink: ClassName;



	// see org.eclipse.m2m.atl.engine.emfvm.lib.TransientLink
const unique TransientLink#source: Field (Map String ref);
const unique TransientLink#target: Field (Map String ref);
const unique TransientLink#rule: Field String;




  axiom (FieldOfDecl(ER$ERSchema, _Field$name) == ERSchema.name);
  axiom (FieldOfDecl(ER$ERSchema, _Field$entities) == ERSchema.entities);
  axiom (FieldOfDecl(ER$ERSchema, _Field$relships) == ERSchema.relships);
  axiom (FieldOfDecl(ER$Entity, _Field$name) == Entity.name);
  axiom (FieldOfDecl(ER$Entity, _Field$schema) == Entity.schema);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$entity) == ERAttribute.entity);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$relship) == ERAttribute.relship);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$name) == ERAttribute.name);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$isKey) == ERAttribute.isKey);
  axiom (FieldOfDecl(ER$RelshipEnd, _Field$entity) == RelshipEnd.entity);
  axiom (FieldOfDecl(ER$Relship, _Field$name) == Relship.name);
  axiom (FieldOfDecl(ER$Relship, _Field$schema) == Relship.schema);
  axiom (FieldOfDecl(ER$RelshipEnd, _Field$relship) == RelshipEnd.relship);
  axiom (FieldOfDecl(ER$Entity, _Field$attrs) == Entity.attrs);
  axiom (FieldOfDecl(ER$Relship, _Field$attrs) == Relship.attrs);

  axiom (FieldOfDecl(REL$RELSchema, _Field$name) == RELSchema.name);
  axiom (FieldOfDecl(REL$RELSchema, _Field$relations) == RELSchema.relations);
  axiom (FieldOfDecl(REL$RELAttribute, _Field$name) == RELAttribute.name);
  axiom (FieldOfDecl(REL$RELAttribute, _Field$isKey) == RELAttribute.isKey);
  axiom (FieldOfDecl(REL$RELAttribute, _Field$relation) == RELAttribute.relation);
  axiom (FieldOfDecl(REL$Relation, _Field$schema) == Relation.schema);
  axiom (FieldOfDecl(REL$Relation, _Field$name) == Relation.name);
  axiom (FieldOfDecl(REL$Relation, _Field$attrs) == Relation.attrs);

  
// [mmName, className]
const classifierTable : [String, String] ClassName;
  axiom classifierTable[_ER, _Entity] == ER$Entity;
  axiom classifierTable[_ER, _Relship] == ER$Relship;
  axiom classifierTable[_ER, _ERSchema] == ER$ERSchema;
  axiom classifierTable[_ER, _ERAttribute] == ER$ERAttribute;
  axiom classifierTable[_ER, _RelshipEnd] == ER$RelshipEnd;

  axiom classifierTable[_REL, _RELAttribute] == REL$RELAttribute;
  axiom classifierTable[_REL, _Relation] == REL$Relation;
  axiom classifierTable[_REL, _RELSchema] == REL$RELSchema;
  
  axiom classifierTable[_#native, _TransientLink] == Native$TransientLink;


function surj_tar_model($s: HeapType, $t: HeapType): bool
{
	(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == REL$RELSchema ==>
		(exists $i: ref :: dtype($i) <: ER$ERSchema && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o))
	&&
	(forall $o: ref :: $o!=null && read($t, $o, alloc) && dtype($o) == REL$Relation ==>
		(exists $i: ref :: (dtype($i) <: ER$Entity || dtype($i)<:ER$Relship) && $i != null && read($s, $i, alloc) && getTarsBySrcs(Seq#Singleton($i))==$o))
}

function valid_src_model($h: HeapType): bool
{
	(forall $i: ref ::
	
	($i!=null && read($h, $i, alloc) && dtype($i) <: ER$ERSchema ==> 
	 // ER$ERSchema => its [entities] feature is not null, and every of them is type of [ER$Entity], not [null], and is [allocated]
		( read($h, $i, ERSchema.entities)!=null &&
		 (forall j: int :: 0<=j && j<_System.array.Length(read($h, $i, ERSchema.entities)) ==> 
		    ($Unbox(read($h, read($h, $i, ERSchema.entities), IndexField(j))): ref !=null 
		      && read($h, $Unbox(read($h, read($h, $i, ERSchema.entities), IndexField(j))): ref, alloc)
		      && dtype($Unbox(read($h, read($h, $i, ERSchema.entities), IndexField(j))): ref)<:ER$Entity) ))
	 // ER$ERSchema => its [relships] feature is not null, and every of them is type of [ER$Relship], not [null], and is [allocated]
	 && ( read($h, $i, ERSchema.relships)!=null &&
		 (forall j: int :: 0<=j && j<_System.array.Length(read($h, $i, ERSchema.relships)) ==> 
		    ($Unbox(read($h, read($h, $i, ERSchema.relships), IndexField(j))): ref !=null 
		      && read($h, $Unbox(read($h, read($h, $i, ERSchema.relships), IndexField(j))): ref, alloc)
		      && dtype($Unbox(read($h, read($h, $i, ERSchema.relships), IndexField(j))): ref)<:ER$Relship) ))
	)
)
}
  
  
  
  axiom (forall cl: ClassName :: cl <: ER$ERAttribute ==> 
	FieldOfDecl(cl, _Field$entity) == ERAttribute.entity);
	
  axiom (forall cl: ClassName :: cl <: ER$RelshipEnd ==> 
	FieldOfDecl(cl, _Field$entity) == RelshipEnd.entity);