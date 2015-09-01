// ------------------------------------------------------------
// -- Source Metamodel Modelling ------------------------------
// ------------------------------------------------------------

const unique ER$ERSchema: ClassName extends  complete;
const unique ER$ERSchema.entities: Field ref;
const unique ER$ERSchema.relships: Field ref;
const unique ER$ERSchema.name: Field String;

const unique ER$Entity: ClassName extends  complete;
const unique ER$Entity.name: Field String;
const unique ER$Entity.attrs: Field ref;
const unique ER$Entity.ends: Field ref;
const unique ER$Entity.schema: Field ref;

const unique ER$Relship: ClassName extends  complete;
const unique ER$Relship.name: Field String;
const unique ER$Relship.attrs: Field ref;
const unique ER$Relship.ends: Field ref;
const unique ER$Relship.schema: Field ref;

const unique ER$RelshipEnd: ClassName extends  complete;
const unique ER$RelshipEnd.name: Field String;
const unique ER$RelshipEnd.relship: Field ref;
const unique ER$RelshipEnd.entity: Field ref;

const unique ER$ERAttribute: ClassName extends  complete;
const unique ER$ERAttribute.name: Field String;
const unique ER$ERAttribute.entity: Field ref;
const unique ER$ERAttribute.relship: Field ref;
const unique ER$ERAttribute.isKey: Field bool;



// ------------------------------------------------------------
// -- Target Metamodel Modelling ------------------------------
// ------------------------------------------------------------

const unique REL$RELSchema: ClassName extends  complete;
const unique REL$RELSchema.relations: Field ref;
const unique REL$RELSchema.name: Field String;

const unique REL$Relation: ClassName extends  complete;
const unique REL$Relation.schema: Field ref;
const unique REL$Relation.attrs: Field ref;
const unique REL$Relation.name: Field String;

const unique REL$RELAttribute: ClassName extends  complete;
const unique REL$RELAttribute.relation: Field ref;
const unique REL$RELAttribute.isKey: Field bool;
const unique REL$RELAttribute.name: Field String;



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









// ---------------------------------------------------------------
// -- Auxulary Type/Data Structure Modelling ---------------------
// ---------------------------------------------------------------










  axiom (FieldOfDecl(ER$ERSchema, _Field$name) == ER$ERSchema.name);
  axiom (FieldOfDecl(ER$ERSchema, _Field$entities) == ER$ERSchema.entities);
  axiom (FieldOfDecl(ER$ERSchema, _Field$relships) == ER$ERSchema.relships);
  axiom (FieldOfDecl(ER$Entity, _Field$name) == ER$Entity.name);
  axiom (FieldOfDecl(ER$Entity, _Field$schema) == ER$Entity.schema);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$entity) == ER$ERAttribute.entity);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$relship) == ER$ERAttribute.relship);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$name) == ER$ERAttribute.name);
  axiom (FieldOfDecl(ER$ERAttribute, _Field$isKey) == ER$ERAttribute.isKey);
  axiom (FieldOfDecl(ER$RelshipEnd, _Field$entity) == ER$RelshipEnd.entity);
  axiom (FieldOfDecl(ER$Relship, _Field$name) == ER$Relship.name);
  axiom (FieldOfDecl(ER$Relship, _Field$schema) == ER$Relship.schema);
  axiom (FieldOfDecl(ER$RelshipEnd, _Field$relship) == ER$RelshipEnd.relship);
  axiom (FieldOfDecl(ER$Entity, _Field$attrs) == ER$Entity.attrs);
  axiom (FieldOfDecl(ER$Relship, _Field$attrs) == ER$Relship.attrs);

  axiom (FieldOfDecl(REL$RELSchema, _Field$name) == REL$RELSchema.name);
  axiom (FieldOfDecl(REL$RELSchema, _Field$relations) == REL$RELSchema.relations);
  axiom (FieldOfDecl(REL$RELAttribute, _Field$name) == REL$RELAttribute.name);
  axiom (FieldOfDecl(REL$RELAttribute, _Field$isKey) == REL$RELAttribute.isKey);
  axiom (FieldOfDecl(REL$RELAttribute, _Field$relation) == REL$RELAttribute.relation);
  axiom (FieldOfDecl(REL$Relation, _Field$schema) == REL$Relation.schema);
  axiom (FieldOfDecl(REL$Relation, _Field$name) == REL$Relation.name);
  axiom (FieldOfDecl(REL$Relation, _Field$attrs) == REL$Relation.attrs);

  
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
		( read($h, $i, ER$ERSchema.entities)!=null &&
		 (forall j: int :: 0<=j && j<_System.array.Length(read($h, $i, ER$ERSchema.entities)) ==> 
		    ($Unbox(read($h, read($h, $i, ER$ERSchema.entities), IndexField(j))): ref !=null 
		      && read($h, $Unbox(read($h, read($h, $i, ER$ERSchema.entities), IndexField(j))): ref, alloc)
		      && dtype($Unbox(read($h, read($h, $i, ER$ERSchema.entities), IndexField(j))): ref)<:ER$Entity) ))
	 // ER$ERSchema => its [relships] feature is not null, and every of them is type of [ER$Relship], not [null], and is [allocated]
	 && ( read($h, $i, ER$ERSchema.relships)!=null &&
		 (forall j: int :: 0<=j && j<_System.array.Length(read($h, $i, ER$ERSchema.relships)) ==> 
		    ($Unbox(read($h, read($h, $i, ER$ERSchema.relships), IndexField(j))): ref !=null 
		      && read($h, $Unbox(read($h, read($h, $i, ER$ERSchema.relships), IndexField(j))): ref, alloc)
		      && dtype($Unbox(read($h, read($h, $i, ER$ERSchema.relships), IndexField(j))): ref)<:ER$Relship) ))
	)
)
}
  
  
  
  axiom (forall cl: ClassName :: cl <: ER$ERAttribute ==> 
	FieldOfDecl(cl, _Field$entity) == ER$ERAttribute.entity);
	
  axiom (forall cl: ClassName :: cl <: ER$RelshipEnd ==> 
	FieldOfDecl(cl, _Field$entity) == ER$RelshipEnd.entity);