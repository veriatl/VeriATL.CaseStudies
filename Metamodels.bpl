
// ------------------------------------------------------------
// -- Source Metamodel Modelling ------------------------------
// ------------------------------------------------------------
const unique ER$Entity: TName;
const unique ER$Relship: TName;
const unique ER$ERSchema: TName;
const unique ER$ERAttribute: TName;
const unique ER$RelshipEnd: TName;

const unique Entity.name: Field String;
const unique Relship.name: Field String;
const unique RelshipEnd.name: Field String;
const unique ERAttribute.name: Field String;
const unique ERAttribute.isKey: Field bool;


const unique ERSchema.entities: Field (Set ref);		// typeof(ref) == ER!Entity forall ref in Set ref
const unique Entity.schema: Field ref;					// typeof(ref) == ER!ERSchema

const unique ERSchema.relships: Field (Set ref);		// typeof(ref) == ER!Relship forall ref in Set ref
const unique Relship.schema: Field ref;					// typeof(ref) == ER!ERSchema

const unique Entity.ends: Field (Set ref);				// typeof(ref) == ER!RelshipEnd
const unique RelshipEnd.entity: Field ref;				// typeof(ref) == ER!Entity
const unique Entity.attrs: Field (Set ref);				// typeof(ref) == ER!ERAttribute
const unique ERAttribute.entity: Field ref;				// typeof(ref) == ER!entity

const unique Relship.attrs: Field (Set ref);			// typeof(ref) == ER!ERAttribute
const unique RelshipEnd.relship: Field ref;				// typeof(ref) == ER!Relship
const unique Relship.ends: Field (Set ref);				// typeof(ref) == ER!RelshipEnd
const unique ERAttribute.relship: Field ref;			// typeof(ref) == ER!Relship

// ------------------------------------------------------------
// -- Target Metamodel Modelling ------------------------------
// ------------------------------------------------------------
const unique REL$RELAttribute: TName;
const unique REL$Relation: TName;
const unique REL$RELSchema: TName;

const unique Relation.name: Field String;
const unique RELAttribute.name: Field String;
const unique RELAttribute.isKey: Field bool;

const unique RELSchema.relations: Field (Set ref);
const unique Relation.schema: Field ref;

const unique Relation.attrs: Field (Set ref);
const unique RELAttribute.relation: Field ref;

// ---------------------------------------------------------------
// -- Auxulary String for Metamodels ----------------------
// ---------------------------------------------------------------

// the const string declared in this part are referred in ASM for the string of field
const unique _Field$name: String;
const unique _Field$isKey: bool;
const unique _Field$relship: ref;
const unique _Field$relation: ref;
const unique _Field$entity: ref;
const unique _Field$schema: ref;

const unique _Field$links: Set ref;

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

// global model store
var Heap : HeapType where $IsGoodHeap(Heap);


type BOOL;
type TName;



// ASM-specific
const unique TRUE: BOOL;
const unique FALSE: BOOL;
const unique Asm: ref;
const unique ASM#Links : Field (Set ref);
const unique Native$TransientLink: TName;

const unique Type#String: TName;
const unique Type#Integer: TName;
const unique Type#Boolean: TName;
const unique Type#Ref: TName;

	// see org.eclipse.m2m.atl.engine.emfvm.lib.TransientLink
const unique TransientLink#source: Field (Map String ref);
const unique TransientLink#target: Field (Map String ref);
const unique TransientLink#rule: Field String;




function getFieldByName<alpha>(TName, alpha): Field alpha;
  axiom (getFieldByName(ER$Entity, _Field$name) == Entity.name);
  axiom (getFieldByName(ER$Entity, _Field$schema) == Entity.schema);
  axiom (getFieldByName(ER$ERAttribute, _Field$entity) == ERAttribute.entity);
  axiom (getFieldByName(ER$ERAttribute, _Field$relship) == ERAttribute.relship);
  axiom (getFieldByName(ER$ERAttribute, _Field$name) == ERAttribute.name);
  axiom (getFieldByName(ER$ERAttribute, _Field$isKey) == ERAttribute.isKey);
  axiom (getFieldByName(ER$RelshipEnd, _Field$entity) == RelshipEnd.entity);
  axiom (getFieldByName(ER$Relship, _Field$name) == Relship.name);
  axiom (getFieldByName(ER$Relship, _Field$schema) == Relship.schema);
  axiom (getFieldByName(ER$RelshipEnd, _Field$relship) == RelshipEnd.relship);
	
  axiom (getFieldByName(REL$RELAttribute, _Field$name) == RELAttribute.name);
  axiom (getFieldByName(REL$RELAttribute, _Field$isKey) == RELAttribute.isKey);
  axiom (getFieldByName(REL$RELAttribute, _Field$relation) == RELAttribute.relation);
  axiom (getFieldByName(REL$Relation, _Field$schema) == Relation.schema);
  axiom (getFieldByName(REL$Relation, _Field$name) == Relation.name);

  
// [mmName, className]
const classifierTable : [String, String] TName;
  axiom classifierTable[_ER, _Entity] == ER$Entity;
  axiom classifierTable[_ER, _Relship] == ER$Relship;
  axiom classifierTable[_ER, _ERSchema] == ER$ERSchema;
  axiom classifierTable[_ER, _ERAttribute] == ER$ERAttribute;
  axiom classifierTable[_ER, _RelshipEnd] == ER$RelshipEnd;

  axiom classifierTable[_REL, _RELAttribute] == REL$RELAttribute;
  axiom classifierTable[_REL, _Relation] == REL$Relation;
  axiom classifierTable[_REL, _RELSchema] == REL$RELSchema;
  
  axiom classifierTable[_#native, _TransientLink] == Native$TransientLink;



  