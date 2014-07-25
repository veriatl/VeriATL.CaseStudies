17
main
	var: self:0


getasm 
push OclParametrizedType 
push #native 
new 
dup 
push Collection 
pcall J.setName(S):V 
dup 
push OclSimpleType 
push #native 
new 
dup 
push OclAny 
pcall J.setName(S):V 
pcall J.setElementType(J):V 
set col 
getasm 
push TransientLinkSet 
push #native 
new 
set links 
getasm 
pcall A.__matcher__():V 
getasm 
pcall A.__exec__():V 
__resolve__
	var: e:2
	var: self:0
	var: value:1

	param: 1:J

load 1 
getasm 
get col 
call J.oclIsKindOf(J):B 
if 18 
getasm 
get links 
load 1 
call NTransientLinkSet;.getLinkBySourceElement(S):QNTransientLink; 
dup 
call J.oclIsUndefined():B 
if 15 
load 1 
call NTransientLink;.getTargetFromSource(J):J 
goto 17 
pop 
load 1 
goto 30 
push Sequence 
push #native 
new 
load 1 
iterate 
store 2 
getasm 
load 2 
call A.__resolve__(J):J 
call QJ.including(J):QJ 
enditerate 
call QJ.flatten():QJ 
resolveTemp
	var: self:0
	var: value:1
	var: name:2

	param: 1:J
	param: 2:S

getasm 
get links 
load 1 
call NTransientLinkSet;.getLinkBySourceElement(S):QNTransientLink; 
load 1 
load 2 
call NTransientLink;.getNamedTargetFromSource(JS):J 
__matcher__
	var: self:0


getasm 
pcall A.__matchS2S():V 
getasm 
pcall A.__matchE2R():V 
getasm 
pcall A.__matchR2R():V 
getasm 
pcall A.__matchEA2A():V 
getasm 
pcall A.__matchRA2A():V 
getasm 
pcall A.__matchRA2AK():V 
__exec__
	var: e:1
	var: e:1
	var: e:1
	var: e:1
	var: e:1
	var: e:1
	var: self:0


getasm 
get links 
push S2S 
call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
iterate 
store 1 
getasm 
load 1 
pcall A.__applyS2S(NTransientLink;):V 
enditerate 
getasm 
get links 
push E2R 
call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
iterate 
store 1 
getasm 
load 1 
pcall A.__applyE2R(NTransientLink;):V 
enditerate 
getasm 
get links 
push R2R 
call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
iterate 
store 1 
getasm 
load 1 
pcall A.__applyR2R(NTransientLink;):V 
enditerate 
getasm 
get links 
push EA2A 
call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
iterate 
store 1 
getasm 
load 1 
pcall A.__applyEA2A(NTransientLink;):V 
enditerate 
getasm 
get links 
push RA2A 
call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
iterate 
store 1 
getasm 
load 1 
pcall A.__applyRA2A(NTransientLink;):V 
enditerate 
getasm 
get links 
push RA2AK 
call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
iterate 
store 1 
getasm 
load 1 
pcall A.__applyRA2AK(NTransientLink;):V 
enditerate 
__matchS2S
	var: s:1
	var: self:0


push ERSchema 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 1 
getasm 
get links 
push TransientLink 
push #native 
new 
dup 
push S2S 
pcall NTransientLink;.setRule(MATL!Rule;):V 
dup 
push s 
load 1 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push t 
push RELSchema 
push REL 
new 
pcall NTransientLink;.addTargetElement(SJ):V 
pusht 
pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
enditerate 
__applyS2S
	var: t:3
	var: s:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

load 1 
push s 
call NTransientLink;.getSourceElement(S):J 
store 2 
load 1 
push t 
call NTransientLink;.getTargetElement(S):J 
store 3 
load 3 
pop 
__matchE2R
	var: s:1
	var: self:0


push Entity 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 1 
getasm 
get links 
push TransientLink 
push #native 
new 
dup 
push E2R 
pcall NTransientLink;.setRule(MATL!Rule;):V 
dup 
push s 
load 1 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push t 
push Relation 
push REL 
new 
pcall NTransientLink;.addTargetElement(SJ):V 
pusht 
pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
enditerate 
__applyE2R
	var: t:3
	var: s:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

load 1 
push s 
call NTransientLink;.getSourceElement(S):J 
store 2 
load 1 
push t 
call NTransientLink;.getTargetElement(S):J 
store 3 
load 3 
dup 
getasm 
load 2 
get name 
call A.__resolve__(J):J 
set name 
dup 
getasm 
load 2 
get schema 
call A.__resolve__(J):J 
set schema 
pop 
__matchR2R
	var: s:1
	var: self:0


push Relship 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 1 
getasm 
get links 
push TransientLink 
push #native 
new 
dup 
push R2R 
pcall NTransientLink;.setRule(MATL!Rule;):V 
dup 
push s 
load 1 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push t 
push Relation 
push REL 
new 
pcall NTransientLink;.addTargetElement(SJ):V 
pusht 
pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
enditerate 
__applyR2R
	var: t:3
	var: s:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

load 1 
push s 
call NTransientLink;.getSourceElement(S):J 
store 2 
load 1 
push t 
call NTransientLink;.getTargetElement(S):J 
store 3 
load 3 
dup 
getasm 
load 2 
get name 
call A.__resolve__(J):J 
set name 
dup 
getasm 
load 2 
get schema 
call A.__resolve__(J):J 
set schema 
pop 
__matchEA2A
	var: att:1
	var: ent:2
	var: self:0


push ERAttribute 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 1 
push Entity 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 2 
load 1 
get entity 
load 2 
call J.=(J):J 
call B.not():B 
if 44 
getasm 
get links 
push TransientLink 
push #native 
new 
dup 
push EA2A 
pcall NTransientLink;.setRule(MATL!Rule;):V 
dup 
push att 
load 1 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push ent 
load 2 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push t 
push RELAttribute 
push REL 
new 
pcall NTransientLink;.addTargetElement(SJ):V 
pusht 
pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
enditerate 
enditerate 
__applyEA2A
	var: t:4
	var: att:2
	var: ent:3
	var: self:0
	var: link:1

	param: 1:NTransientLink;

load 1 
push att 
call NTransientLink;.getSourceElement(S):J 
store 2 
load 1 
push ent 
call NTransientLink;.getSourceElement(S):J 
store 3 
load 1 
push t 
call NTransientLink;.getTargetElement(S):J 
store 4 
load 4 
dup 
getasm 
load 2 
get name 
call A.__resolve__(J):J 
set name 
dup 
getasm 
load 2 
get isKey 
call A.__resolve__(J):J 
set isKey 
dup 
getasm 
load 3 
call A.__resolve__(J):J 
set relation 
pop 
__matchRA2A
	var: att:1
	var: rs:2
	var: self:0


push ERAttribute 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 1 
push Relship 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 2 
load 1 
get relship 
load 2 
call J.=(J):J 
call B.not():B 
if 44 
getasm 
get links 
push TransientLink 
push #native 
new 
dup 
push RA2A 
pcall NTransientLink;.setRule(MATL!Rule;):V 
dup 
push att 
load 1 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push rs 
load 2 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push t 
push RELAttribute 
push REL 
new 
pcall NTransientLink;.addTargetElement(SJ):V 
pusht 
pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
enditerate 
enditerate 
__applyRA2A
	var: t:4
	var: att:2
	var: rs:3
	var: self:0
	var: link:1

	param: 1:NTransientLink;

load 1 
push att 
call NTransientLink;.getSourceElement(S):J 
store 2 
load 1 
push rs 
call NTransientLink;.getSourceElement(S):J 
store 3 
load 1 
push t 
call NTransientLink;.getTargetElement(S):J 
store 4 
load 4 
dup 
getasm 
load 2 
get name 
call A.__resolve__(J):J 
set name 
dup 
getasm 
load 2 
get isKey 
call A.__resolve__(J):J 
set isKey 
dup 
getasm 
load 3 
call A.__resolve__(J):J 
set relation 
pop 
__matchRA2AK
	var: att:1
	var: rse:2
	var: self:0


push ERAttribute 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 1 
push RelshipEnd 
push ER 
findme 
push IN 
call MMOF!Classifier;.allInstancesFrom(S):QJ 
iterate 
store 2 
load 1 
get entity 
load 2 
get entity 
call J.=(J):J 
load 1 
get isKey 
pusht 
call J.=(J):J 
call J.and(J):J 
call B.not():B 
if 50 
getasm 
get links 
push TransientLink 
push #native 
new 
dup 
push RA2AK 
pcall NTransientLink;.setRule(MATL!Rule;):V 
dup 
push att 
load 1 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push rse 
load 2 
pcall NTransientLink;.addSourceElement(SJ):V 
dup 
push t 
push RELAttribute 
push REL 
new 
pcall NTransientLink;.addTargetElement(SJ):V 
pusht 
pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
enditerate 
enditerate 
__applyRA2AK
	var: t:4
	var: att:2
	var: rse:3
	var: self:0
	var: link:1

	param: 1:NTransientLink;

load 1 
push att 
call NTransientLink;.getSourceElement(S):J 
store 2 
load 1 
push rse 
call NTransientLink;.getSourceElement(S):J 
store 3 
load 1 
push t 
call NTransientLink;.getTargetElement(S):J 
store 4 
load 4 
dup 
getasm 
load 2 
get name 
call A.__resolve__(J):J 
set name 
dup 
getasm 
load 2 
get isKey 
call A.__resolve__(J):J 
set isKey 
dup 
getasm 
load 3 
get relship 
call A.__resolve__(J):J 
set relation 
pop 
