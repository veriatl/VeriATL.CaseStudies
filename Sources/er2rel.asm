main
	var: self:0


0:	getasm 
1:	push OclParametrizedType 
2:	push #native 
3:	new 
4:	dup 
5:	push Collection 
6:	pcall J.setName(S):V 
7:	dup 
8:	push OclSimpleType 
9:	push #native 
10:	new 
11:	dup 
12:	push OclAny 
13:	pcall J.setName(S):V 
14:	pcall J.setElementType(J):V 
15:	set col 
16:	getasm 
17:	push TransientLinkSet 
18:	push #native 
19:	new 
20:	set links 
21:	getasm 
22:	pcall A.__matcher__():V 
23:	getasm 
24:	pcall A.__exec__():V 
__resolve__
	var: e:2
	var: self:0
	var: value:1

	param: 1:J

0:	load 1 
1:	getasm 
2:	get col 
3:	call J.oclIsKindOf(J):B 
4:	if 18 
5:	getasm 
6:	get links 
7:	load 1 
8:	call NTransientLinkSet;.getLinkBySourceElement(S):QNTransientLink; 
9:	dup 
10:	call J.oclIsUndefined():B 
11:	if 15 
12:	load 1 
13:	call NTransientLink;.getTargetFromSource(J):J 
14:	goto 17 
15:	pop 
16:	load 1 
17:	goto 30 
18:	push Sequence 
19:	push #native 
20:	new 
21:	load 1 
22:	iterate 
23:	store 2 
24:	getasm 
25:	load 2 
26:	call A.__resolve__(J):J 
27:	call QJ.including(J):QJ 
28:	enditerate 
29:	call QJ.flatten():QJ 
resolveTemp
	var: self:0
	var: value:1
	var: name:2

	param: 1:J
	param: 2:S

0:	getasm 
1:	get links 
2:	load 1 
3:	call NTransientLinkSet;.getLinkBySourceElement(S):QNTransientLink; 
4:	load 1 
5:	load 2 
6:	call NTransientLink;.getNamedTargetFromSource(JS):J 
__matcher__
	var: self:0


0:	getasm 
1:	pcall A.__matchS2S():V 
2:	getasm 
3:	pcall A.__matchE2R():V 
4:	getasm 
5:	pcall A.__matchR2R():V 
__exec__
	var: e:1
	var: e:1
	var: e:1
	var: self:0


0:	getasm 
1:	get links 
2:	push S2S 
3:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
4:	iterate 
5:	store 1 
6:	getasm 
7:	load 1 
8:	pcall A.__applyS2S(NTransientLink;):V 
9:	enditerate 
10:	getasm 
11:	get links 
12:	push E2R 
13:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
14:	iterate 
15:	store 1 
16:	getasm 
17:	load 1 
18:	pcall A.__applyE2R(NTransientLink;):V 
19:	enditerate 
20:	getasm 
21:	get links 
22:	push R2R 
23:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
24:	iterate 
25:	store 1 
26:	getasm 
27:	load 1 
28:	pcall A.__applyR2R(NTransientLink;):V 
29:	enditerate 
__matchS2S
	var: s:1
	var: self:0


0:	push ERSchema 
1:	push ER 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	getasm 
8:	get links 
9:	push TransientLink 
10:	push #native 
11:	new 
12:	dup 
13:	push S2S 
14:	pcall NTransientLink;.setRule(MATL!Rule;):V 
15:	dup 
16:	push s 
17:	load 1 
18:	pcall NTransientLink;.addSourceElement(SJ):V 
19:	dup 
20:	push t 
21:	push RELSchema 
22:	push REL 
23:	new 
24:	pcall NTransientLink;.addTargetElement(SJ):V 
25:	pusht 
26:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
27:	enditerate 
__applyS2S
	var: t:3
	var: s:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push s 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push t 
6:	call NTransientLink;.getTargetElement(S):J 
7:	store 3 
8:	load 3 
9:	dup 
10:	getasm 
11:	load 2 
12:	get name 
13:	call A.__resolve__(J):J 
14:	set name 
15:	dup 
16:	getasm 
17:	load 2 
18:	get entities 
19:	call A.__resolve__(J):J 
20:	set relations 
21:	dup 
22:	getasm 
23:	load 2 
24:	get relships 
25:	call A.__resolve__(J):J 
26:	set relations 
27:	pop 
__matchE2R
	var: s:1
	var: self:0


0:	push Entity 
1:	push ER 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	getasm 
8:	get links 
9:	push TransientLink 
10:	push #native 
11:	new 
12:	dup 
13:	push E2R 
14:	pcall NTransientLink;.setRule(MATL!Rule;):V 
15:	dup 
16:	push s 
17:	load 1 
18:	pcall NTransientLink;.addSourceElement(SJ):V 
19:	dup 
20:	push t 
21:	push Relation 
22:	push REL 
23:	new 
24:	pcall NTransientLink;.addTargetElement(SJ):V 
25:	pusht 
26:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
27:	enditerate 
__applyE2R
	var: t:3
	var: s:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push s 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push t 
6:	call NTransientLink;.getTargetElement(S):J 
7:	store 3 
8:	load 3 
9:	dup 
10:	getasm 
11:	load 2 
12:	get name 
13:	call A.__resolve__(J):J 
14:	set name 
15:	pop 
__matchR2R
	var: s:1
	var: self:0


0:	push Relship 
1:	push ER 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	getasm 
8:	get links 
9:	push TransientLink 
10:	push #native 
11:	new 
12:	dup 
13:	push R2R 
14:	pcall NTransientLink;.setRule(MATL!Rule;):V 
15:	dup 
16:	push s 
17:	load 1 
18:	pcall NTransientLink;.addSourceElement(SJ):V 
19:	dup 
20:	push t 
21:	push Relation 
22:	push REL 
23:	new 
24:	pcall NTransientLink;.addTargetElement(SJ):V 
25:	pusht 
26:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
27:	enditerate 
__applyR2R
	var: t:3
	var: s:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push s 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push t 
6:	call NTransientLink;.getTargetElement(S):J 
7:	store 3 
8:	load 3 
9:	dup 
10:	getasm 
11:	load 2 
12:	get name 
13:	call A.__resolve__(J):J 
14:	set name 
15:	pop 
