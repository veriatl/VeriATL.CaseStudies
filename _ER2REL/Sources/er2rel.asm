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
6:	getasm 
7:	pcall A.__matchEA2A():V 
8:	getasm 
9:	pcall A.__matchRA2A():V 
10:	getasm 
11:	pcall A.__matchRA2AK():V 
__exec__
	var: e:1
	var: e:1
	var: e:1
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
30:	getasm 
31:	get links 
32:	push EA2A 
33:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
34:	iterate 
35:	store 1 
36:	getasm 
37:	load 1 
38:	pcall A.__applyEA2A(NTransientLink;):V 
39:	enditerate 
40:	getasm 
41:	get links 
42:	push RA2A 
43:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
44:	iterate 
45:	store 1 
46:	getasm 
47:	load 1 
48:	pcall A.__applyRA2A(NTransientLink;):V 
49:	enditerate 
50:	getasm 
51:	get links 
52:	push RA2AK 
53:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
54:	iterate 
55:	store 1 
56:	getasm 
57:	load 1 
58:	pcall A.__applyRA2AK(NTransientLink;):V 
59:	enditerate 
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
__matchEA2A
	var: att:1
	var: ent:2
	var: self:0


0:	push ERAttribute 
1:	push ER 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	push Entity 
8:	push ER 
9:	findme 
10:	push IN 
11:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
12:	iterate 
13:	store 2 
14:	load 1 
15:	get entity 
16:	load 2 
17:	call J.=(J):J 
18:	call B.not():B 
19:	if 44 
20:	getasm 
21:	get links 
22:	push TransientLink 
23:	push #native 
24:	new 
25:	dup 
26:	push EA2A 
27:	pcall NTransientLink;.setRule(MATL!Rule;):V 
28:	dup 
29:	push att 
30:	load 1 
31:	pcall NTransientLink;.addSourceElement(SJ):V 
32:	dup 
33:	push ent 
34:	load 2 
35:	pcall NTransientLink;.addSourceElement(SJ):V 
36:	dup 
37:	push t 
38:	push RELAttribute 
39:	push REL 
40:	new 
41:	pcall NTransientLink;.addTargetElement(SJ):V 
42:	pusht 
43:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
44:	enditerate 
45:	enditerate 
__applyEA2A
	var: t:4
	var: att:2
	var: ent:3
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push att 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push ent 
6:	call NTransientLink;.getSourceElement(S):J 
7:	store 3 
8:	load 1 
9:	push t 
10:	call NTransientLink;.getTargetElement(S):J 
11:	store 4 
12:	load 4 
13:	dup 
14:	getasm 
15:	load 2 
16:	get name 
17:	call A.__resolve__(J):J 
18:	set name 
19:	dup 
20:	getasm 
21:	load 2 
22:	get isKey 
23:	call A.__resolve__(J):J 
24:	set isKey 
25:	dup 
26:	getasm 
27:	load 3 
28:	call A.__resolve__(J):J 
29:	set relation 
30:	pop 
__matchRA2A
	var: att:1
	var: rs:2
	var: self:0


0:	push ERAttribute 
1:	push ER 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	push Relship 
8:	push ER 
9:	findme 
10:	push IN 
11:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
12:	iterate 
13:	store 2 
14:	load 1 
15:	get relship 
16:	load 2 
17:	call J.=(J):J 
18:	call B.not():B 
19:	if 44 
20:	getasm 
21:	get links 
22:	push TransientLink 
23:	push #native 
24:	new 
25:	dup 
26:	push RA2A 
27:	pcall NTransientLink;.setRule(MATL!Rule;):V 
28:	dup 
29:	push att 
30:	load 1 
31:	pcall NTransientLink;.addSourceElement(SJ):V 
32:	dup 
33:	push rs 
34:	load 2 
35:	pcall NTransientLink;.addSourceElement(SJ):V 
36:	dup 
37:	push t 
38:	push RELAttribute 
39:	push REL 
40:	new 
41:	pcall NTransientLink;.addTargetElement(SJ):V 
42:	pusht 
43:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
44:	enditerate 
45:	enditerate 
__applyRA2A
	var: t:4
	var: att:2
	var: rs:3
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push att 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push rs 
6:	call NTransientLink;.getSourceElement(S):J 
7:	store 3 
8:	load 1 
9:	push t 
10:	call NTransientLink;.getTargetElement(S):J 
11:	store 4 
12:	load 4 
13:	dup 
14:	getasm 
15:	load 2 
16:	get name 
17:	call A.__resolve__(J):J 
18:	set name 
19:	dup 
20:	getasm 
21:	load 2 
22:	get isKey 
23:	call A.__resolve__(J):J 
24:	set isKey 
25:	dup 
26:	getasm 
27:	load 3 
28:	call A.__resolve__(J):J 
29:	set relation 
30:	pop 
__matchRA2AK
	var: att:1
	var: rse:2
	var: self:0


0:	push ERAttribute 
1:	push ER 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	push RelshipEnd 
8:	push ER 
9:	findme 
10:	push IN 
11:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
12:	iterate 
13:	store 2 
14:	load 1 
15:	get entity 
16:	load 2 
17:	get entity 
18:	call J.=(J):J 
19:	load 1 
20:	get isKey 
21:	pusht 
22:	call J.=(J):J 
23:	call J.and(J):J 
24:	call B.not():B 
25:	if 50 
26:	getasm 
27:	get links 
28:	push TransientLink 
29:	push #native 
30:	new 
31:	dup 
32:	push RA2AK 
33:	pcall NTransientLink;.setRule(MATL!Rule;):V 
34:	dup 
35:	push att 
36:	load 1 
37:	pcall NTransientLink;.addSourceElement(SJ):V 
38:	dup 
39:	push rse 
40:	load 2 
41:	pcall NTransientLink;.addSourceElement(SJ):V 
42:	dup 
43:	push t 
44:	push RELAttribute 
45:	push REL 
46:	new 
47:	pcall NTransientLink;.addTargetElement(SJ):V 
48:	pusht 
49:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
50:	enditerate 
51:	enditerate 
__applyRA2AK
	var: t:4
	var: att:2
	var: rse:3
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push att 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push rse 
6:	call NTransientLink;.getSourceElement(S):J 
7:	store 3 
8:	load 1 
9:	push t 
10:	call NTransientLink;.getTargetElement(S):J 
11:	store 4 
12:	load 4 
13:	dup 
14:	getasm 
15:	load 2 
16:	get name 
17:	call A.__resolve__(J):J 
18:	set name 
19:	dup 
20:	getasm 
21:	load 2 
22:	get isKey 
23:	call A.__resolve__(J):J 
24:	set isKey 
25:	dup 
26:	getasm 
27:	load 3 
28:	get relship 
29:	call A.__resolve__(J):J 
30:	set relation 
31:	pop 
