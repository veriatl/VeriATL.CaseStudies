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
1:	pcall A.__matchSM2SM():V 
2:	getasm 
3:	pcall A.__matchRS2RS():V 
4:	getasm 
5:	pcall A.__matchIS2IS():V 
6:	getasm 
7:	pcall A.__matchIS2RS():V 
8:	getasm 
9:	pcall A.__matchT2TA():V 
10:	getasm 
11:	pcall A.__matchT2TB():V 
12:	getasm 
13:	pcall A.__matchT2TC():V 
__exec__
	var: e:1
	var: e:1
	var: e:1
	var: e:1
	var: e:1
	var: e:1
	var: e:1
	var: self:0


0:	getasm 
1:	get links 
2:	push SM2SM 
3:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
4:	iterate 
5:	store 1 
6:	getasm 
7:	load 1 
8:	pcall A.__applySM2SM(NTransientLink;):V 
9:	enditerate 
10:	getasm 
11:	get links 
12:	push RS2RS 
13:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
14:	iterate 
15:	store 1 
16:	getasm 
17:	load 1 
18:	pcall A.__applyRS2RS(NTransientLink;):V 
19:	enditerate 
20:	getasm 
21:	get links 
22:	push IS2IS 
23:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
24:	iterate 
25:	store 1 
26:	getasm 
27:	load 1 
28:	pcall A.__applyIS2IS(NTransientLink;):V 
29:	enditerate 
30:	getasm 
31:	get links 
32:	push IS2RS 
33:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
34:	iterate 
35:	store 1 
36:	getasm 
37:	load 1 
38:	pcall A.__applyIS2RS(NTransientLink;):V 
39:	enditerate 
40:	getasm 
41:	get links 
42:	push T2TA 
43:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
44:	iterate 
45:	store 1 
46:	getasm 
47:	load 1 
48:	pcall A.__applyT2TA(NTransientLink;):V 
49:	enditerate 
50:	getasm 
51:	get links 
52:	push T2TB 
53:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
54:	iterate 
55:	store 1 
56:	getasm 
57:	load 1 
58:	pcall A.__applyT2TB(NTransientLink;):V 
59:	enditerate 
60:	getasm 
61:	get links 
62:	push T2TC 
63:	call NTransientLinkSet;.getLinksByRule(S):QNTransientLink; 
64:	iterate 
65:	store 1 
66:	getasm 
67:	load 1 
68:	pcall A.__applyT2TC(NTransientLink;):V 
69:	enditerate 
__matchSM2SM
	var: sm1:1
	var: self:0


0:	push StateMachine 
1:	push HSM 
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
13:	push SM2SM 
14:	pcall NTransientLink;.setRule(MATL!Rule;):V 
15:	dup 
16:	push sm1 
17:	load 1 
18:	pcall NTransientLink;.addSourceElement(SJ):V 
19:	dup 
20:	push sm2 
21:	push StateMachine 
22:	push FSM 
23:	new 
24:	pcall NTransientLink;.addTargetElement(SJ):V 
25:	pusht 
26:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
27:	enditerate 
__applySM2SM
	var: sm2:3
	var: sm1:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push sm1 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push sm2 
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
__matchRS2RS
	var: rs1:1
	var: self:0


0:	push RegularState 
1:	push HSM 
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
13:	push RS2RS 
14:	pcall NTransientLink;.setRule(MATL!Rule;):V 
15:	dup 
16:	push rs1 
17:	load 1 
18:	pcall NTransientLink;.addSourceElement(SJ):V 
19:	dup 
20:	push rs2 
21:	push RegularState 
22:	push FSM 
23:	new 
24:	pcall NTransientLink;.addTargetElement(SJ):V 
25:	pusht 
26:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
27:	enditerate 
__applyRS2RS
	var: rs2:3
	var: rs1:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push rs1 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push rs2 
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
18:	get stateMachine 
19:	call A.__resolve__(J):J 
20:	set stateMachine 
21:	pop 
__matchIS2IS
	var: is1:1
	var: self:0


0:	push InitialState 
1:	push HSM 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	load 1 
8:	get compositeState 
9:	call J.oclIsUndefined():J 
10:	call B.not():B 
11:	if 32 
12:	getasm 
13:	get links 
14:	push TransientLink 
15:	push #native 
16:	new 
17:	dup 
18:	push IS2IS 
19:	pcall NTransientLink;.setRule(MATL!Rule;):V 
20:	dup 
21:	push is1 
22:	load 1 
23:	pcall NTransientLink;.addSourceElement(SJ):V 
24:	dup 
25:	push is2 
26:	push InitialState 
27:	push FSM 
28:	new 
29:	pcall NTransientLink;.addTargetElement(SJ):V 
30:	pusht 
31:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
32:	enditerate 
__applyIS2IS
	var: is2:3
	var: is1:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push is1 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push is2 
6:	call NTransientLink;.getTargetElement(S):J 
7:	store 3 
8:	load 3 
9:	dup 
10:	getasm 
11:	load 2 
12:	get stateMachine 
13:	call A.__resolve__(J):J 
14:	set stateMachine 
15:	dup 
16:	getasm 
17:	load 2 
18:	get name 
19:	call A.__resolve__(J):J 
20:	set name 
21:	pop 
__matchIS2RS
	var: is1:1
	var: self:0


0:	push InitialState 
1:	push HSM 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	load 1 
8:	get compositeState 
9:	call J.oclIsUndefined():J 
10:	call J.not():J 
11:	call B.not():B 
12:	if 33 
13:	getasm 
14:	get links 
15:	push TransientLink 
16:	push #native 
17:	new 
18:	dup 
19:	push IS2RS 
20:	pcall NTransientLink;.setRule(MATL!Rule;):V 
21:	dup 
22:	push is1 
23:	load 1 
24:	pcall NTransientLink;.addSourceElement(SJ):V 
25:	dup 
26:	push is2 
27:	push RegularState 
28:	push FSM 
29:	new 
30:	pcall NTransientLink;.addTargetElement(SJ):V 
31:	pusht 
32:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
33:	enditerate 
__applyIS2RS
	var: is2:3
	var: is1:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push is1 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push is2 
6:	call NTransientLink;.getTargetElement(S):J 
7:	store 3 
8:	load 3 
9:	dup 
10:	getasm 
11:	load 2 
12:	get stateMachine 
13:	call A.__resolve__(J):J 
14:	set stateMachine 
15:	dup 
16:	getasm 
17:	load 2 
18:	get name 
19:	call A.__resolve__(J):J 
20:	set name 
21:	pop 
__matchT2TA
	var: t1:1
	var: self:0


0:	push Transition 
1:	push HSM 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	load 1 
8:	get source 
9:	push CompositeState 
10:	push HSM 
11:	findme 
12:	call J.oclIsTypeOf(J):J 
13:	call J.not():J 
14:	load 1 
15:	get target 
16:	push CompositeState 
17:	push HSM 
18:	findme 
19:	call J.oclIsTypeOf(J):J 
20:	call J.not():J 
21:	call J.and(J):J 
22:	call B.not():B 
23:	if 44 
24:	getasm 
25:	get links 
26:	push TransientLink 
27:	push #native 
28:	new 
29:	dup 
30:	push T2TA 
31:	pcall NTransientLink;.setRule(MATL!Rule;):V 
32:	dup 
33:	push t1 
34:	load 1 
35:	pcall NTransientLink;.addSourceElement(SJ):V 
36:	dup 
37:	push t2 
38:	push Transition 
39:	push FSM 
40:	new 
41:	pcall NTransientLink;.addTargetElement(SJ):V 
42:	pusht 
43:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
44:	enditerate 
__applyT2TA
	var: t2:3
	var: t1:2
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push t1 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push t2 
6:	call NTransientLink;.getTargetElement(S):J 
7:	store 3 
8:	load 3 
9:	dup 
10:	getasm 
11:	load 2 
12:	get label 
13:	call A.__resolve__(J):J 
14:	set label 
15:	dup 
16:	getasm 
17:	load 2 
18:	get stateMachine 
19:	call A.__resolve__(J):J 
20:	set stateMachine 
21:	dup 
22:	getasm 
23:	load 2 
24:	get source 
25:	call A.__resolve__(J):J 
26:	set source 
27:	dup 
28:	getasm 
29:	load 2 
30:	get target 
31:	call A.__resolve__(J):J 
32:	set target 
33:	pop 
__matchT2TB
	var: t1:1
	var: src:2
	var: trg:3
	var: c:4
	var: self:0


0:	push Transition 
1:	push HSM 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	push CompositeState 
8:	push HSM 
9:	findme 
10:	push IN 
11:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
12:	iterate 
13:	store 2 
14:	push AbstractState 
15:	push HSM 
16:	findme 
17:	push IN 
18:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
19:	iterate 
20:	store 3 
21:	push AbstractState 
22:	push HSM 
23:	findme 
24:	push IN 
25:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
26:	iterate 
27:	store 4 
28:	load 1 
29:	get source 
30:	load 2 
31:	call J.=(J):J 
32:	load 1 
33:	get target 
34:	load 3 
35:	call J.=(J):J 
36:	call J.and(J):J 
37:	load 4 
38:	get compositeState 
39:	load 2 
40:	call J.=(J):J 
41:	call J.and(J):J 
42:	load 3 
43:	push CompositeState 
44:	push HSM 
45:	findme 
46:	call J.oclIsTypeOf(J):J 
47:	call J.not():J 
48:	call J.and(J):J 
49:	call B.not():B 
50:	if 83 
51:	getasm 
52:	get links 
53:	push TransientLink 
54:	push #native 
55:	new 
56:	dup 
57:	push T2TB 
58:	pcall NTransientLink;.setRule(MATL!Rule;):V 
59:	dup 
60:	push t1 
61:	load 1 
62:	pcall NTransientLink;.addSourceElement(SJ):V 
63:	dup 
64:	push src 
65:	load 2 
66:	pcall NTransientLink;.addSourceElement(SJ):V 
67:	dup 
68:	push trg 
69:	load 3 
70:	pcall NTransientLink;.addSourceElement(SJ):V 
71:	dup 
72:	push c 
73:	load 4 
74:	pcall NTransientLink;.addSourceElement(SJ):V 
75:	dup 
76:	push t2 
77:	push Transition 
78:	push FSM 
79:	new 
80:	pcall NTransientLink;.addTargetElement(SJ):V 
81:	pusht 
82:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
83:	enditerate 
84:	enditerate 
85:	enditerate 
86:	enditerate 
__applyT2TB
	var: t2:6
	var: t1:2
	var: src:3
	var: trg:4
	var: c:5
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push t1 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push src 
6:	call NTransientLink;.getSourceElement(S):J 
7:	store 3 
8:	load 1 
9:	push trg 
10:	call NTransientLink;.getSourceElement(S):J 
11:	store 4 
12:	load 1 
13:	push c 
14:	call NTransientLink;.getSourceElement(S):J 
15:	store 5 
16:	load 1 
17:	push t2 
18:	call NTransientLink;.getTargetElement(S):J 
19:	store 6 
20:	load 6 
21:	dup 
22:	getasm 
23:	load 2 
24:	get label 
25:	call A.__resolve__(J):J 
26:	set label 
27:	dup 
28:	getasm 
29:	load 2 
30:	get stateMachine 
31:	call A.__resolve__(J):J 
32:	set stateMachine 
33:	dup 
34:	getasm 
35:	load 5 
36:	call A.__resolve__(J):J 
37:	set source 
38:	dup 
39:	getasm 
40:	load 4 
41:	call A.__resolve__(J):J 
42:	set target 
43:	pop 
__matchT2TC
	var: t1:1
	var: src:2
	var: trg:3
	var: c:4
	var: self:0


0:	push Transition 
1:	push HSM 
2:	findme 
3:	push IN 
4:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
5:	iterate 
6:	store 1 
7:	push AbstractState 
8:	push HSM 
9:	findme 
10:	push IN 
11:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
12:	iterate 
13:	store 2 
14:	push CompositeState 
15:	push HSM 
16:	findme 
17:	push IN 
18:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
19:	iterate 
20:	store 3 
21:	push InitialState 
22:	push HSM 
23:	findme 
24:	push IN 
25:	call MMOF!Classifier;.allInstancesFrom(S):QJ 
26:	iterate 
27:	store 4 
28:	load 1 
29:	get source 
30:	load 2 
31:	call J.=(J):J 
32:	load 1 
33:	get target 
34:	load 3 
35:	call J.=(J):J 
36:	call J.and(J):J 
37:	load 4 
38:	get compositeState 
39:	load 3 
40:	call J.=(J):J 
41:	call J.and(J):J 
42:	load 2 
43:	push CompositeState 
44:	push HSM 
45:	findme 
46:	call J.oclIsTypeOf(J):J 
47:	call J.not():J 
48:	call J.and(J):J 
49:	call B.not():B 
50:	if 83 
51:	getasm 
52:	get links 
53:	push TransientLink 
54:	push #native 
55:	new 
56:	dup 
57:	push T2TC 
58:	pcall NTransientLink;.setRule(MATL!Rule;):V 
59:	dup 
60:	push t1 
61:	load 1 
62:	pcall NTransientLink;.addSourceElement(SJ):V 
63:	dup 
64:	push src 
65:	load 2 
66:	pcall NTransientLink;.addSourceElement(SJ):V 
67:	dup 
68:	push trg 
69:	load 3 
70:	pcall NTransientLink;.addSourceElement(SJ):V 
71:	dup 
72:	push c 
73:	load 4 
74:	pcall NTransientLink;.addSourceElement(SJ):V 
75:	dup 
76:	push t2 
77:	push Transition 
78:	push FSM 
79:	new 
80:	pcall NTransientLink;.addTargetElement(SJ):V 
81:	pusht 
82:	pcall NTransientLinkSet;.addLink2(NTransientLink;B):V 
83:	enditerate 
84:	enditerate 
85:	enditerate 
86:	enditerate 
__applyT2TC
	var: t2:6
	var: t1:2
	var: src:3
	var: trg:4
	var: c:5
	var: self:0
	var: link:1

	param: 1:NTransientLink;

0:	load 1 
1:	push t1 
2:	call NTransientLink;.getSourceElement(S):J 
3:	store 2 
4:	load 1 
5:	push src 
6:	call NTransientLink;.getSourceElement(S):J 
7:	store 3 
8:	load 1 
9:	push trg 
10:	call NTransientLink;.getSourceElement(S):J 
11:	store 4 
12:	load 1 
13:	push c 
14:	call NTransientLink;.getSourceElement(S):J 
15:	store 5 
16:	load 1 
17:	push t2 
18:	call NTransientLink;.getTargetElement(S):J 
19:	store 6 
20:	load 6 
21:	dup 
22:	getasm 
23:	load 2 
24:	get label 
25:	call A.__resolve__(J):J 
26:	set label 
27:	dup 
28:	getasm 
29:	load 2 
30:	get stateMachine 
31:	call A.__resolve__(J):J 
32:	set stateMachine 
33:	dup 
34:	getasm 
35:	load 3 
36:	call A.__resolve__(J):J 
37:	set source 
38:	dup 
39:	getasm 
40:	load 5 
41:	call A.__resolve__(J):J 
42:	set target 
43:	pop 
