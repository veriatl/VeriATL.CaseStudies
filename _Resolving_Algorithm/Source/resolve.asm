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