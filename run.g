tic := NanosecondsSinceEpoch;
toc := x->Int((NanosecondsSinceEpoch()-x)/1000000000);
Read("perfect.g");
Read("imf.g");
Read("qtbl.g");
LogOutputTo("run.out");
threshold:=10^6;
maxdim:=10;;
list:=[];;

Print("[1] Searching for mns subgroups of imf groups in dimension <=", maxdim," of order >=", threshold, ".\n");
t:=tic();;
for dim in [1..maxdim] do; MNSMakeDimMin(list, dim, threshold); od;
t:=toc(t);;
s:=Size(Concatenation(List(list, x->x.ccsr)));
Print("[1] Found ",  s, " groups.\n");
Print("[1] Time of calculations: ", t, "s.\n");

Print("[2] Searching for mns groups of order <=", threshold, " with faithful rational character of degree <=",maxdim,".\n");
t:=tic();;
mns := MNSPerfectGroupsMaxSize(threshold);;
mns:=Filtered( mns, id->HasFaithfulQIrr(PerfectGroup(id),maxdim));;
t:=toc(t);;
Print("[2] Found ", Size(mns), " groups.\n");
Print("[2] Time of calculations: ", t, "s.\n");

Print("[3] Calculating rational character tables of the groups.\n");
t:=tic();;
for id in mns do 
	tbl:=CharacterTableToRec(CharacterTable(PerfectGroup(id))); 
	tbl.Identifier:=PERFGRP[PerfGrpLoad(id[1])][id[2]][2]; 
	CharacterTableFromRec(tbl); 
	qtbl:=QCharacterTable(tbl); 
	Print("\n");
	Display(qtbl, rec(centralizers:=false, powermaps:=false)); 
	Print("\n"); 
od;
t:=toc(t);;
Print("[3] Time of calculations: ", t, "s\n");

