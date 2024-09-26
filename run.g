tic := NanosecondsSinceEpoch;
toc := x->Int((NanosecondsSinceEpoch()-x)/1000000000);
Reread("perfect.g");
Reread("imf.g");
Reread("qtbl.g");

step1 := function(m,t,v)
    local list, dim;

    list := [];
    for dim in [1..m] do
        MNSMakeDimMin(list, dim, t, v); 
    od;
    return Concatenation(List(list, x->x.ccsr));
end;

step21 := function(t)
    return MNSPerfectGroupsMaxSize(t);
end;
step22 := function(mns, m)
    return Filtered( mns, id->HasFaithfulQIrr(PerfectGroup(id),m));
end;
step2 := function(m,t)
    local mns;
    mns := step21(t);
    return step22(mns, m);
end;

step3 := function(mns)
    local id, tbl, qtbl, qtbls;
    qtbls := [];
    for id in mns do 
        tbl:=CharacterTableToRec(CharacterTable(PerfectGroup(id))); 
        tbl.Identifier:=PERFGRP[PerfGrpLoad(id[1])][id[2]][2]; 
        CharacterTableFromRec(tbl); 
        qtbl:=QCharacterTable(tbl);
        Add(qtbls, qtbl);
        Print("\nPG.", id[1], ".", id[2], "\n" );
        Display(qtbl, rec(centralizers:=false, powermaps:=false)); 
        Print("\n"); 
    od;
    return qtbls;
end;

run := function(maxdim, threshold, verbose)
    local t, r;

    LogOutputTo("run.out");

    r := rec();
    
    Print("[1] Searching for mns subgroups of imf groups in dimension <=", maxdim," of order >=", threshold, ".\n");
    t:=tic();;
    r.groups:=step1(maxdim, threshold, verbose);
    t:=toc(t);;
    Print("[1] Found ",  Size(r.groups), " groups.\n");
    Print("[1] Time of calculations: ", t, "s.\n");

    Print("[2] Searching for mns groups of order <=", threshold, " with faithful rational character of degree <=",maxdim,".\n");
    t:=tic();;
    r.mnsid := step2(maxdim, threshold);
    t:=toc(t);;
    Print("[2] Found ", Size(r.mnsid), " groups.\n");
    Print("[2] Time of calculations: ", t, "s.\n");
    Print("[2] The groups' perfect ids: ", r.mnsid, "\n");

    Print("[3] Calculating rational character tables of the groups.\n");
    t:=tic();;
    r.qtbls := step3(r.mnsid);;
    t:=toc(t);;
    Print("[3] Time of calculations: ", t, "s\n");

    LogOutputTo();

    return r;
end;
