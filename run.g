tic := NanosecondsSinceEpoch;
toc := x->Int((NanosecondsSinceEpoch()-x)/1000000000);
Reread("perfect.g");
Reread("imf.g");
Reread("qtbl.g");

# use the "first divide by the solvable radical" method
SetMNSFindMinOp(ConjugacyClassRepsMNSBySolvableRadical);

step1 := function(m,t,v)
    local list, dim;

    list := [];
    for dim in [1..m] do
        MNSMakeDimMin(list, dim, t, v); 
    od;
    return Concatenation(List(list, x->x.ccsr));
end;

step2 := function(t)
    return MNSPerfectGroupsMaxSize(t);
end;
step3 := function(mns, m)
    return Filtered( mns, id->HasFaithfulQIrr(PerfectGroup(id),m));
end;

step4 := function(mns, verbose)
    local id, tbl, qtbl, qtbls;
    qtbls := [];
    for id in mns do 
        tbl:=CharacterTableToRec(CharacterTable(PerfectGroup(id))); 
        tbl.Identifier:=PERFGRP[PerfGrpLoad(id[1])][id[2]][2]; 
        CharacterTableFromRec(tbl); 
        qtbl:=QCharacterTable(tbl);
        Add(qtbls, qtbl);
        if verbose then
            Print("\nPG.", id[1], ".", id[2], "\n" );
            Display(qtbl, rec(centralizers:=false, powermaps:=false)); 
            Print("\n");
        fi;
    od;
    return qtbls;
end;

run := function(arg)
    local t, r, maxdim, threshold, verbose, print, display;

    maxdim := arg[1];
    threshold := arg[2];

    verbose := false;
    print := function(arg)
        return ;
    end;
    display := function(arg)
        return ;
    end;
    if Size(arg)>2 then
        if not arg[3] in [0,1,2,3] then
            Error("Usage: run(maxdim, threshold[, verbose level])\n");
        fi;
        if arg[3]>=1 then
            display := Display;
        fi;
        if arg[3]>=2 then
            print := Print;
        fi;
        if arg[3]=3 then
            verbose:=true;
        fi;
    fi;

    LogOutputTo("run.out");

    r := rec();
    
    print("[1] Searching for mns subgroups of imf groups in dimension <=", maxdim," of order >=", threshold, ".\n");
    t:=tic();;
    r.imfsg:=step1(maxdim, threshold, verbose);
    # Be careful here - PerfectIdentification and the orders of perfect groups
    r.tmpid:=SSortedList(r.imfsg, PerfectIdentification);
    t:=toc(t);;
    print("[1] Found ",  Size(r.tmpid), " group(s).\n");
    print("[1] Time of calculations: ", t, "s.\n");

    print("[2] Searching for mns groups of order <=", threshold, ".\n");
    t:=tic();;
    r.mnsid := step2(threshold);
    t:=toc(t);;
    print("[2] Found ", Size(r.mnsid), " groups.\n");
    print("[2] Time of calculations: ", t, "s.\n");
    if verbose then
        print("[2] The groups' perfect ids: ", r.mnsid, "\n");
    fi;

    print("[3] Searching for mns groups of order <=", threshold, " with faithful rational character of degree <=",maxdim,".\n");
    t:=tic();;
    r.imfid := step3(r.mnsid, maxdim);
    t:=toc(t);;
    print("[3] Found ", Size(r.imfid), " groups.\n");
    print("[3] Time of calculations: ", t, "s.\n");
    if verbose then
        print("[3] The groups' perfect ids: ", r.imfid, "\n");
    fi;
    Append(r.imfid, r.tmpid);
    Unbind(r.tmpid);

    print("[4] Calculating rational character tables of the groups.\n");
    t:=tic();;
    r.qtbls := step4(r.imfid, display=Display);;
    t:=toc(t);;
    print("[4] Time of calculations: ", t, "s\n");

    LogOutputTo();

    return r;
end;
