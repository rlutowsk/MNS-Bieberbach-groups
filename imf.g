Read("mns.g");

# conjugacy classes subgroups representatives
CCSReps := grp->List(ConjugacyClassesSubgroups(grp), Representative);;

# generators on list of groups
GroupsGens := grps->List(grps, GeneratorsOfGroup);;


###############################################################################
##
#F InitImfPermData( <dimension>, <q-class>, <z-class> )
##
## initiates a record r for further use with the following fields:
## - imf: identifier of the irreducible matrix group in the catalogue
## - mgrp: the group itself
## - iso: permutation representation of the group
## - pgrp: image of iso
## - *gens: generators of the m/p group
## - solvable: is the group solvable
##
## some fields to calculate further:
## - ccsr: conjugacy classes of subgroups of the group
## - mnsind: indices on the list ccsr of those groups which are mns
##
InitImfPermData := function(dim, q, z)
    local r;
    r := rec();
    r.imf  := [dim,q,z];
    r.mgrp := ImfMatrixGroup(dim,q,z);
    r.iso  := IsomorphismPermGroup(r.mgrp);
    r.pgrp := Image(r.iso);
    r.mgens:= GeneratorsOfGroup(r.mgrp);
    r.pgens:= List(r.mgens, x->Image(r.iso,x));
    r.solvable:= IsSolvableGroup(r.pgrp);
    return r;
end;;

# strip and recover non-text data for writing to/reading from saved text files
StripImfPermData := function(r)
    if IsBound(r.iso) then
        Unbind(r.iso);
    fi;
    if IsBound(r.mgrp) then
        Unbind(r.mgrp);
    fi;
    if IsBound(r.pgrp) then
        Unbind(r.pgrp);
    fi;
    if IsBound(r.ccsr) then
        Unbind(r.ccsr);
    fi;
end;;
RecoverImfPermData := function(r)
    r.mgrp := Group(r.mgens);
    r.pgrp := Group(r.pgens);
    r.iso  := GroupHomomorphismByImagesNC(r.mgrp,r.pgrp,r.mgens,r.pgens);
    r.ccsr := [];
    if Size(r.ccsrgens) > 0 then
        if r.ccsrgens[1] = [] then
            Remove(r.ccsrgens,1);
        fi;
        r.ccsr := List(r.ccsrgens,Group);
    fi;
end;;

###############################################################################
##
#F MNSIsIrreducible( <record>, <index> )
##
## check whether the subgroup given by <index> of the matrix group defined
## by the <record> is absolutely irreducible
##
MNSIsIrreducible := function(r,i)
    return Sum(PreImage(r.iso,r.ccsr[i]), x->Trace(x)^2)=Size(r.ccsr[i]);
end;;
###############################################################################
##
#F MNSHasTrivial( <record>, <index> )
##
## check whether the subgroup given by <index> of the matrix group defined
## by the <record> has trivial constituent
##
MNSHasTrivial := function(r,i)
    return Sum(PreImage(r.iso,r.ccsr[i]), x->Trace(x))>0;
end;;

###############################################################################
##
#F MNSPrintData( <record>, [ <delimiter> ] )
##
## Display info about the <record>, using <delimiter> bewteen the fields
##
MNSPrintData := function(arg)
    local i,j,data,max,row,r, d;
    r   := arg[1];
    Print(r.imf,"\n");
    if r.mnsind = [] then
        return;
    fi;
    d   := "\t";
    if Length(arg)>1 then
        d := arg[2];
    fi;
    data:= [["Index","Description","Group id","Irreducible/C","Has trivial"]];
    max := List(data[1],Length);
    for i in r.mnsind do
        row := List([i,StructureDescription(r.ccsr[i]),IdGroup(r.ccsr[i]),MNSIsIrreducible(r,i),MNSHasTrivial(r,i)],String);
        Add(data,row);
        for j in [1..5] do
            if Length(row[j]) > max[j] then
                max[j] := Length(row[j]);
            fi;
        od;
    od;
    for row in data do
        for j in [1..5] do
            Print(String(row[j],-max[j]), d);
        od;
        Print("\n");
    od;
    Print("\n");
end;;

###############################################################################
##
#F MNSMakeImf( <cache>, <dimension>, <q-class>, <z-class>, [verbose] )
##
## Calculate and display info about mns subgroups of the matrix group given by
## ImfMatrixGroup( <dimension>, <q-class>, <z-class> )
##
## Use the list <cache> to store the results
##
DeclareOperation("MNSMakeImf", [IsList, IsPosInt, IsPosInt, IsPosInt, IsBool]);
InstallMethod( MNSMakeImf,[IsList, IsPosInt, IsPosInt, IsPosInt, IsBool],
function(list, dim, q, z, verbose)
    local r;
    r := First(list, x->x.imf = [dim,q,z]);
    if r = fail then
        r := InitImfPermData(dim, q, z);
        r.ccsr := ConjugacyClassRepsMNS(r.pgrp);
        r.mnsind := [1..Size(r.ccsr)];
        Add(list,r);
    fi;
    if verbose then
        MNSPrintData(r);
    fi;
end );

InstallOtherMethod( MNSMakeImf, [IsList, IsPosInt, IsPosInt, IsPosInt],
function(list, dim, q, z)
    MNSMakeImf(list, dim, q, z, false);
end);

###############################################################################
##
#F MNSMakeDim( <cache>, <dimension>[, <verbose>] )
##
## Calculate and display info about mns subgroups of the irreducible integer 
## matrix groups in dimension <dimension>
##
## Use the list <cache> to store the results
##
DeclareOperation("MNSMakeDim", [IsList, IsPosInt, IsBool]);
InstallMethod(MNSMakeDim, [IsList, IsPosInt, IsBool],
function(list, dim, verbose)
    local q;
    for q in [1..ImfNumberQQClasses(dim)] do
        MNSMakeImf(list, dim, q, 1, verbose);
    od;
end);
InstallOtherMethod(MNSMakeDim, [IsList, IsPosInt],
function(list, dim)
    MNSMakeDim(list, dim, false);
end);

###############################################################################
##
#F SetMNSFindMinOp( <num|function> )
##
## sets function used in MNSMakeImfMinOp
##
SetMNSFindMinOp := function(arg)
    local funcs, i;
    funcs := [
        ConjugacyClassRepsMNSMinSize,
        ConjugacyClassRepsMNSBySolvableRadical,
        ConjugacyClassRepsMNSRecursive
    ];
    if Size(arg) = 0 then
        Print("Usage: SetMNSFindOp(opt)\n\n");
        Print("Available options:\n");
        for i in [1..Size(funcs)] do
            Print(i, ": ", NameFunction(funcs[i]), "\n");
        od;
        Print("\nOne can also use one of the above functions as an argument.\n");
        return;
    fi;
    i := arg[1];
    if not i in [1..Size(funcs)] and not i in funcs then
        Error("The argument must be an integer or a function name ", [1..Size(funcs)], "or a function");
    fi;
    if IsBound(MNSFindMinOp) then
        MakeReadWriteGlobal("MNSFindMinOp");
        UnbindGlobal("MNSFindMinOp");
    fi;
    if IsInt(i) then
        BindGlobal("MNSFindMinOp", funcs[i]);
    else
        BindGlobal("MNSFindMinOp", i);
    fi;
end;

###############################################################################
##
## set default value for MNSFindMinOp
SetMNSFindMinOp(ConjugacyClassRepsMNSBySolvableRadical);

###############################################################################
##
#F MNSMakeImfMin( <cache>, <dimension>, <q-class>, <z-class>, <minimum order>, [<verbose>] )
##
## Calculate and display info about mns subgroups of the matrix group given by
## ImfMatrixGroup( <dimension>, <q-class>, <z-class> )
## which order is greater than or equal to <minimum order>
##
## Use the list <cache> to store the results
##
DeclareOperation("MNSMakeImfMin", [IsList, IsPosInt, IsPosInt, IsPosInt, IsPosInt, IsBool]);
InstallMethod( MNSMakeImfMin,[IsList, IsPosInt, IsPosInt, IsPosInt, IsPosInt, IsBool],
function(list, dim, q, z, min, verbose)
    local r;
    r := First(list, x->x.imf = [dim,q,z]);
    if r = fail then
        r := InitImfPermData(dim, q, z);
        r.ccsr := MNSFindMinOp(r.pgrp, min);
        r.mnsind := [1..Size(r.ccsr)];
        Add(list,r);
    fi;
    if verbose then
        MNSPrintData(r);
    fi;
end );

InstallOtherMethod( MNSMakeImfMin, [IsList, IsPosInt, IsPosInt, IsPosInt, IsPosInt],
function(list, dim, q, z, min)
    MNSMakeImfMin(list, dim, q, z, min, false);
end);

###############################################################################
##
#F MNSMakeDimMin( <cache>, <dimension>, <minimum order>[, <verbose>] )
##
## Calculate and display info about mns subgroups of the irreducible integer 
## matrix groups in dimension <dimension> which order is greater than or equal 
## to <minimum order>
##
## Use the list <cache> to store the results
##
DeclareOperation("MNSMakeDimMin", [IsList, IsPosInt, IsPosInt, IsBool]);
InstallMethod(MNSMakeDimMin, [IsList, IsPosInt, IsPosInt, IsBool],
function(list, dim, min, verbose)
    local q;
    for q in [1..ImfNumberQQClasses(dim)] do
        MNSMakeImfMin(list, dim, q, 1, min, verbose);
    od;
end);
InstallOtherMethod(MNSMakeDimMin, [IsList, IsPosInt, IsPosInt],
function(list, dim, min)
    MNSMakeDimMin(list, dim, min, false);
end);