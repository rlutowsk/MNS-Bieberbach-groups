###############################################################################
##
#P IsMinimalSimpleGroup( <group> )
#P IsMinimalNonsolvableGroup( <group> )
##
## the group is minimal non-solvable iff it is non-solvable and its maximal
## subgroups are solvable
##
## the maximal subgroups are calculated up to conjugacy
##
DeclareProperty("IsMinimalSimpleGroup", IsGroup);
InstallMethod(IsMinimalSimpleGroup, [IsGroup],
function(grp)
    return IsSimpleGroup(grp) and ForAll(MaximalSubgroupClassReps(grp), IsSolvableGroup);
end
);

DeclareProperty("IsMinimalNonsolvableGroup", IsGroup);
InstallMethod(IsMinimalNonsolvableGroup, [IsGroup],
function(grp)
    if IsSolvableGroup(grp) or not IsPerfectGroup(grp) then
        return false;
    fi;
    if not IsMinimalSimpleGroup(grp/SolvableRadical(grp)) then
        return false;
    fi;
    return ForAll(MaximalSubgroupClassReps(grp), IsSolvableGroup);
end);

###############################################################################
##
#A MximalNonsolvableSubgroups( <group> )
##
## calculation of maximal non-solvable subgroups up to conjugacy
##
DeclareAttribute("MaximalNonsolvableSubgroups", IsGroup);
InstallMethod(MaximalNonsolvableSubgroups, [IsGroup],
function(grp)
    return Filtered(MaximalSubgroupClassReps(grp), x->not IsSolvableGroup(x));
end);

###############################################################################
##
#A PerfectDerivedSubgroup( <grp> )
##
## return last element in the derived series of a <grp>
##
DeclareAttribute("PerfectDerivedSubgroup", IsGroup);
InstallMethod(PerfectDerivedSubgroup, [IsGroup],
function(grp)
    return DerivedSeriesOfGroup(grp)[DerivedLength(grp)+1];
end
);

###############################################################################
##
#F MaximalNonsolvableSubgroupsMinSize( <group> )
##
## calculation of maximal non-solvable subgroups up to conjugacy
## with lower bound on their order
##
MaximalNonsolvableSubgroupsMinSize := function(grp, min)
    return Filtered(MaximalSubgroupClassReps(grp), x->not IsSolvableGroup(x) and (Size(x) >= min));
end;

###############################################################################
##
## some helper function for faster decision whether groups are isomorphic
## or conjugate in a parent group
##
SameSize := function(g1,g2)
  return Size(g1) = Size(g2);
end;

SameCenter := function(g1,g2)
    local c1, c2;
    c1 := Center(g1);
    c2 := Center(g2);
    if Exponent(c1) <> Exponent(c2) then
        return false;
    fi;
    return IsomorphismGroups( Center(g1) , Center(g2) ) <> fail;
end;

# this is taken for the GAP code
SameConjugacyClass := function(g,x,y)
  # shortcut for normal subgroups
  if (HasIsNormalInParent(x) and IsNormalInParent(x)
      and CanComputeIsSubset(Parent(x),g) and IsSubset(Parent(x),g))
  or (HasIsNormalInParent(y) and IsNormalInParent(y)
      and CanComputeIsSubset(Parent(y),g) and IsSubset(Parent(y),g)) then
    return x=y;
  fi;

  return RepresentativeAction(g,x,y,OnPoints)<>fail;
end;

###############################################################################
##
## for caching purposes
##
AlreadyTested := function(checked, grp, sg)
    return ForAny(checked, x->
        SameSize(x,sg) and
        SameCenter(x,sg) and
        SameConjugacyClass(grp,x,sg)
    );
end;

###############################################################################
##
#F ConjugacyClassRepsMNS( <group> )
##
## returns representatives of conjugacy classes os mns-subgroups of <group>
##
ConjugacyClassRepsMNS := function(grp)
    local mns, list, checked, g, sg;

    if IsSolvableGroup(grp) then
        return [];
    fi;

    mns  := [];
    list := [grp];
    checked := [ ];
    while list <> [] do
        g := Remove(list);
        if AlreadyTested(checked, grp, g) then
            continue;
        fi;
        Add( checked, g );
        sg := MaximalNonsolvableSubgroups(g);
        Append( list, sg );
        if sg = [] then
            Add( mns, g );
        fi;
    od;
    return mns;
end;

tmp1 := function(list, group)
    return First(list, x->x.size=Size(group));
end;

tmp2 := function(grp, g1, g2)
    return IsConjugate(grp, g1, g2);
end;

ConjugacyClassRepsMNSAlt := function(n)
    local mns, list, checked, g, sg, grp, s, sym;

    if not IsInt(n) then
        Error("Argument must be an integer");
    fi;
    if n<5 then
        return [];
    fi;
    grp := AlternatingGroup(n);
    sym := SymmetricGroup(n);

    mns  := [];
    list := [grp];
    checked := [ ];
    while list <> [] do
    #for g in list do
        g := Remove(list);
        #Print(0, " / ", Size(list), " / ", Size(checked), "\n");
        #s := tmp1(checked, g); #First(checked, x->x.size=Size(g));
        #if s = fail then
        #    s := rec( size:=Size(g), grps := []);
        #    Add(checked, s);
        #fi;
        #if ForAny(checked, x->ContainedConjugates(grp, g, x, true)<>fail) then
        #    continue;
        #fi;
        #Add( checked, g );
        sg := MaximalNonsolvableSubgroups(g);
        if sg = [] then
            if ForAll(mns, x->ContainedConjugates(grp, g, x, true)=fail) then
                Add( mns, g );
            fi;
        else
            sg := Filtered(sg, x->NrMovedPoints(x)=n);
            sg := List(sg, PerfectDerivedSubgroup);
            Append(list, Filtered(sg, x->NrMovedPoints(x)=n));
        fi;
    od;
    return mns;
end;


###############################################################################
##
#F ConjugacyClassRepsMNSMinSize( <group>, <minimal order> )
##
## returns representatives of conjugacy classes os mns-subgroups of <group>
## of order greater than or equal to <minimal order>
##
ConjugacyClassRepsMNSMinSize := function(grp, min)
    local mns, list, checked, g, sg;

    if IsSolvableGroup(grp) or Size(grp) < min then
        return [];
    fi;

    mns  := [];
    list := [grp];
    checked := [ ];
    while list <> [] do
        g := Remove(list);
        if AlreadyTested(checked, grp, g) then
            continue;
        fi;
        Add( checked, g );
        sg := MaximalNonsolvableSubgroupsMinSize(g, min);
        Append( list, sg );
        if sg = [] and IsMinimalNonsolvableGroup(g) then
            Add( mns, g );
        fi;
    od;
    return mns;
end;

###############################################################################
##
#F ConjugacyClassRepsMNSBySolvableRadical( <group>, <minimal order> )
##
## returns representatives of conjugacy classes os mns-subgroups of <group>
## of order greater than or equal to <minimal order>
##
## First, it delegates the task to the quotient of <group> by its solvable
## radical.
## Second, checks for preimages of the groups found above and looks for MNS
## subgroups there.
##
ConjugacyClassRepsMNSBySolvableRadical := function(grp, min)
    local sol, hom, mns;

    sol := SolvableRadical(grp);
    if Size(sol) = 1 then
        return ConjugacyClassRepsMNSMinSize(grp, min);
    fi;
    hom := NaturalHomomorphismByNormalSubgroup(grp, sol);
    mns := ConjugacyClassRepsMNSMinSize(Image(hom), min/Size(sol));
    mns := List(mns, x->PreImage(hom, x));
    return Concatenation( List(mns, x->ConjugacyClassRepsMNSMinSize(x, min) ) );
end;

###############################################################################
##
#F ConjugacyClassRepsMNSRecursive( <group>, <minimal order> )
##
## returns representatives of conjugacy classes os mns-subgroups of <group>
## of order greater than or equal to <minimal order>
##
## Uses recursion on the group by its solvable radical.
## If the radical is trivial, uses its maximal subgroups.
##
## The following function is called.
BySolvableRadicalOp := function(group, min, super, checked)
    local sol, hom, mns, g, m, max, lst, iso, grp;

    grp := PerfectDerivedSubgroup(group);

    if IsSolvable(grp) or Size(grp)<min or AlreadyTested(checked, super, grp) then
        return [];
    fi;
    Add(checked, grp);

    lst := [];
    sol := SolvableRadical(grp);
    if Size(sol)=1 then
        max := MaximalNonsolvableSubgroups(grp);
        if max=[] then
            Add(lst, grp);
        else
            for m in max do
                Append(lst, BySolvableRadicalOp(m, min, super, checked));
            od;
        fi;
    else
        hom := NaturalHomomorphismByNormalSubgroup(grp, sol);
        mns := BySolvableRadicalOp( Image(hom), min/Size(sol), Image(hom), [] );
        mns := List(mns, x->PreImage(hom, x));
        for g in mns do
            max := MaximalNonsolvableSubgroups(g);
            if max=[] then
                Add(lst, g);
            else
                for m in max do
                    Append(lst, BySolvableRadicalOp(m, min, super, checked));
                od;
            fi;
        od;
    fi;
    return lst;
end;

BySolvableRadicalOp1 := function(group, min, super, checked)
    local sol, hom, mns, g, m, max, lst, iso, grp, img, list, lcheck, lg, g1;

    g1 := PerfectDerivedSubgroup(group);
    NormalSubgroups(g1);

    for grp in DirectFactorsOfGroup(g1) do

    if IsSolvable(grp) or Size(grp)<min or AlreadyTested(checked, super, grp) then
        return [];
    fi;
    Add(checked, grp);

    lst := [];
    sol := SolvableRadical(grp);
    if Size(sol)=1 then
        max := MaximalNonsolvableSubgroups(grp);
        if max=[] then
            Add(lst, grp);
        else
            for m in max do
                Append(lst, BySolvableRadicalOp1(m, min, super, checked));
            od;
        fi;
    else
        hom := NaturalHomomorphismByNormalSubgroup(grp, sol);
        mns := BySolvableRadicalOp1( Image(hom), min/Size(sol), Image(hom), [] );
        for img in mns do
            lg   := PreImage(hom, img);
            list := [PerfectDerivedSubgroup(PreImage(hom, img))];
            lcheck := [];
            while list<>[] do
                g := Remove(list,1);
                if ForAny(lcheck, x->IsConjugate(lg, g, x)) then
                    continue;
                fi;
                Add(lcheck, g);
                max := MaximalNonsolvableSubgroups(g);
                if max=[] then
                    if not ForAny(lst, x->IsConjugate(super, g, x)) then
                        Add(lst, g);
                    fi;
                else
                    Append(list, Filtered(List(max, PerfectDerivedSubgroup), x->Size(x)>=min));
                fi;
            od;
        od;
    fi;

    od;
    return lst;
end;

BySolvableRadicalOp2 := function(group, min, super, checked)
    local sol, hom, mns, g, m, max, lst, iso, grp, img, list, lcheck, lg, g1;

    g1 := PerfectResiduum(group);
    NormalSubgroups(g1);

    for grp in DirectFactorsOfGroup(g1) do

    if IsSolvable(grp) or Size(grp)<min or AlreadyTested(checked, super, grp) then
        return [];
    fi;
    Add(checked, grp);

    lst := [];
    sol := SolvableRadical(grp);
    if Size(sol)=1 then
        max := MaximalNonsolvableSubgroups(grp);
        if max=[] then
            Add(lst, grp);
        else
            for m in max do
                Append(lst, BySolvableRadicalOp2(m, min, super, checked));
            od;
        fi;
    else
        hom := NaturalHomomorphismByNormalSubgroup(grp, sol);
        mns := BySolvableRadicalOp2( Image(hom), min/Size(sol), Image(hom), [] );
        for img in mns do
            lg   := PreImage(hom, img);
            list := [PerfectResiduum(PreImage(hom, img))];
            lcheck := [];
            while list<>[] do
                g := Remove(list,1);
                if ForAny(lcheck, x->IsConjugate(lg, g, x)) then
                    continue;
                fi;
                Add(lcheck, g);
                max := MaximalNonsolvableSubgroups(g);
                if max=[] then
                    if not ForAny(lst, x->IsConjugate(super, g, x)) then
                        Add(lst, g);
                    fi;
                else
                    Append(list, Filtered(List(max, PerfectResiduum), x->Size(x)>=min));
                fi;
            od;
        od;
    fi;

    od;
    return lst;
end;

ConjugacyClassRepsMNSRecursive := function(grp, min)
    return BySolvableRadicalOp1(grp, min, grp, []);
end;

###############################################################################
##
#F ConjugacyClassRepsMNSMinSizeNC( <group>, <minimal order> )
##
## variation of ConjugacyClassRepsMNSMinSize
## may return duplicates in representatives of conjugacy classes
##
ConjugacyClassRepsMNSMinSizeNC := function(grp, min)
    local mns, list, checked, g, sg;

    if IsSolvableGroup(grp) then
        return [];
    fi;

    mns  := [];
    list := [grp];
    checked := [ ];
    while list <> [] do
        g := Remove(list);
        Add( checked, g );
        sg := MaximalNonsolvableSubgroupsMinSize(g, min);
        Append( list, sg );
        if sg = [] and IsMinimalNonsolvableGroup(g) then
            Add( mns, g );
        fi;
    od;
    return mns;
end;
