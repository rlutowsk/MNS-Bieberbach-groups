###############################################################################
##
#F IsMinimalNonSolvableGroup( <group> )
##
## the group is minimal non-solvable iff it is non-solvable and its maximal 
## subgroups are solvable
## 
## the maximal subgroups are calculated up to conjugacy
##
IsMinimalNonSolvableGroup := function(grp)
  return not IsSolvableGroup(grp) and ForAll(MaximalSubgroupClassReps(grp), IsSolvableGroup);
end;

###############################################################################
##
#F MaximalNonsolvableSubgroups( <group> )
##
## calculation of maximal non-solvable subgroups up to conjugacy
##
MaximalNonsolvableSubgroups := function(grp)
    return Filtered(MaximalSubgroupClassReps(grp), x->not IsSolvableGroup(x));
end;

###############################################################################
##
#F MaximalNonsolvableSubgroups( <group> )
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
        if sg = [] and IsMinimalNonSolvableGroup(g) then
            Add( mns, g );
        fi;
    od;
    return mns;
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
        if sg = [] and IsMinimalNonSolvableGroup(g) then
            Add( mns, g );
        fi;
    od;
    return mns;
end;