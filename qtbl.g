###############################################################################
##
#F IdCtbl( ctbl )
##
## we assume that Identifier(tbl) is a string that represents id of prfect 
## group in the library
##
IdCtbl := x->EvalString(Identifier(x));


LoadPackage("wedderga");
###############################################################################
##
#F SchurIndexByCharacterDescent( <field>, <group>, <position> )
##
## let chi := Irr(group)[position]
## calculates Schur index of chi/Kernel(chi)
##
SchurIndexByCharacterDescent := function( f, grp, c )
    local ker, nh, q, chi, qtbl, r, cc, qchi, tbl;

    if not HasOrdinaryCharacterTable( grp ) then
        Error("calculate character table of grp first");
    fi;
    tbl := CharacterTable( grp );

    if IsPosInt(c) then
    	  chi := Irr(grp)[c];	
    elif IsCharacter( tbl, c ) then
    	  chi := c;
    else
    	  Error("c must be a character or its position in Irr(grp)");
    fi;

    ker := KernelOfCharacter( chi );
    if Size(ker) = 1 then
    	  return SchurIndexByCharacter( f, grp, c );
    fi;
    nh  := NaturalHomomorphismByNormalSubgroup( grp, ker );
    q   := Image( nh );
    qtbl:= CharacterTable( q );
    qchi:= [];
    for cc in ConjugacyClasses(qtbl) do
    	  r := PreImagesRepresentative( nh, Representative(cc) );
    	  Add(qchi, chi[First([1..NrConjugacyClasses(tbl)], i->r in ConjugacyClasses(tbl)[i])]);
    od;
    return SchurIndexByCharacter( f, q,  Character( qtbl, MakeImmutable( qchi ) ) );
end;

###############################################################################
##
#F IsConjugateCharacters( chi1, chi2 )
##
## assume grp := UnderlyingGroup( chi1 ) ( = UnderlyingGroup( chi2 ) ) 
## decide whether:
## - there exists s in Gal(Q(chi1)/Q) such that chi1^s = chi2 or
## - there exists a in Aut(grp) such that chi1 a = chi2
##
IsConjugateCharacters := function( c1, c2)
    local f, g, grp, aut, inn, hom, ccl;
    if c1[1]<>c2[1] then
        return false;
    fi;

    f := Field(c1);
    if f<>Field(c2) then
        return false;
    fi;

    g := GaloisGroup( f );
    if ForAny( g, a->c1^a = c2 ) then
      return true;
    fi;

    grp := UnderlyingGroup( c1 );
    ccl := ConjugacyClasses( UnderlyingCharacterTable( c1 ) );
    aut := AutomorphismGroup( grp );
    inn := InnerAutomorphismsAutomorphismGroup( aut );
    hom := NaturalHomomorphismByNormalSubgroup( aut, inn );
    for g in Image(hom) do                   # g - elm of aut/inn
        f := PreImagesRepresentative(hom,g); # f - representative of g
        if ForAll([2..Size(ccl)], i->c1[i] = c2[Position(ccl, ConjugacyClass(grp, Image(f,Representative(ccl[i]))))]) then
            return true;
        fi;
    od;
    return false;
end;

###############################################################################
##
#A QSchurIndexOrbits(<ctbl>)
##
## return positions of characters with the same Schur index over rationals
##
DeclareAttribute( "QSchurIndexOrbits", IsCharacterTable );
InstallMethod( QSchurIndexOrbits, [IsCharacterTable],
function(tbl)
    local orbits, list, c, orb, i;

    orbits := [ [1] ];
    list   := [2..NrConjugacyClasses(tbl)];
    while list <> [] do
        c   := Remove( list, 1 );
        orb :=[c];
        for i in list do
            if IsConjugateCharacters( Irr(tbl)[c], Irr(tbl)[i] ) then
                Add(orb, i);
            fi;
        od;
        list := Difference( list, orb );
        Add( orbits, orb );
    od;
    return orbits;
end );

###############################################################################
##
#A QSchurIndices(<ctbl>)
##
## Schur indices over rationals of characters in ctbl
##
DeclareAttribute( "QSchurIndices", IsCharacterTable and HasUnderlyingGroup );
InstallMethod(QSchurIndices, [IsCharacterTable and HasUnderlyingGroup],
function(tbl)
    local orbits, orb, m, c, indices;

    indices := [];
    for orb in QSchurIndexOrbits(tbl) do
        c := orb[1];
        m := SchurIndexByCharacterDescent( Field(Irr(tbl)[c]), UnderlyingGroup(tbl), c);
        indices{orb} := List(orb, x->m);
    od;
    return indices;
end );

###############################################################################
##
#A QIrr(<ctbl>)
##
## characters of rational representations group of ctbl
##
DeclareAttribute( "QIrr", IsCharacterTable );
InstallMethod( QIrr, "characters of rationals representations", [IsCharacterTable],
function( tbl )
    local irr, qirr, c, gc, m, grp, ind, sum, sci;

    sci  := QSchurIndices(tbl);
    irr  := Irr(tbl);
    grp  := UnderlyingGroup( tbl );
    if Irr( grp ) <> Irr( tbl ) then
        Error("Irr for grp and tbl must be the same");
    fi;
    
    if ForAll(irr[1], x->x=1) then
        qirr := [ irr[1] ];
        ind  := [2..Size(irr)];
    else
        qirr := [];
        ind  := [1..Size(irr)];
    fi;
    while ind<>[] do
        c   := Remove( ind, 1 );
        gc  := List( GaloisGroup(Field(irr[c])), a->(irr[c])^a );
        sum := Sum(gc);
        if not ForAll(sum, IsInt) then
            Error("sum is not rational");
        fi;
        ind := Difference(ind,List(gc, x->Position(irr,x))); 
        m   := sci[c]; 
        Add(qirr, m*Sum(gc));
    od;
    Sort( qirr );
    return qirr;
end );

###############################################################################
##
#A QCharacterTable(<ctbl>)
##
## calculates the rational character table of the group of ctbl
## NOTE: this in not really a character table in terms of GAP
##       but can be used for nice displaying
##
DeclareAttribute("QCharacterTable", IsOrdinaryTable);
InstallMethod(QCharacterTable, [IsOrdinaryTable],
function(tbl)
    local r, l, i, g, rcc, rep;

    r   := rec();
    l   := [];
    rcc := [];

    g := UnderlyingGroup( tbl );
    r.UnderlyingGroup := g;

    for i in [1..NrConjugacyClasses(tbl)] do
        rep := Representative(ConjugacyClasses(tbl)[i]); 
        if ForAny( rcc, c->rep in c ) then
            continue;
        fi;
        Add(l,i);
        Add(rcc, RationalClass(g, rep));
    od;

    r.ConjugacyClasses := rcc;
    r.NrConjugacyClasses := Size(l);
    r.IsFinite := IsFinite( g );
    r.OrdersClassRepresentatives := OrdersClassRepresentatives( tbl ){l};
    r.ClassNames := ClassNames( tbl ){l};
    r.Identifier := Concatenation("Rational character table of ", Identifier(tbl));
    r.Irr        := QIrr( tbl ){[1..Size(QIrr(tbl))]}{l}; # for start
    r.UnderlyingCharacteristic := 0;
    r.SizesCentralizers := SizesCentralizers( tbl ){l};

    ConvertToCharacterTableNC(r);
    return r;
end );

###############################################################################
##
#A IsFaithful(<char>)
##
## quite fast decision whether character is faithful
##
DeclareAttribute( "IsFaithful", IsCharacter );
InstallMethod( IsFaithful, [IsCharacter], function( char )
    return Size( Filtered(char, x->x=char[1]) ) = 1;
end );

###############################################################################
##
#F QSchurIndexLowerBound( <ctbl>, <n> )
##
## if the Frobenius-Schur index of Irr(ctbl)[n] is -1, then the Schur index 
## is at least 2
##
QSchurIndexLowerBound := function( tbl, n )
    local f, c;

    if Indicator(tbl,2)[n] = -1 then
        return 2;
    fi;
    return 1;
end;

###############################################################################
##
#F QSchurIndexUpperBoundBySubgroups( <ctbl>, <n>, <subgroups> )
##
## search for upper bound of Schur index by looking on subgroups
##
## based on Isaacs, Character Theory if finite groups, 1976:
## - Corollary 10.2h
## - Lemma 10.4
##
QSchurIndexUpperBoundBySubgroups := function( tbl, n, subgroups )
    local f, fs, fus, c, m, min, max, mtbl, mirr, mfs, mc, mind, res, sp, msi, tmp, i, ind, data;

    min := QSchurIndexLowerBound(tbl,n);
    c   := Irr(tbl)[n];
    f   := Field(c);
    fs  := Size( GaloisGroup(f) );
    max := c[1];
    
    if max = 1 then
        return 1;
    fi;

    for m in subgroups do
        mtbl := CharacterTable( m );
        mirr := Irr( mtbl );
        res  := RestrictedClassFunction( c, mtbl );
        sp   := List(mirr, chi->ScalarProduct(res, chi));
        ind  := Filtered([1..Size(sp)], i->sp[i]>0);
        data := List(ind, i->rec( pos:=i, chi:=mirr[i], mult:=sp[i]*Size(GaloisGroup(Field(Concatenation(c,mirr[i]))))/fs));
        SortBy( data, x->[x.mult, x.pos] );
        for mc in data do
            if IsInt(mc.mult/max) then
                continue;
            fi;
            msi := SchurIndexByCharacterDescent( Field(mc.chi), m, mc.pos );
            tmp := Gcd(max, msi * mc.mult);
            if tmp < max then
                max := tmp;
            fi;
            if max < min then
                Error("Lower bound greater than the Upper, shouldn't happen...");
            fi;
            if max = min then
                return min;
            fi;
        od;
    od;
    return max;
end;

QSchurIndexUpperBound := function( tbl, n )
    return QSchurIndexUpperBoundBySubgroups( tbl, n, MaximalSubgroupClassReps(UnderlyingGroup(tbl)) );
end;

#################################################################################################################################
##
#M PerfectIdentificationCtbl( ctbl )
##
## for each character chi from Irr(ctbl) calculates perfect id of image of representation with character chi
##
PerfectIdentificationCtblSubset := [];
DeclareAttribute("PerfectIdentificationCtbl", IsOrdinaryTable and HasUnderlyingGroup);
InstallMethod(PerfectIdentificationCtbl, "identify images of character representations", [IsOrdinaryTable and HasUnderlyingGroup],
function(tbl)
    local chi, grp, orb, id, ids, qgp, pid, pos, sio, orbits, i, ker, kernels;

    kernels := [];
    orbits  := [];
    for i in [1..Size(QSchurIndexOrbits(tbl))] do
        orb := QSchurIndexOrbits( tbl )[i];
        chi := Irr( tbl )[ orb[1] ];
        ker := KernelOfCharacter( chi );
        pos := Position( kernels, ker );
        if pos = fail then
            Add( kernels, ker );
            Add( orbits, ShallowCopy(orb) );
        else
            Append( orbits[pos], orb );
        fi;
    od;
    grp := UnderlyingGroup( tbl );
    pid := [];
    for orb in orbits do
        ker := kernels[ Position(orbits, orb) ];
        #Print(Size(ker), " / ", orb, "\n");
        qgp := grp / ker;
        if Size(qgp) = 1 then
            id  := [1,1];
        elif Size(ker) = 1 then
            id  := IdCtbl(tbl); #PerfectIdentification( grp );
            # do check
            if GeneratorsOfGroup(grp) = GeneratorsOfGroup( PerfectGroup(id) ) then
                continue;
            fi;
            if IsomorphismGroups(grp, PerfectGroup(id)) = fail then
                Error("Error in database");
            fi;
        elif PerfectIdentificationCtblSubset = [] then
        #else
            id  := PerfectIdentification( qgp );
        else
            ids := Filtered( PerfectIdentificationCtblSubset, x->x[1]=Size(qgp) );
            id  := First( ids, x->IsomorphismGroups(qgp, PerfectGroup(x))<>fail );
        fi;
        pid{orb} := List(orb, i->id);
    od;
    return pid;
    #return List( Irr(tbl), chi->PerfectIdentification(UnderlyingGroup(tbl)/KernelOfCharacter(chi)) );
end );

###############################################################################
##
#F CharacterTableToRec( <ctbl> )
##
## saving data from character table to record, which can be saved to text file
##
CharacterTableToRec := function( arg )
    local r, nc, tbl, id;

    tbl := arg[1];
    if not IsCharacterTable( tbl ) then
        Error("tbl must be a character table");
    fi;
    if Size(arg)>1 then
        id := arg[2];
    else
        id := Identifier(tbl);
    fi;
    if not IsString( id ) then
        Error("id must be a string");
    fi;

    r := rec();
    r.UnderlyingGroupGens  := GeneratorsOfGroup( UnderlyingGroup( tbl ) );
    r.ConjugacyClassesReps := List( ConjugacyClasses( tbl ), Representative );
    nc := NrConjugacyClasses( tbl );

    r.IdentificationOfConjugacyClasses := ShallowCopy( IdentificationOfConjugacyClasses( tbl ) );

    r.IdentificationOfClasses := r.IdentificationOfConjugacyClasses;

    r.Irr := List( Irr( tbl ){[1..nc]}{[1..nc]}, ShallowCopy );

    r.IsFinite := ShallowCopy( IsFinite( UnderlyingGroup( tbl ) ) );

    r.NrConjugacyClasses := nc;

    r.OrdersClassRepresentatives := ShallowCopy( OrdersClassRepresentatives( tbl ) );

    r.SizesCentralizers := ShallowCopy( SizesCentralizers( tbl ) );

    r.SizesConjugacyClasses := ShallowCopy( SizesConjugacyClasses( tbl ) );

    r.UnderlyingCharacteristic := UnderlyingCharacteristic( tbl );

    r.ClassNames := ShallowCopy( ClassNames( tbl ) );

    r.Identifier := id;

    r.InfoText := InfoText( tbl );

    r.ComputedPowerMaps := List( ComputedPowerMaps( tbl ), ShallowCopy );

    if IsBound( tbl!.qirr ) then
        r.qirr := List(tbl!.qirr, AsList);
    fi;

    if HasQIrr( tbl ) then
    	  r.QIrr := List(QIrr(tbl), AsList);
    fi;

    if HasQSchurIndexOrbits( tbl ) then
        r.QSchurIndexOrbits := QSchurIndexOrbits( tbl );
    fi;

    if HasQSchurIndices( tbl ) then
        r.QSchurIndices := QSchurIndices( tbl );
    fi;

    if HasPerfectIdentificationCtbl( tbl ) then
        r.PerfectIdentificationCtbl := PerfectIdentificationCtbl( tbl );
    fi;

    return r;
end;

###############################################################################
##
#F CharacterTableFromRec( <record> )
##
## convert record to character table
##
CharacterTableFromRec := function( r )
    local i;

    r.UnderlyingGroup  := Group( r.UnderlyingGroupGens );
    r.ConjugacyClasses := List( r.ConjugacyClassesReps, x->ConjugacyClass(r.UnderlyingGroup, x) );

    SetConjugacyClasses( r.UnderlyingGroup, r.ConjugacyClasses );

    for i in [1..Length(r.ConjugacyClasses)] do
        SetSize(r.ConjugacyClasses[i],r.SizesConjugacyClasses[i]);
    od;

    ConvertToCharacterTableNC( r );
    SetOrdinaryCharacterTable( UnderlyingGroup( r ), r );

    if IsBound( r!.qirr ) then
        r!.qirr := MakeImmutable( List( r!.qirr, chi->Character(r, MakeImmutable(chi)) ) );
    fi;

    if IsBound( r!.QIrr ) then
        SetQIrr(r, MakeImmutable( List( r!.QIrr, row->Character( r, MakeImmutable(row) ) ) ) );
    fi;

    if IsBound( r!.QSchurIndexOrbits ) then
        SetQSchurIndexOrbits(r, MakeImmutable( r!.QSchurIndexOrbits ) );
    fi;

    if IsBound( r!.QSchurIndices ) then
        SetQSchurIndices( r, MakeImmutable( r!.QSchurIndices ) );
    fi;

    if IsBound( r!.PerfectIdentificationCtbl ) then
        SetPerfectIdentificationCtbl( r, MakeImmutable( r!.PerfectIdentificationCtbl ) );
    fi;

    return r;
end;

###############################################################################
##
#F RepairOrderInCharacterTable( <ctbl> )
##
## set conjugacy classes in orders of their representatives
##
RepairOrderInCharacterTable := function(tbl)
    local r, v, l, n, i, p;

    r := ShallowCopy(CharacterTableToRec( tbl ));
    n := NrConjugacyClasses( tbl );
    v := List([1..n], i->[r.OrdersClassRepresentatives[i], r.ClassNames[i]]);
    l := [1..n];

    SortParallel(v,l);

    # there fields may not be all - be careful
    r.ClassNames := r.ClassNames{l};
    p := PermList(l)^-1;
    for i in [2..Length(r.ComputedPowerMaps)] do
        if IsBound(r.ComputedPowerMaps[i]) then
            r.ComputedPowerMaps[i] := List(r.ComputedPowerMaps[i]{l}, a->a^p);
        fi;
    od;
    r.Irr := r.Irr{[1..n]}{l};
    r.OrdersClassRepresentatives := r.OrdersClassRepresentatives{l};
    r.SizesCentralizers := r.SizesCentralizers{l};
    r.SizesConjugacyClasses := r.SizesConjugacyClasses{l};
    if IsBound(r.QIrr) then
        r.QIrr := List(r.QIrr, x->x{l});
    fi;

    return CharacterTableFromRec(r);
end;

################################################################################
############################### left to clean up ###############################
if not IsBound( QIrrDebug ) then
    QIrrDebug := false;
fi;
################################################################################

DeclareOperation("FaithfulQIrr", [ IsCharacterTable, IsPosInt, IsInt ]);
InstallOtherMethod( FaithfulQIrr, [ IsCharacterTable, IsPosInt, IsInt ],
function( tbl, dim, num )
    local irr, qirr, c, gc, m, grp, ind, sum;

    irr  := Filtered( Irr(tbl), char->char[1]<=dim );
    qirr := [ ];
    grp  := UnderlyingGroup( tbl );
    SetIrr(grp, Irr(tbl));
    #if Irr( grp ) <> Irr( tbl ) then
    #    Error("Irr for grp and tbl must be the same");
    #fi;

    if num<0 then
        num := 0;
    fi;

    ind := [2..Size(irr)];
    while ind<>[] do
        c   := Remove( ind, 1 );
        if not IsFaithful(irr[c]) then
            continue;
        fi;
		if ForAll(irr[c], IsRat) then
			sum := irr[c];
		else
			if 2*irr[c][1] > dim then
				continue;
			fi;
	        gc  := List( GaloisGroup(Field(Rationals, irr[c])), a->(irr[c])^a );
		    ind := Difference(ind,List(gc, x->Position(irr,x)));
			sum := Sum( gc );
		fi;
        if sum[1] > dim then
            continue;
        fi;
        m   := SchurIndexByCharacter( Rationals, grp, c );
        sum := m*sum;
        if sum[1] <= dim then
            Add(qirr, sum);
            if Size(qirr) = num then
                ind:=[];
            fi;
        fi;
    od;
    Sort( qirr );
    return qirr;
end );

DeclareOperation("HasFaithfulQIrr", [IsGroup, IsPosInt]);
InstallOtherMethod( HasFaithfulQIrr, [IsGroup, IsPosInt],
function(grp, dim)
	return FaithfulQIrr( CharacterTable(grp), dim, 1 ) <> [] ;
end );
