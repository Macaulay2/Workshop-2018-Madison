FIRing = new Type of HashTable
globalAssignment FIRing

FIMonomial = new Type of HashTable
FIRingElement = new Type of HashTable
FIMatrix = new Type of MutableHashTable



-- FI RINGS
--=====================================

FI = method()

FI (Ring, Symbol) := (R, f) -> (
    FI := new FIRing from (hashTable{
	    (symbol CoefficientRing) => R,
	    (symbol FunctionSymbol) => f
	    });
    return FI
    ) 

net FIRing := R -> (
    net "FI(" | net R.CoefficientRing | net ", " | net R.FunctionSymbol | ")"
    )


-- FI MONOMIALS
--=====================================

listToFIMon = method()

listToFIMon(FIRing, List, ZZ) := FIMonomial => (R, l, n) -> (
    if any(l, i -> not instance(i, ZZ) or i <= 0) then (error "listToFIMon: Expected a list of positive integers.");
    if not instance(n, ZZ) or n < 0 then (error "listToFIMon: Expected a non-negative integer.");
    if max l > n or #(unique l) < #l then( error "listToFIMon: Expected a list representing an injective function."); 
    m := new FIMonomial from (hashTable{
	    (symbol ring) => R,
	    (symbol BaseName) => R.FunctionSymbol,
	    (symbol FunctionName) => l,
	    (symbol TargetName) => n
	    });
    return m
    )

FIRing_List := FIMonomial => (R, l) -> listToFIMon(R, first l, last l)


net FIMonomial := m -> (
    net m.BaseName | net "_{" | net m.FunctionName | net "," | net m.TargetName | net "}"
    )

monomialCompose := (i1,i2) -> (
    j := length i2_0;
    inj := apply(toList(1..j), i -> (i1_0)_((i2_0)_(i-1)-1));
    dest := i1_1;
    return {inj,dest}
    )

/// TEST

restart
load "FIModules.m2"
R = FI(QQ, f)
listToFIMon(R, {1,4,5},5) 


///