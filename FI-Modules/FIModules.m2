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
	    (symbol FunctionName) => l
	    });
    return m
    )

FIRing_List := FIMonomial => (R, l) -> listToFIMon(R, first l, last l)


net FIMonomial := m -> (
    net m.BaseName | net "_" | net m.FunctionName
    )