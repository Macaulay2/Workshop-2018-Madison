FIMorphism = new Type of BasicList
FIRingElement = new Type of HashTable
FIRing = new Type of Type
globalAssignment FIRing

-- FI MORPHISMS
--================================

FI = method()

FI List := l -> (
    if #l == 2 then new FIMorphism from l
    else new FIMorphism from {drop(l, -1), last l}
    )

FIMorphism * FIMorphism := (g, f) -> (
    if f#1 < g#1 then error "Morphisms are not composable."
    else new FIMorphism from {apply(#(g#0), i -> f#0#(g#0#i-1)), f#1}
    )

target FIMorphism := f -> last f

source FIMorphism := f -> length f -1 

net FIMorphism := l -> net "f_" | net toList l


-- FI RINGS
--================================


coefficient (FIRingElement, FIMorphism) := (m,f) -> (
    if (terms m)#?f then return (terms m)#f
    else return 0
    )

terms FIRingElement := g -> g.terms

fiRing = method()

fiRing (Ring) := R -> (
    F := new FIRing of FIRingElement from hashTable{
	baseRings => (R.baseRings)|{R}
	};
    F + F := (m,n) -> (
	new F from hashTable{
	    (symbol ring) => F;
	    (symbol terms) => hashTable	apply(unique( keys terms m| keys terms n), key ->(
			 coefsum = coefficient(m,key) + coefficient(n,key);
			 if coefsum =!= 0 then key => coefsum
			 ))	
	    }
	);
    return F
    ) 


coefficientRing FIRing := R -> last R.baseRings

fiRingElement = method()

fiRingElement (FIMorphism,FIRing) := (l,R) ->(
    L := new R from hashTable{
	(symbol ring) => R,
	(symbol terms) => hashTable{
	    l => 1
	    }
	};
    return L
    )







/// TEST 

restart
load "Categories.m2"
f = FI{1,2,5}
g = FI{3,1,2,4,6,7}
R = fiRing(QQ)
coefficientRing R
S = fiRing(ZZ[x])
coefficientRing S
m = fiRingElement(f,R)
n = fiRingElement(g,R)
m+n
///
