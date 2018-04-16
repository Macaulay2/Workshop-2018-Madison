FIMorphism = new Type of BasicList
FIRingElement = new Type of HashTable
FIRing = new Type of Type

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

source FIMorphism := f -> (length first f) 

mapsbetween = method()

mapsbetween (FIMorphism,Thing,Thing) := (f,a,b) -> target f == b and source f == a

net FIMorphism := l -> net "f_" | net toList l

coefficient (FIRingElement, FIMorphism) := (m,f) -> (
    if (terms m)#?f then return (terms m)#f
    else return 0
    )

fiRing = method()

fiRing (Ring) := R -> (
    F := new FIRing of FIRingElement from hashTable{
        (symbol CoefficientRing) => R;
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
    R * F := (r,m) -> (
        new F from hashTable{
            (symbol ring) => F;
            (symbol terms) => hashTable apply( keys terms m, key -> key => r*coefficient(m,key))
        }
    );
    F * R := (m,r) -> r*m;
    return F
    ) 

--coefficientRing (FIRing) := R -> R#CoefficientRing


fiRingElement = method()

fiRingElement (FIMorphism,FIRing) := (l,R) ->(
    L := new R from hashTable{
	(symbol ring) => R,
	(symbol terms) => hashTable{
	    l => 1  -- TODO we need the 1 from _(coefficientRing R)
	    }
	};
    return L
    )

terms FIRingElement := g -> g.terms

mapsbetween (FIRingElement,Thing,Thing) := (m,a,b) -> (
        all(keys terms m, key-> mapsbetween(key,a,b))
    )

--ring (FIRingElement) := m -> m#Ring



/// TEST 

restart
load "Categories.m2"
f = FI{1,2,5}
g = FI{3,1,2,4,6,7}
h = FI{5,2,6,1,3,7}
source f
target f
mapsbetween(f,3,5)
mapsbetween(f,2,5)
f*g
g*f
R = fiRing(QQ)
m = fiRingElement(f,R)
n = fiRingElement(g,R)
p = fiRingElement(h,R)
x = m+n
y = m+m
z = n+p
mapsbetween(m,2,5)
mapsbetween(x,2,5)
mapsbetween(y,2,5)
mapsbetween(z,5,7)
y === 2*m
y === 2/1*m
y === m*(2/1)

///
