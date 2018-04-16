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

source FIMorphism := f -> (length first f) 

net FIMorphism := l -> net "f_" | net toList l


-- FI RINGS
--================================

fiRing = method()

fiRing (Ring) := R -> (
    RFI := new FIRing of FIRingElement from hashTable{
        baseRings => (R.baseRings)|{R}
	};
    RFI + RFI := (m,n) -> (
    	new RFI from hashTable{
    	    (symbol ring) => RFI,
    	    (symbol terms) => hashTable	apply(unique( keys terms m| keys terms n), key ->(
    			 coefsum = coefficient(m,key) + coefficient(n,key);
    			 if coefsum =!= 0 then key => coefsum
    			 ))	
    	    }
	);
    R * RFI := (r,m) -> (
        new RFI from hashTable{
            (symbol ring) => F;
            (symbol terms) => hashTable apply( keys terms m, key -> key => r*coefficient(m,key))
        }
    );
    RFI * R := (m,r) -> r*m;
    RFI * RFI := (m,n) -> (
        eltsum = 0_RFI;
        for mkey in keys terms m do
            for nkey in keys terms n do
                if target mkey === source nkey then
                    eltsum = eltsum + (coefficient(m,mkey)*coefficient(n,nkey))*fiRingElement(mkey*nkey,RFI);
        return eltsum
    );
    return RFI
    ) 


coefficient (FIRingElement, FIMorphism) := (m,f) -> (
    if (terms m)#?f then return (terms m)#f
    else return 0
    )

terms FIRingElement := g -> g.terms


net FIRingElement := f -> (
    termsf := terms f;
    keysf := keys termsf;
    kk := coefficientRing ring f;
    N := #(keysf);
    printCoefficient := m -> (
	c := coefficient(f,m);
	if c == 1_kk then net ""
	else net c
	);
    local m;
    if N == 1 then (
	m = first keysf;
	return printCoefficient(m)|net m
	)
    else if N > 1 then (
	horizontalJoin apply(N, i -> (
		m := keysf#i;
		if i < N-1 then printCoefficient(m)|net m|net " + "
		else printCoefficient(m)|net m
		)
	    )
	)
    )

isFromTarget=method()

isFromTarget (FIRingElement,Thing) := (m,b) -> (
        if m === 0_(ring m) then return true
        else return all (keys terms m,key ->target key == b)
    )    

isFromSource=method()

isFromSource (FIRingElement, Thing) := (m,a) -> (
        if m === 0_(ring m) then return true
        else return all (keys terms m,key -> source key == a)
    )

isHomogeneous FIRingElement := m -> (
        if m === 0_(ring m) then return true
        else return all (keys terms m,key -> source key == source first keys terms m and target key == target first keys terms m)
    )


coefficientRing FIRing := R -> last R.baseRings


FIRing_List := (R, l) -> fiRingElement(FI l, R)

ZZ _ FIRing := (n,R) -> (
    if n =!= 0 then error "ZZ_FIRing is only defined for 0_FIRing"
    else return new R from hashTable{
        symbol ring => R,
        symbol terms => hashTable{}
    }
    )


fiRingElement = method()

fiRingElement (FIMorphism,FIRing) := (l,R) ->(
    kk := coefficientRing R;
    L := new R from hashTable{
	(symbol ring) => R,
	(symbol terms) => hashTable{
	    l => 1_kk
	    }
	};
    return L
    )



ring (FIRingElement) := m -> m.ring



/// TEST 

restart
load "Categories.m2"
f = FI{1,2,5}
g = FI{3,1,2,4,6,7}
h = FI{4,2,1,5,6,7}
QQFI = fiRing(QQ)
coefficientRing R
S = fiRing(ZZ[x])
coefficientRing S
0_QQFI
0_S
m = fiRingElement(f,QQFI)
n = fiRingElement(g,QQFI)
p = fiRingElement(h,QQFI)
f+g
2*f
S = fiRing(ZZ/2)
S_{2,1,3}+S_{2,1,3}+S_{2,1,4}
x = m+n
y = m+m
z = n+p
x*z
y === 2*m
y === 2/1*m
y === m*(2/1)
isFromSource(x*z,2)
isHomogeneous(x*z)
isHomogeneous(0_RFI)
isHomogeneous x

///
