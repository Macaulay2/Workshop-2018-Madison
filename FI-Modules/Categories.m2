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

mapsbetween = method()

mapsbetween (FIMorphism,Thing,Thing) := (f,a,b) -> target f == b and source f == a

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
	    (symbol ring) => F,
	    (symbol terms) => hashTable	apply(unique( keys terms m| keys terms n), key ->(
			 coefsum = coefficient(m,key) + coefficient(n,key);
			 if coefsum =!= 0_R then key => coefsum
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
    F * F := (m,n) -> (
        eltsum = 0_F;
        for mkey in keys terms m do
            for nkey in keys terms n do
                if target mkey === source nkey then
                    eltsum = eltsum + (coefficient(m,mkey)*coefficient(n,nkey))*fiRingElement(mkey*nkey,F);
        return eltsum
    );
    return F
    ) 

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

    

coefficientRing FIRing := R -> last R.baseRings


FIRing_List := (R, l) -> fiRingElement(FI l, R)

ZZ _ FIRing := (n,R) -> (
    if n =!= 0 then error "ZZ_FIRing is only defined for 0_FIRing"
    else return new R from hashTable{
        symbol ring => F;
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



mapsbetween (FIRingElement,Thing,Thing) := (m,a,b) -> (
        all(keys terms m, key-> mapsbetween(key,a,b))
    )

ring (FIRingElement) := m -> m.ring



/// TEST 

restart
load "Categories.m2"
R = fiRing(QQ)
coefficientRing R
f = R_{1,2,5}
g = R_{2,3,1,4}
f+g
2*f
S = fiRing(ZZ/2)
S_{2,1,3}+S_{2,1,3}+S_{2,1,4}
m = fiRingElement(f,R)
n = fiRingElement(g,R)
p = fiRingElement(h,R)
x = m+n
y = m+m
z = n+p
x*z
mapsbetween(m,2,5)
mapsbetween(x,2,5)
mapsbetween(y,2,5)
mapsbetween(z,5,7)
y === 2*m
y === 2/1*m
y === m*(2/1)

///
