FIMorphism = new Type of HashTable
-- a list, representing the images of {1..n} under an injective
-- function to ZZ
FIRingElement = new Type of HashTable
-- The Type for elements of arbitrary FI Rings
FIMatrix = new Type of MutableHashTable
-- A Matrix of FI Ring elements: a ring (the ambient FI ring of the
-- matrix elts, rowdegs a list of row labels, coldegs a list of column
-- degress, matrix a table of FIRingElements FIRing = new Type of Type
FIRing = new Type of Ring
globalAssignment FIRing

-- FI MORPHISMS
--================================

FI = method()

-- FI {1,3,4} gives the FIMorphism corresponding to the injective
-- function {1,2,3} -> the positive integers that sends 1 to 1, 2 to
-- 3, and 3 to 4.
FI List := l -> (  
    if #l >#unique l then error "FI: list does not give injective map"
    else if all (l,i -> class i === ZZ and i<1) then error "FI: list is not a list of positive integers"
    else new FIMorphism from hashTable{ (symbol morphismList) => l}
)

-- composition of FI morphisms, as injective functions. The domain and
-- range have to agree. So (FI {2,1,5,6}) * (FI {1,4}) should be (FI {2,6})
FIMorphism * FIMorphism := (f, g) -> (
    if target f > source g then error "Morphisms are not composable."
    else new FIMorphism from hashTable{ (symbol morphismList) => apply(f.morphismList, i -> (g.morphismList)#(i-1))}
)

-- target is the domain of the FI morphism, and source is the smallest
-- {1..n} that contains the image
target FIMorphism := f -> max f.morphismList
source FIMorphism := f -> length f.morphismList

-- add data to class print.
FIMorphism#{Standard,AfterPrint} = 
FIMorphism#{Standard,AfterNoPrint} = f -> (
     << endl;                 -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : FIMorphism";
     << " " << source f << " ---> " << target f;
     dumbfix = " --"; -- local syntax highlighting fix
     << endl;
)
 
-- nets for printing
net FIMorphism := l -> net l.morphismList


FIMorphism == FIMorphism := (f,g) -> f.morphismList == g.morphismList




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
    			 if coefsum =!= 0_R then key => coefsum
    			 ))	
    	    }
	);
    R * RFI := (r,m) -> (
        new RFI from hashTable{
            (symbol ring) => RFI,
            (symbol terms) => hashTable apply( keys terms m, key -> key => r*coefficient(m,key))
        }
    );
    RFI * R := (m,r) -> r*m;
    ZZ * RFI := (r,m) -> (r_R)*m;
    RFI * ZZ := (m,r) -> m*(r_R);
    RFI * RFI := (m,n) -> (
        eltsum = 0_RFI;
        for mkey in keys terms m do
            for nkey in keys terms n do
                if target mkey <= source nkey then
                    eltsum = eltsum + (coefficient(m,mkey)*coefficient(n,nkey))*fiRingElement(mkey*nkey,RFI);
        return eltsum
    );
    RFI - RFI := (m, n) -> m + (-1)_R*n;
    RFI == RFI := (m,n) -> pairs m.terms == pairs n.terms;
    return RFI
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

ZFI := fiRing(ZZ)

net FIRing := RFI -> net (coefficientRing RFI)|net " FI"

FIMorphism + FIMorphism := (f,g) -> fiRingElement(f,ZFI) + fiRingElement(g,ZFI)

FIMorphism + FIRingElement := (f,m) -> fiRingElement(f, ring m) + m

FIRingElement + FIMorphism := (m,f) -> f+m






coefficient (FIRingElement, FIMorphism) := (m,f) -> (
    if (terms m)#?f then return (terms m)#f
    else return 0
    )

terms FIRingElement := g -> g.terms


{*net FIRingElement := f -> (
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
    else net 0
    )
*}



net FIRingElement := f -> (
   if #(f.terms) == 0 then return net "0";
   
   firstTerm := true;
   myNet := net "";
   isZp := (class coefficientRing ring f === QuotientRing and ambient coefficientRing ring f === ZZ);
   for t in pairs f.terms do (
      coefNet := net t#1;
      coefSign := ("-" == first last coefNet);
      printParens := ring t#1 =!= QQ and ring t#1 =!= ZZ and not isZp and (size t#1 > 1 or (isField ring t#1 and numgens coefficientRing ring t#1 > 0 and size sub(t#1, coefficientRing ring t#1) > 1));
      myNet = myNet | (
        if (not coefSign or printParens) and not firstTerm then net "+"
        else net ""
      ) | (
        if printParens then net "(" else net ""
      ) | (
        if t#1 != 1 and t#1 != -1 then coefNet
        else if t#1 == -1 then net "-"
        else net ""
      ) | (
        if printParens then net ")" else net ""
      ) | (
        net t#0
      );
      firstTerm = false;
   );
   myNet
)

isToTarget=method()

isToTarget (FIRingElement,Thing) := (m,b) -> (
        if m === 0_(ring m) then return true
        else return all (keys terms m,key ->target key <= b)
    )    

isFromSource=method()

isFromSource (FIRingElement, Thing) := (m,a) -> (
        if m === 0_(ring m) then return true
        else return all (keys terms m,key -> source key == a)
    )

{*isHomogeneous FIRingElement := m -> (
        if m === 0_(ring m) then return true
        else return all (keys terms m,key -> source key == source first keys terms m and target key == target first keys terms m)
    )
*}




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


-- FI MATRICES
--================================

fiMatrix = method()

fiMatrix (List,List,List) := (rowdeglist,fiEntries,coldeglist) -> (
    if not isTable fiEntries then error "Expected a rectangular matrix.";
    -- number of rows, cols
    if 1 != fiEntries // flatten / class // unique // length then error "Expected all entries to be from the same FIRing.";
    if #rowdeglist =!= #fiEntries then error "Row degrees don't match matrix";
    if #coldeglist =!= #(fiEntries#0) then error "Col degrees don't match matrix";
    if not all(#rowdeglist, i -> all(fiEntries#i, m->isFromSource(m,rowdeglist#i))) then error "The sources of the entries don't match the degrees in the rows.";
    if not all(fiEntries, row -> all(#coldeglist, i->isToTarget(row#i,coldeglist#i))) then error "The targets of the entries don't match the degrees in the columns.";
    -- find a common ring to promote all entries to. For now, just
    -- expect them to be from the same ring. If not, throw an error.
    return new FIMatrix from hashTable {
    (symbol ring, (fiEntries#0#0).ring),
    (symbol rowdegs, rowdeglist),
	(symbol matrix, fiEntries),
    (symbol coldegs, coldeglist),
	(symbol cache, new CacheTable from {})};
    )


FIMatrix#{Standard,AfterPrint} = 
FIMatrix#{Standard,AfterNoPrint} = M -> (
     << endl;                 -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : FIMatrix";
     << " ";
     if #M.rowdegs == 0 then << "0"
     else (
        firstTerm = true;
        for deg in M.rowdegs do (
            if not firstTerm then << " + ";
            << "M(" << deg << ")";
            firstTerm = false;
        );
     );
     <<" <--- ";
     dumbfix = " --";
     if #M.coldegs == 0 then << "0"
     else (
        firstTerm = true;
        for deg in M.coldegs do (
            if not firstTerm then << " + ";
            << "M(" << deg << ")";
            firstTerm = false;
        );
     );
     << endl
     )

net FIMatrix := M -> (
    MyNet := net (Table ( {{""}|(M.coldegs)}| apply(#(M.rowdegs),i->(({(M.rowdegs)#i})| ((M.matrix)#i) )) ));
    StringList := unstack(MyNet);
    colnum := max(apply(M.rowdegs,d -> length toString d))+1;
    rowwidth := width MyNet;
    StringList1 := {substring(StringList#0,0,colnum)|" "|substring(StringList#0,colnum)|" ",pad(colnum+1," ")|pad(rowwidth-colnum+1," ")};
    StringList2 := apply(take(StringList,{2,#StringList}), str -> (
        if #str == 0 then pad(colnum+1,"|")|pad(rowwidth-colnum+1,"|")
        else if #str<rowwidth then substring(str,0,colnum)|"|"|substring(str,colnum)|pad(rowwidth-#str+1,"|")
        else substring(str,0,colnum)|"|"|substring(str,colnum)|"|"
        ));
    return stack(StringList1|StringList2)
    )

--{{""}|{1,2}}| apply(#b,i->b#i| a#i)
--Table applyTable({{"",Table {M.coldegs}},{Table M.rowdegs,MatrixExpression applyTable(M.matrix, expression)}},expression)
entries FIMatrix := M -> M.matrix
numRows FIMatrix := M -> #(entries M)
numColumns FIMatrix := M -> #(first entries M)
ring FIMatrix := M -> M.ring

FIMatrix * FIMatrix := (M, N) -> (
    entriesM := entries M;
    entriesN := entries N;
    if colDegrees M == rowDegrees N then (
    new FIMatrix from hashTable{
        (symbol ring) => ring M,
        (symbol rowdegs) => rowDegrees M,
        (symbol coldegs) => colDegrees N,
        (symbol matrix) => apply(numRows M, 
        i -> apply(numColumns N, 
            j -> sum apply(numColumns M, k -> entriesM#i#k*entriesN#k#j)
            )
        ),
        (symbol cache) => new CacheTable from {}
        }
    )
    )

rowDegrees = method()

rowDegrees FIMatrix := M -> M.rowdegs

colDegrees = method()

colDegrees FIMatrix := M -> M.coldegs


/// TEST 
-- FI

restart
load "Categories.m2"

f = FI{1,3}
g = FI{2,6,5,1}
f*g

-- fiRing

restart
load "Categories.m2"

f = FI{1,3}
g = FI{2,6,5,1}
h = FI{3,4,5}
x = f+g
y = x +h

S = fiRing(ZZ/3)
f = S_{2,1,3}+S_{2,1,3}+S_{2,1,3}
g = S_{1,4,5,6}
f*g


-- FIMatrix Tests

restart
load "Categories.m2"
f = FI{1,2,5}

R = fiRing(ZZ/3[t])
f = FI{1,2,5}
g = FI{3,1,2,4,6,7}
h = FI{5,2,6,1,3,7}
x = fiRingElement(f,R);
y = fiRingElement(g,R);
z = fiRingElement(h,R);
mat = fiMatrix ({2,5},{{x,0_R},{0_R,2*y+(-t^2-t)*z}},{5,7})
mat1 = fiMatrix( {5,7}, {{fiRingElement(FI({2,3,5,1,6,6}),R),fiRingElement(FI({4,6,1,3,7,7}),R)},{0_R,fiRingElement(FI({4,3,1,5,6,7,2,7}),R)}}, {6,7} )
mat*mat1

-- John's multiplication Test

restart
load "Categories.m2"

R = fiRing(QQ)
m = fiMatrix({1,2},{{R_{1}-2*R_{2},R_{1}+R_{2}+R_{3}},{R_{1,2}-R_{2,1},R_{1,2}+R_{2,3}+R_{3,1}}},{2,3})
o = fiMatrix({2,3},{{R_{1,2},R_{2,3}-R_{3,2}},{0_R,R_{1,2,3}+R_{2,3,1}+R_{3,1,2}}},{2,3})
m*o

-- Demo for Dan

restart
load "Categories.m2"

R = ZZ/101
RFI = fiRing(R)
f = fiRingElement(FI{1,3,5,110},RFI)
100*f


-- Demo for Aida

restart
load "Categories.m2"

RFI = fiRing(ZZ/3)
m = RFI_{4,2,1}
n = RFI_{1,6,2}
m-n
5*m


///
