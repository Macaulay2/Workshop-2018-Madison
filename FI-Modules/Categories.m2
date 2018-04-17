FIMorphism = new Type of BasicList
FIRingElement = new Type of HashTable
FIMatrix = new Type of MutableHashTable
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

FIMorphism#{Standard,AfterPrint} = 
FIMorphism#{Standard,AfterNoPrint} = f -> (
     << endl;                 -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : FIMorphism";
     << " " << source f << " ---> " << target f;
     << endl;
     )

net FIMorphism := l -> net "["|net l#0|net ","|net l#1|net"]"




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
    RFI - RFI := (m, n) -> m + (-1)_R*n;
    return RFI
    ) 


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
      tempNet := net t#1;
      printParens := ring t#1 =!= QQ and ring t#1 =!= ZZ and not isZp and (size t#1 > 1 or (isField ring t#1 and numgens coefficientRing ring t#1 > 0 and size sub(t#1, coefficientRing ring t#1) > 1));
      myNet = myNet | (
        if isZp and tempNet#0#0 != "-" and not firstTerm then net "+"
        else if not isZp and not firstTerm and t#1>0 then net "+"
        else net ""
      ) | (
        if printParens then net "(" else net ""
      ) | (
        if t#1 != 1 and t#1 != -1 then tempNet
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
    if not all(fiEntries, row -> all(#coldeglist, i->isFromTarget(row#i,coldeglist#i))) then error "The targets of the entries don't match the degrees in the columns.";
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
    if numColumns M == numRows N then (
	new FIMatrix from hashTable{
	    (symbol ring) => ring M,
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

restart
load "Categories.m2"
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
mat = fiMatrix ({2,5},{{x,0_R},{0_R,y+t^2*z}},{5,7})


///
