--*
--restart
--loadPackage("VirtualResolutions", Reload =>true)
--installPackage "VirtualResolutions"
--installPackage "CompleteIntersectionResolutions"
--installPackage "BGG"
--viewHelp "VirtualResolutions"
--viewHelp "TateOnProducts"
--viewHelp CompleteIntersectionResolutions
--check "VirtualResolutions"
--*-
---------------------------------------------------------------------------
-- PURPOSE : 
--           
--
-- PROGRAMMERS : 
--               
--
-- UPDATE HISTORY : created 14 April 2018;
---------------------------------------------------------------------------
newPackage ("VirtualResolutions",
    Version => "0.0",
    Date => "April 14, 2018",
    Headline => "Methods for virtual resolutions on products of projective spaces",
    Authors =>{
    	{Name => "Ayah Almousa",       Email => "aka66@cornell.edu"},
    	{Name => "Christine Berkesch", Email => "cberkesc@umn.edu",    HomePage => "http://www-users.math.umn.edu/~cberkesc/"},
	{Name => "Juliette Bruce",     Email => "jebruce@wisc.edu",    HomePage => "https://juliettebruce.github.io"},
        {Name => "David Eisenbud",     Email => "de@msri.org",         HomePage => "http://www.msri.org/~de/"},
	{Name => "Michael Loper",      Email => "loper012@umn.edu",    HomePage => "http://www-users.math.umn.edu/~loper012/"},
        {Name => "Mahrud Sayrafi",     Email => "mahrud@berkeley.edu"}
    	},
    PackageExports => {
	"BGG",
	"TateOnProducts",
	"CompleteIntersectionResolutions",
	"NormalToricVarieties",
	"RandomSpaceCurves"
	},
    DebuggingMode => true,
    AuxiliaryFiles => false
    )

export{
    "curveFromP3toP1P2",
    "DegreeBounds",
    "findCorners",
    "findGensUpToIrrelevance",
    "HideZeros",
    "isVirtual",
    "multiGradedRegularity",
    "multiWinnow",
    "randomRationalCurve",
    "randomMonomialCurve",
    "randomCurve",
    "saturationZero",
    "Bound",
    "PreserveDegree",
    "ShowVirtualFailure"
    }

debug Core
--Given a toric variety and its free resolution, keeps only summands in resolution of specified degrees
--See Theorem 4.1 of [BES]
--TODO: Split multiWinnow and resolveTail
multiWinnow = method();
multiWinnow (NormalToricVariety, ChainComplex, List) := (X,F,alphas) ->(
    if any(alphas, alpha -> #alpha =!= degreeLength ring X) then error "degree has wrong length";
    L := apply(length F, i ->(
	    m := F.dd_(i+1); apply(alphas, alpha -> m = submatrixByDegrees(m, (,alpha), (,alpha))); m));
    N := 0;
    L / (m -> if m != 0 then N = N + 1);
    T := res coker syz L_(N - 1);
    L' := for i from min T to max T - 1 list T.dd_(i+1);
    chainComplex (L_{0..N - 1} | L')
    );

multiWinnow (Ring, ChainComplex, List) := (S,F,alphas) ->(
    if any(alphas, alpha -> #alpha =!= degreeLength S) then error "degree has wrong length";
    L := apply(length F, i ->(
	    m := F.dd_(i+1); apply(alphas, alpha -> m = submatrixByDegrees(m, (,alpha), (,alpha))); m));
    N := 0;
    L / (m -> if m != 0 then N = N + 1);
    T := res coker syz L_(N - 1);
    L' := for i from min T to max T - 1 list T.dd_(i+1);
    chainComplex (L_{0..N - 1} | L')
    );

--Given ideal J, irrelevant ideal, and a vector A, computes free resolution of J intersected with Ath power of the irrelevant ideal
--Only a Virtual resolution for 'sufficiently positive' powers of B
--See Theorem 5.1 of [BES]

intersectionRes = method();
intersectionRes(Ideal, Ideal, List) := ChainComplex => (J, irr, A) -> (
    N := (length A)-1;
    L := decompose irr;
    irrelevantIntersection := {};
    for i from 0 to N do (
	irrelevantIntersection = append(irrelevantIntersection, intersect J, L_i^(A_i));
	);
    res intersect(irrelevantIntersection)
   )

-- TODO: change cohomologyTable to return a Tally, then redo this.
findCorners = m -> (
    corners := {};
    (rows, cols) := (new MutableList, new MutableList);
    for r to numrows m - 1 do (
    	for c to numcols m - 1 do (
	    if m_(r, c) != 0 then (
	    	if not rows#?r or rows#r === null then rows#r = 0;
	    	if not cols#?c or cols#c === null then cols#c = infinity;
	    	rows#r = max(c + 1, rows#r);
	    	cols#c = min(r - 1, cols#c);
    	    	)));
    for r to numrows m - 2 do (
    	if rows#r > rows#(r+1) then rows#(r+1) = rows#r;
    	for c from 1 to numcols m - 1 do (
	    if cols#(c-1) > cols#c then cols#(c-1) = cols#c;
	    ));
    for r to numrows m - 2 do (
    	if rows#r < rows#(r+1) then (
	    for c from 1 to numcols m - 1 do (
	    	if cols#(c-1) < cols#c then (
		    if r === cols#c and rows#r === c then corners = append(corners, {r, c});
		    ))));
    corners
    )

-----------------------------------------------------------
-- This is a temporary fast saturation. Keep this up to date
-- with any changes in Colon.m2 (hopefully we can just change
-- this to saturate(I,irr)
ourSaturation = (I,irr) -> (
    saturationByElimination(I,irr)
    )

-- This is the temporary fast saturation that Mike Stillman created
eliminationInfo = method()
eliminationInfo Ring := (cacheValue symbol eliminationInfo)(R -> (
     n := numgens R;
     k := coefficientRing R;
     X := local X;
     M := monoid [X_0 .. X_n,MonomialOrder=>Eliminate 1,MonomialSize=>16];
     R1 := k M;
     fto := map(R1,R,drop(generators R1, 1));
     fback := map(R,R1,matrix{{0_R}}|vars R);
     (R1, fto, fback)
    ))

-- Computing (I : f^\infty) = saturate(I,f)
-- version #1: elimination
saturationByElimination = method()
saturationByElimination(Ideal, RingElement) := (I, f) -> (
     R := ring I;
     (R1,fto,fback) := eliminationInfo R;
     f1 := fto f;
     I1 := fto I;
     J := ideal(f1*R1_0-1) + I1;
     --g := groebnerBasis(J, Strategy=>"MGB");
     --g := gens gb J;
     g := groebnerBasis(J, Strategy=>"F4");
     p1 := selectInSubring(1, g);
     ideal fback p1
     )

intersectionByElimination = method()
intersectionByElimination(Ideal, Ideal) := (I,J) -> (
     R := ring I;
     (R1,fto,fback) := eliminationInfo R;
     I1 := R1_0 * fto I;
     J1 := (1-R1_0) * fto J;
     L := I1 + J1;
     --g := groebnerBasis(J, Strategy=>"MGB");
     --g := gens gb J;
     g := groebnerBasis(L, Strategy=>"F4");
     p1 := selectInSubring(1, g);
     ideal fback p1
    )

intersectionByElimination List := (L) -> fold(intersectionByElimination, L)

saturationByElimination(Ideal, Ideal) := (I, J) -> (
    L := for g in J_* list saturationByElimination(I, g);
    intersectionByElimination L
    )
--This is where the fast saturation functions end
-----------------------------------------------------------------------

--This method checks if a given complex is a virtual resoltion.
--Input: Chain Complex - proposed virtual resolution
--       Ideal (or module) - what the virtual resolution resolves
--       Ideal - the irrelevant ideal of the ring
--Output: Boolean - true if complex is virtual resolution, false otherwise
isVirtual = method(Options => {ShowVirtualFailure => false})
isVirtual (ChainComplex, Ideal, Ideal) := Boolean => opts -> (C, I, irr) -> ( 
    annHH0 := ideal(image(C.dd_1));
    Isat := ourSaturation(I,irr);
    annHH0sat := ourSaturation(annHH0,irr);
    if not(Isat == annHH0sat) then (
	if opts.ShowVirtualFailure then (
	    return (false,0);
	    );
	return false
	);    
    for i from 1 to length(C) do (
	annHHi := ann HH_i(C);
	if annHHi != ideal(sub(1,ring I)) then (
		if annHHi == 0 then (
		    if opts.ShowVirtualFailure then return (false,i);
		    );
		    return false;
	    	if  ourSaturation(annHHi,irr) != 0 then (
		    if opts.ShowVirtualFailure then (
			return (false,i);
			);
		    return false;
		    )
		)
	);
    true
    )

-* I need to test this still (the part that is commented out
isVirtual (ChainComplex, Module, Ideal) := Boolean=> (C, M, irr) ->( 
    annM := ann(M);
    annHH0 := ann(HH_0(C));
    annMsat := ourSaturation(annM,irr);
    annHH0sat := ourSaturation(annHH0,irr);
    if not(annMsat == annHH0sat) then return (false,0);    
    for i from 1 to length(C) do (
	annHHi := ann HH_i(C);
	if annHHi != ideal(sub(1,ring M)) then (
		if annHHi == 0 then return (false,i);
	    	if  ourSaturation(annHHi,irr) != 0 then (
		    return (false,i);
		    )
		)
	);
    true
    )
*-

findGensUpToIrrelevance = method();
findGensUpToIrrelevance(Ideal,ZZ,Ideal):= List => (J,n,irr) -> (
-- Input: saturated ideal J and ZZ n
-- Output: all subsets of size n of the generators of J that
--         give the same saturated ideal as J
    use ring(J);
    comps := decompose irr;
    lists := subsets(numgens(J),n);
    output := {};
    apply(lists, l -> (
	I := ideal(J_*_l);
	if ourSaturation(ourSaturation(I,comps_0),comps_1) == J then (
	    output = append(output,l);
	         );
	     )
	 );
     output
	    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e,F)=(degree,degree,base ring)
----- Output: The ideal of a random rational curve in P1xP2 of 
----- degree (d,e) defined over F.
----- Description: This randomly generates 2 forms of degree
----- d and 3 forms of degree 3 in the ring S (locally defined), 
----- and computes the ideal defining the image of the map of the
----- associated map P^1---->P^1xP^2.
--------------------------------------------------------------------
--------------------------------------------------------------------
randomRationalCurve = method() 
randomRationalCurve (ZZ,ZZ,Ring) := (d,e,F)->(
    -- Defines P1
    s := getSymbol "s";
    t := getSymbol "t";
    R := F(monoid[s,t]);
    --- Defines P1xP2
    x := getSymbol "x";
    y := getSymbol "y";
    S1 := F(monoid[x_0, x_1]);
    S2 := F(monoid[y_0,y_1,y_2]);
    S := tensor(S1,S2);
    --- Defines P1x(P1xP2)
    U := tensor(R,S);
    uVars := flatten entries vars U;   
    --- Defines graph of morphisms in P1x(P1xP2)
    --M1 := matrix {apply(2,i->random({d,0,0},U)),{x_0,x_1}};
    M1 := matrix {apply(2,i->random({d,0,0},U)),{uVars#2,uVars#3}};
    --M2 := matrix {apply(3,i->random({e,0,0},U)),{y_0,y_1,y_2}};
    M2 := matrix {apply(3,i->random({e,0,0},U)),{uVars#4,uVars#5,uVars#6}};
    J := minors(2,M1)+minors(2,M2);
    --- Computes saturation and then eliminates producing curve in P1xP2
    J' := saturate(J,ideal(uVars#0,uVars#1),MinimalGenerators=>false);
    sub(eliminate({uVars#0,uVars#1},J'),S)
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,degree)
----- Output: The ideal of a random rational curve in P1xP2 of 
----- degree (d,e) defined over ZZ/101
--------------------------------------------------------------------
--------------------------------------------------------------------
randomRationalCurve (ZZ,ZZ) := (d,e)->(
    randomRationalCurve(d,e,ZZ/101)
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e,F)=(degree,degree,base ring)
----- Output: The ideal of a random rational curve in P1xP2 of degree (d,e).
----- Description: This randomly generates 2 monomials of degree
----- d and 3 monomials of degree 3 in the ring S (locally defined), 
----- and computes the ideal defining the image of the map of the
----- associated map P^1---->P^1xP^2.
--------------------------------------------------------------------
--------------------------------------------------------------------
randomMonomialCurve = method() 
randomMonomialCurve (ZZ,ZZ,Ring) := (d,e,F)->(
    --- Defines P1
    s := getSymbol "s";
    t := getSymbol "t";
    R := F[s,t];
    --- Defines P1xP2
    x := getSymbol "x";
    y := getSymbol "y";
    S1 := F(monoid[x_0, x_1]);
    S2 := F(monoid[y_0,y_1,y_2]);
    S := tensor(S1,S2);
    --- Defines P1x(P1xP2)
    U := tensor(R,S);  
    uVars := flatten entries vars U;
    --- Choose random monomial to define map to P2.
    B := drop(drop(flatten entries basis({e,0,0},U),1),-1);
    f := (random(B))#0;
    --- Defines graph of morphisms in P1x(P1xP2)
    M1 := matrix {{(uVars#0)^d,(uVars#1)^d},{uVars#2,uVars#3}};
    M2 := matrix {{(uVars#0)^e,(uVars#1)^e,f},{uVars#4,uVars#5,uVars#6}};
    J := minors(2,M1)+minors(2,M2);
    --- Computes saturation and then eliminates producing curve in P1xP2
    J' := saturate(J,ideal(uVars#0,uVars#1),MinimalGenerators=>false);
    sub(eliminate({uVars#0,uVars#1},J'),S)
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,degree)
----- Output: The ideal of a random rational curve in P1xP2 of
----- of degree (d,e) defined over ZZ/101.
--------------------------------------------------------------------
--------------------------------------------------------------------
randomMonomialCurve (ZZ,ZZ) := (d,e)->(
    randomMonomialCurve(d,e,ZZ/101)
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (J)=(ideal of curve in P3)
----- Output: The ideal of a corresponding curve in P1xP2.
----- Description: Given a curve defined by the ideal J in P3
----- this outputs the ideal I of the curve in P1xP2 given by
----- considering the projection P3---->P1 on the first two variables.
----- and the projection P3----->P2 on the last three variables.
--------------------------------------------------------------------
--------------------------------------------------------------------
curveFromP3toP1P2 = method(Options => {PreserveDegree => true}) 
curveFromP3toP1P2 (Ideal) := randomCurve => opts -> (J) ->(
    --- Defines P3
    R := ring J;
    rVars := flatten entries vars R;
    --- Base locus of projection
    BL1 := ideal(rVars#0,rVars#1);
    BL2 := ideal(rVars#1,rVars#2,rVars#3);
    BL := intersect(BL1,BL2);
    --- If PreserveDegree => true checks whether curve intersects base locus;
    --- this ensures the curve has the correct degree and genus.
    if opts.PreserveDegree == true then (
	    if (saturate((J+BL1))==ideal(rVars)) or (saturate((J+BL2))==ideal(rVars)) then error "Given curve intersects places of projection.";
	);
    --- Defines P1xP2
    x := getSymbol "x";
    y := getSymbol "y";
    S1 := (coefficientRing ring J) monoid([x_0, x_1]);
    S2 := (coefficientRing ring J) monoid([y_0,y_1,y_2]);
    S := tensor(S1,S2);
    --- Defines P3x(P1xP2)
    U := tensor(R,S);   
    uVars := flatten entries vars U;
    --- Place curve in P3x(P1xP2)
    C' := sub(J,U);
    --- Defines graph of projection
    M1 := matrix {{uVars#0,uVars#1},{uVars#4,uVars#5}};
    M2 := matrix {{uVars#1,uVars#2,uVars#3},{uVars#6,uVars#7,uVars#8}};
    D := minors(2,M1)+minors(2,M2);
    --- Intersects irrelevant ideal with base locus
    B1 := ideal(apply(4,i->uVars#i));
    B2 := ideal(apply(2,i->uVars#(4+i)));
    B3 := ideal(apply(3,i->uVars#(6+i)));
    B := intersect(B1,B2,B3,sub(BL,U));
    --- Computes saturation and then eliminates producing curve in P1xP2
    K := saturate(C'+D,B,MinimalGenerators=>false);
    sub(eliminate({uVars#0,uVars#1,uVars#2,uVars#3},K),S)
)

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e,F)=(degree,genus,base ring)
----- Output: The ideal of a random curve in P1xP2 defined over F.
----- Description: This randomly generates a curve of degree d
----- and genus g in P3, and then computes the ideal of the correspnding
----- curve in P1xP2 given by considering the projection 
----- P3---->P1 on the first two variables.
----- and the projection P3----->P2 on the last three variables.
--------------------------------------------------------------------
--------------------------------------------------------------------
randomCurveP1P2 = method(Options => {Bound => 1000}) 
randomCurveP1P2 (ZZ,ZZ,Ring) := opts -> (d,g,F)->(
    --- Defines P3
    z := getSymbol "z";
    R := F(monoid[z_0,z_1,z_2,z_3]);
    rVars := flatten entries vars R;
    --- Base locus of porjection
    BL1 := ideal(rVars#0,rVars#1);
    BL2 := ideal(rVars#1,rVars#2,rVars#3);
    BL := intersect(BL1,BL2);
    --- Randomly generates curve in P3 until finds one not intersecting
    --- base locus of projection or until Bound is reached.
    C := ideal(0);
    apply(opts.Bound,i->(
	    C = (random spaceCurve)(d,g,R);
	    if (saturate(C+BL1)!=ideal(rVars)) and (saturate(C+BL2)!=ideal(rVars)) then break C;
	    ));
    --- Checks whether curve in P3 intersects base locus of projection;
    --- this ensures the curve has the correct degree and genus.
    if (saturate(C+BL1)==ideal(rVars)) or (saturate(C+BL2)==ideal(rVars)) then error "Unable to find curve not intersecting places of projection.";
    --- Defines P1xP2
    curveFromP3toP1P2(C)
)

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,genus)
----- Output: The ideal of a random curve in P1xP2 over ZZ/101
--------------------------------------------------------------------
--------------------------------------------------------------------
randomCurveP1P2 (ZZ,ZZ) := randomCurveP1P2 => opts -> (d,g)->(
    randomCurveP1P2(d,g,ZZ/101)
    )

    
--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (M,B)=(Module,Ideal)
----- Output: Returns true if saturate(M,B)==0 and false otherwise
----- Description: This checks whether the saturation of a module M
----- with respects to an ideal B is zero. This is done by checking 
----- whether for each generator of B some power of it annihilates
----- the module M. We do this generator by generator.
--------------------------------------------------------------------
--------------------------------------------------------------------
saturationZero = method() 
saturationZero (Module,Ideal) := (M,B) ->(
    Vars := flatten entries vars ring B;
    bGens := flatten entries mingens B;
    for i from 0 to #bGens-1 do (
    	  b := bGens#i;
	  bVars := support b;
	      rVars := delete(bVars#1,delete(bVars#0,Vars))|bVars;
	      R := coefficientRing ring B [rVars,MonomialOrder=>{Position=>Up,#Vars-2,2}];
	      P := sub(presentation M,R);
	      G := gb P; 
	      if (ann coker selectInSubring(1,leadTerm G)) == 0 then return false;
    );
    true
)

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (I,B)=(Ideal,Ideal)
----- Output: Returns true if saturate(comodule I,B)==0 and false otherwise.
--------------------------------------------------------------------
--------------------------------------------------------------------
saturationZero (Ideal,Ideal) := (I,B) ->(
    saturationZero(comodule I,B)
)

--------------------------
-- Begining of the documentation
------------------------
beginDocumentation()

doc ///
    Key
    	isVirtual
	(isVirtual,ChainComplex,Ideal,Ideal)
    Headline
    	checks if a chain complex is a virtual resolution of a given ideal
    Usage
    	isVirtual(C,I,irr)
    Inputs
    	C:ChainComplex
	    chain complex we want to check is a virtual resolution
	I:Ideal
	    ideal that the virtual resolution should resolve
	irr:Ideal
	    irrelevant ideal of the ring
    Outputs
    	:Boolean
	    true if C is a virtual resolution of I
	    false if not
    Description
    	Text
	    Given a chain complex C, ideal I, and irrelevant ideal irr, isVirtual returns true if
	    C is a virtual resolution of I. If not, it returns false.
	    
	    This is done by checking that the saturation of I and the saturation of the annihilator of HH_0(C)
	    agree. Then checking that the higher homology groups of C are supported on the irrelevant ideal    	
	Example
       	    isVirtual(res ideal(x),ideal(x),ideal(x,y))
///

doc ///
    Key
    	findGensUpToIrrelevance
	(findGensUpToIrrelevance,Ideal,ZZ,Ideal)
    Headline
    	creates a list of n element subsets of the minimal generators that generate an ideal up to saturation
    Usage
    	findGensUpToIrrelevance(I,n,irr)
    Inputs
    	I:Ideal
	    ideal we are intereseted in
	n:ZZ
	    size of subset of minimal generators of I that may generate I up to saturation with irr
	irr:Ideal
	    irrelvant ideal
    Outputs
    	:List
	    all subsets of size n of generators of I that generate I up to saturation with irr
    Description
    	Text
	    Given an ideal I, integer n, and irrelevant ideal irr, findGensUpToIrrelevance searches through
	    all n-subsets of the generators of I. If a subset generates the same irr-saturated ideal as the
	    irr-saturation of I then that subset is added to a list. After running through all subsets, the list
	    is outputted.
	Example
	    findGensUpToIrrelevance()
    Caveat
	    If no subset of generators generates the ideal up to saturation, then the empty list is outputted
///

doc ///
    Key
    	randomRationalCurve
	(randomRationalCurve,ZZ,ZZ,Ring)
	(randomRationalCurve,ZZ,ZZ)
    Headline
    	creates the Ideal of a random rational curve of degree (d,e) in P^1xP^2
    Usage
    	randomRationalCurve(d,e,F)
    	randomRationalCurve(d,e)
    Inputs
    	d:ZZ
	    degree of curve on the P^1 factor of P^1xP^2
	e:ZZ
	    degree of curve on the P^2 factor of P^1xP^2
	F:Ring
	    base ring
    Outputs
    	:Ideal
	    defining random rational curve in P1xP2 of degree (d,e) over F.
    Description
    	Text
	    Given two positive integers d and e and a ring F randomRationalCurve returns the ideal of a random curve in P1xP2 of degree (d,e) defined over the base ring F. 
	    
	    This is done by randomly generating 2 homogenous polynomials of degree d and 3 homogenous polynomials of degree 3 in F[s,t] defining maps P^1->P^2 and P^1->P^3
	    respectively. The graph of the product of these two maps in P^1x(P^1xP^2) is computed, from which a curve of bi-degree (d,e) in P^1xP^2 over F is obtained by 
	    saturating and then eliminating. 
	    
	    If the no base ring is specified the computations is preformed over F=ZZ/101
	Example
	    randomRationalCurve(2,3,QQ)
	    randomRationalCurve(2,3)
    Caveat
        This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.	
///

doc ///
    Key
    	randomMonomialCurve
	(randomMonomialCurve,ZZ,ZZ,Ring)
	(randomMonomialCurve,ZZ,ZZ)
    Headline
    	creates the Ideal of a random monomial curve of degree (d,e) in P^1xP^2
    Usage
    	randomMonomialCurve(d,e,F)
    	randomMonomialCurve(d,e)
    Inputs
    	d:ZZ
	    degree of curve on the P^1 factor of P^1xP^2
	e:ZZ
	    degree of curve on the P^2 factor of P^1xP^2
	F:Ring
	    base ring
    Outputs
    	:Ideal
	    defining random monomial curve in P^1xP^2 of degree (d,e) over F.
    Description
    	Text
	    Given two positive integers d and e and a ring F randomMonomialCurve returns the ideal of a random curve in P1xP2 of degree (d,e) defined over the base ring F. 
	    
	    This is done by randomly generating a monomial m of degree e in F[s,t], which is not s^e or t^e. This allows one to define two maps P^1->P^1 and P^1->P^2 
	    given by {s^d,t^d} and {s^e,m,t^e} respectively. The graph of the product of these two maps in P^1x(P^1xP^2) is computed, from which a curve 
	    of bi-degree (d,e) in P^1xP^2 over F is obtained by saturating and then eliminating. 
	    
	    If the no base ring is specified the computations is preformed over F=ZZ/101.
	Example
	    randomMonomialCurve(2,3,QQ)
	    randomMonomialCurve(2,3)	
    Caveat
        This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.
///

doc ///
    Key
    	curveFromP3toP1P2
    Headline
    	creates the Ideal of a curve in P^1xP^2 from the ideal of a curve in P^3
    Usage
    	I=curveFromP3toP1P2(J)
    Inputs
    	J:Ideal
	    defining a curve in P^3.
    Outputs
    	I:Ideal
	    defining a curve in P^1xP^2.
    Description
    	Text
	    Given an ideal J defining a curve C in P^3 curveFromP3toP1P2 procudes the ideal of the curve in P^1xP^2 defined as follows: Consider the projections P^3->P^2 and P^3->P^1 
	    from the point [0:0:0:1] and the line [0:0:s:t] respective. The product of these defines a map from P^3 to P^1xP^2. The curve produced by curveFromP3toP1P2 is the image of the input curve under this map.
	    
	    This computation is done by first constructing the graph in P^3x(P^1xP^2) of the product of the two projections P^3->P^2 and P^3->P^1 defined above. This graph is then 
	    intersected with Cx(P^1xP^3). A curve in P^1xP^2 is then obtained from this by saturating and then eliminating. 
	    
	    Note the curve in P^1xP^2 will have degree and genus equal to the degree and genus of C as long as C does not intersect the base locus of the projection. If the option
	    PreserveDegree => true curveFromP3toP1P2 will check whether C intersects the base locus, and if it does will return an error. If PreserveDegree => false this check is not
	    preformed and the output curve in P^1xP^2 may have degree and genus different from C.
	Example
	    R = ZZ/101[z_0,z_1,z_2,z_3];
            C = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
	    curveFromP3toP1P2(J)
    Caveat
        This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.
///

doc ///
    Key
    	randomCurveP1P2
	(randomCurveP1P2,ZZ,ZZ,Ring)
	(randomCurveP1P2,ZZ,ZZ)
    Headline
    	creates the Ideal of a random  curve of degree (d,d) and genus g in P^1xP^2.
    Usage
    	randomCurveP1P2(d,g,F)
    	randomCurveP1P2(d,g)
    Inputs
    	d:ZZ
	    degree of the curve.
	g:ZZ
	    genus of the curve.
	F:Ring
	    base ring
    Outputs
    	:Ideal
	    defining random curve of degree (d,d) and genus g in P1xP2 over F.
    Description
    	Text
	    Given a positive integer d, a non-negative integer g, and a ring F randomCurveP1P2 prouces a random curve of bi-degree (d,d) and genus g in P^1xP^2.
	    This is done by using (random spaceCurve) function from the RandomSpaceCurve package to first generate a random curve of degree d and genus g in
	    P^1xP^2, and then applying curveFromP3toP1P2 to produce a curve in P^1xP^2.
	    
	    Since curveFromP3toP1P2 relies on projecting from the point [0:0:0:1] and the line [0:0:s:t] randomCurveP1P2 attempts to find a curve in P^3, which
	    does not intersect the base locus of these projections. (If the curve did intersect the base locus the resulting curve in P^1xP^2 would not have degree (d,d).)
	    The number of attempts used to try to find such curves is controled by the Bound option, which by default is 1000.
	Example
	    randomCurve(3,0,QQ)
	    randomCurve(3,0)
    Caveat
        This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.

///

doc ///
    Key
    	saturationZero
	(saturationZero,Module,Ideal)
	(saturationZero,Ideal,Ideal)
    Headline
    	checks whether the saturation of a module with respects to a given ideal is zero
    Usage
    	saturationZero(M,B)
	saturationZero(I,B)
    Inputs
    	M:Module
	B:Ideal
        I:Ideal
    Outputs
    	:Boolean
    Description
    	Text
    	    Given an module M and an ideal B saturationZero checks whether the saturation of M by B is zero. If it is 
	    saturationZero returns true otherwise it returns false. This is done without compute the saturation of M by B. 
	    Instead we check whether for each generator of B some power of it annihilates the module M. We do this
	    generator by generator.
	    
	    If M is an ideal saturationZero checks whether the saturation comodule of M by B is zero.
	Example
	    randomCurve(3,0)

///
-------------------------
-- Beginning of the TESTS
-------------------------
------ Tests for randomRationalCurve        
TEST ///
    assert (dim randomRationalCurve(2,3,QQ) == 3)
    ///
    
TEST ///
    assert (degree randomRationalCurve(2,3,QQ) == 2+3)
    ///
    
TEST ///
    assert (dim randomRationalCurve(2,3,ZZ/11) == 3)
    ///
    
TEST ///
    assert (degree randomRationalCurve(2,3,ZZ/11) == 2+3)
    ///
       
TEST ///
    assert (dim randomRationalCurve(2,3) == 3)
    ///

TEST ///
    assert (degree randomRationalCurve(2,3) == 2+3)
    ///

------ Tests for randomMonomialCurve        
TEST ///
    assert (dim randomMonomialCurve(2,3,QQ) == 3)
    ///

TEST ///
    assert (degree randomMonomialCurve(2,3,QQ) == 2+3)
    ///
    
TEST ///
    assert (dim randomMonomialCurve(2,3,ZZ/11) == 3)
    ///

TEST ///
    assert (degree randomMonomialCurve(2,3,ZZ/11) == 2+3)
    ///
           
TEST ///
    assert (dim randomMonomialCurve(2,3) == 3)
    ///

TEST ///
    assert (degree randomMonomialCurve(2,3) == 2+3)
    ///

------ Tests for curveFromP3toP1P2        
TEST ///
    R = ZZ/101[z_0,z_1,z_2,z_3];
    C = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
    assert dim curveFromP3toP1P2(C) == 3
    ///
    
TEST ///
    R = ZZ/101[z_0,z_1,z_2,z_3];
    C = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
    assert dim curveFromP3toP1P2(C,PreserveDegree=>false) == 3
    ///

------ Tests for randomCurveP1P2
TEST ///
    assert (dim randomCurveP1P2(3,0,ZZ/2) == 3)
    ///  

TEST ///
    assert (degree randomCurveP1P2(3,0,ZZ/2) == 3+3)
    ///  
        
TEST ///
    assert (dim randomCurveP1P2(5,2,ZZ/11,Bound=>10) == 3)
    /// 

TEST ///
    assert (degree randomCurveP1P2(5,2,ZZ/11,Bound=>10) == 5+5)
    /// 
    
TEST ///
    assert (dim randomCurveP1P2(3,0) == 3)
    ///  

TEST ///
    assert (degree randomCurveP1P2(3,0) == 3+3)
    ///  
    
TEST ///
    assert (dim randomCurveP1P2(3,0,Bound=>10) == 3)
    ///  

TEST ///
    assert (degree randomCurveP1P2(3,0,Bound=>10) == 3+3)
    ///  
    
TEST ///
    assert (dim randomCurveP1P2(5,2,Bound=>10) == 3)
    /// 

TEST ///
    assert (degree randomCurveP1P2(5,2,Bound=>10) == 5+5)
    ///       

------ Tests for saturationZero     
TEST ///
    S = ZZ/11[x_0,x_1,x_2,x_3,x_4];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    I' = saturate(I,irr);
    R = S^1/I';
    t = (saturate(R,irr)==0);
    assert (saturationZero(R,irr)==t)
    ///

TEST ///
    S = ZZ/11[x_0,x_1,x_2,x_3,x_4];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    I' = saturate(I,irr);
    R = S^1/I';
    t = (saturate(R,irr)==0);
    assert (saturationZero(I',irr)==t)
    ///
    
------ Tests for isVirtual
TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_1^3*x_2+x_1^3*x_3+x_0^3*x_4,
	    x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2,
	    x_0*x_1*x_2^3+x_0*x_1*x_2^2*x_3-x_0^2*x_3^2*x_4+x_1^2*x_2*x_4^2+x_1^2*x_3*x_4^2,
	    x_1^2*x_2^3+x_1^2*x_2^2*x_3-x_0*x_1*x_3^2*x_4-x_0^2*x_4^3}};
    d2 = map(source d1, ,{{x_3^2, x_4^2, -x_2^2},
	{-x_1*x_2-x_1*x_3, 0, x_0*x_4},
	{x_0, -x_1, 0},
	{0, x_0, x_1}});
    C = chainComplex({d1,d2});
    assert(isVirtual(C,I,irr) == true)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2,
	x_0*x_1*x_2^3+x_0*x_1*x_2^2*x_3-x_0^2*x_3^2*x_4+x_1^2*x_2*x_4^2+x_1^2*x_3*x_4^2,
	x_1^2*x_2^3+x_1^2*x_2^2*x_3-x_0*x_1*x_3^2*x_4-x_0^2*x_4^3}};
    C = chainComplex({d1})
    assert(isVirtual(C,I,irr) == false)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2,
	x_0*x_1*x_2^3+x_0*x_1*x_2^2*x_3-x_0^2*x_3^2*x_4+x_1^2*x_2*x_4^2+x_1^2*x_3*x_4^2,
	x_1^2*x_2^3+x_1^2*x_2^2*x_3-x_0*x_1*x_3^2*x_4-x_0^2*x_4^3}};
    C = chainComplex({d1})
    assert(isVirtual(C,I,irr,ShowVirtualFailure => true) == (false,1))
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2}};
    C = chainComplex({d1});
    assert(isVirtual(C,I,irr) == false)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2}};
    C = chainComplex({d1});
    assert(isVirtual(C,I,irr,ShowVirtualFailure => true) == (false,0))
    ///
    
TEST ///
    S = ZZ/101[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(random({1,2},S),random({3,1},S),random({2,2},S));
    r = res I;
    assert(isVirtual(r,I,irr) == true)
    ///

TEST ///
    S = ZZ/101[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(random({1,2},S),random({4,1},S),random({2,2},S));
    J = ourSaturation(I,irr);
    r = res J;
    assert(isVirtual(r,J,irr) == true)
    ///

----- Tests for findGensUpToIrrelevance
TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    J = ourSaturation(I,irr);
    lst = {{0,1}};
    assert(findGensUpToIrrelevance(J,2,irr) == lst)
    ///
    
    
TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    J = ourSaturation(I,irr);
    lst = {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 1, 4}, {0, 2, 4}, {0, 1,5},
	 {0, 3, 5}, {0, 4, 5}, {0, 1, 6}, {0, 1, 7}};
    assert(findGensUpToIrrelevance(J,3,irr) == lst)
    ///
 
end--

restart
needsPackage "SplendidComplexes"
needsPackage "VirtualResolutions"
load "CapeCod.m2"
R = ZZ/32003[a,b, Degrees => {{1,0}, {0,1}}]
I = ideal"a2,b2,ab"
C = res I
--compactMatrixForm = false
betti' C

---------------------------------

restart
needsPackage "VirtualResolutions"
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(2)
S = ring X
irr = ideal X

I = intersect(ideal(x_0, x_2), ideal(x_1, x_3))
J = saturate(I,irr)
hilbertPolynomial(X,J)
C = res J
betti' C
winnow(X, C, {2,1})
winnow(X, C, {1,2})
L = multiWinnow(X, C, {{1,2}, {2,1}})



I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = saturate(I',irr);
hilbertPolynomial(X,J')
r' = res J'
betti' r'
winnow(X, r', {2,3})

---------------------------------
restart
uninstallPackage "BGG"
uninstallPackage "TateOnProducts"
restart
installPackage "BGG"
installPackage "TateOnProducts"
viewHelp BGG

restart
needsPackage "VirtualResolutions"
needsPackage "SplendidComplexes"
needsPackage "BGG"
needsPackage "TateOnProducts"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(1)
S = ring X
irr = ideal X

-- Correct
E = (coefficientRing S)[A_(0)..A_(3), SkewCommutative => true, Degrees=>degrees S]
Q = presentation(S^1)
D = res image symExt(Q, E)
cohomologyTable(D, {-3,-3},{3,3})

-- Not complete
I = intersect(ideal(x_0, x_2), ideal(x_1, x_3))
J = saturate(I,irr)

Q = presentation(S^1/I)
D = res image symExt(Q, E)
cohomologyTable(D, {-3,-3},{3,3})

-- Better
I = ideal(x_0^2*x_2^3)
J' = saturate(I',irr)



-- This is a temporary function, inputs and outputs are changing
multiGradedRegularity = method();
multiGradedRegularity (Module, List, List, ZZ) := (M, D, T, N) -> (
    S = ring M;
    P = presentation(truncate(T, M));
    E = (coefficientRing S)[A_(0)..A_(numgens S - 1), SkewCommutative => true, Degrees=>degrees S];
    se = symExt(P, E);
    print se;
    C = res (image se, LengthLimit => N);
    print betti C;
    C' = res(coker transpose C.dd_(length C + min C), LengthLimit => 2 * length C);
    C' = C'[N];
--    C' := res(coker transpose C.dd_N, LengthLimit => 2 * N);    
    C'' = beilinsonWindow C';
--    C''' = (ring C'')^{D}**(sloppyTateExtension C'');
--    cohomologyTable(C''' ** E^{{-1,-1}}, {-N,-N},{N,N})
    C''' = sloppyTateExtension C'';
    cohomologyTable(C''', {-N,-N},{N,N})
    )

coarseMultigradedRegularity = M -> (
    F := res M;
    el := length F;
    r := degreeLength ring M;
    D := apply((min F..max F), i-> degrees F_i);
    L := flatten apply(length D, i-> apply(D_i, s -> s-toList(r:i)));
    apply(r, p-> max(apply(L, q-> q_p)))
    )


max{{1,2},{2,1}}
cohomology(0,(sheaf S)^{{1,1}}**sheaf M)


M= S^1;D = {1,0};T = {0,0};N = 4; -- works now with any N
M = S^1/S_0^2
M = truncate({1,0},M)
M = S^{{1,0}}**M
degrees presentation M
multiGradedRegularity(M,D,T, N)

C'
C''
C'''
cohomologyTable (E^{{0,-1}}**C''',{-5,-5},{5,5})

M = (S^1++S^{0,2})/ideal(S_0^2,S_2^4)
r = coarseMultigradedRegularity M
M' = truncate(r,M)
D = {1,1};T = {0,0};N = 6; -- works now with any N
multiGradedRegularity(M',D,T, N)


multiGradedRegularity(S^1, {0,0}, {0,0}, 6)
multiGradedRegularity(S^1, {0,0}, {0,0}, 2)

x = symbol x; e = symbol e;
(S,E) = setupRings(ZZ/101,{1,1},x,e)
I = module ideal(x_(0,0)^2*x_(1,0)^3)

T = dual exteriorTateResolution(I,E,{4,5},7)

T = dual exteriorTateResolution(S^1,E,{1,2},5)
C = beilinsonWindow T
C' = sloppyTateExtension C
cohomologyTable (C', {-5,-5},{5,5})

multiGradedRegularity(S^1/I, {0,0}, {2,2}, 3)

multiGradedRegularity(S^1/I, {0,0}, {2,2}, 3) -- FIXME



multiGradedRegularity(S^1 ++ S^{{2,3}}, {0,0}, {0,0}, 4)

-- Finding Multi Graded Regularity
M = S^1/I'
H = multiGradedRegularity(M, {0,0}, {2,3}, 4)
m = diff((ring H)_0, H)
c = (pair -> {5 - first pair, last pair - 5}) \ findCorners m
L = multiWinnow(X, res M, c) --- error


m' = new MutableMatrix from m
m'_(2,4) = 0
m'_(3,5) = 0
m'_(5,6) = 0
m'_(6,7) = 0
m'
findCorners matrix m'

-- Complete
M = S^1/I
C = res M
H = multiGradedRegularity(M, {0,0}, {2,3}, 4)
m = diff((ring H)_0, H)
c = findCorners m
c = (pair -> {5 - first pair, last pair - 5}) \ findCorners m


---------------------
--Mike's Playspace--
---------------------
restart
needsPackage "VirtualResolutions"
needsPackage "SplendidComplexes"
load "CapeCod.m2"

S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}]
irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4))
I = paramCurve(1,3,4);
numgens J
findGensUpToIrrelevance(J',2,irr)
J = ideal(I_2,I_3);
r = res J
betti' r
isVirtual(r,J,irr)


I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = moduleSat(I',irr)
J' = saturate(I',irr)
r' = res J'
betti' r'
q1 = winnowProducts(S,r',{2,1})
prune HH q1
isVirtual(q1,I',irr)
q2 = winnowProducts(S,r',{1,1})
isVirtual(q2,I',irr)

q3 = winnowProducts(S,r',{1,0})
isVirtual(q3,I',irr,ShowVirtualFailure => true)

q1' = multiWinnow(S,r',{{3,3}})
q1' == q1 --multiWinnow doesn't act like winnowProducts
          -- i.e. doesn't add vector n
isVirtual(q1',I',irr)
q2' = multiWinnow(S,r',{{2,3}})
betti' q2'
isVirtual(q2',I',irr)
prune HH q2'
saturate(ideal(image(q2'.dd_1)),irr) == J'
--Test for isVirtual (but bug in multiWinnow)
S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}]
irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4))
I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = saturate(I',irr)
r' = res J'
q1 = multiWinnow(S,r',{{3,3}})
S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}]
irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4))
I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
C1d1 = matrix{{x_1^3*x_2+x_1^3*x_3+x_0^3*x_4,
	    x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2,
	    x_0*x_1*x_2^3+x_0*x_1*x_2^2*x_3-x_0^2*x_3^2*x_4+x_1^2*x_2*x_4^2+x_1^2*x_3*x_4^2,
	    x_1^2*x_2^3+x_1^2*x_2^2*x_3-x_0*x_1*x_3^2*x_4-x_0^2*x_4^3}}
C1d2 = map(source Cd1, ,{{x_3^2, x_4^2, -x_2^2},
	{-x_1*x_2-x_1*x_3, 0, x_0*x_4},
	{x_0, -x_1, 0},
	{0, x_0, x_1}})
C1 = chainComplex({C1d1,C1d2})
isVirtual(C1,I',irr)
q2
q2.dd_1_2
d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2,
	x_0*x_1*x_2^3+x_0*x_1*x_2^2*x_3-x_0^2*x_3^2*x_4+x_1^2*x_2*x_4^2+x_1^2*x_3*x_4^2,
	x_1^2*x_2^3+x_1^2*x_2^2*x_3-x_0*x_1*x_3^2*x_4-x_0^2*x_4^3}}
C2 = chainComplex({d1})
C2 == q2
isVirtual(q2,I',irr)
isVirtual(C2,I',irr)
q3.dd_1
d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2}}
C = chainComplex({d1})
C == q3
assert(isVirtual(q1,I',irr))
assert(isVirtual(q2,I',irr) == (false,1))
assert(isVirtual(q2,I',irr) == (false,0))


I = randomRationalCurve(3,4)
var S
degrees(S)