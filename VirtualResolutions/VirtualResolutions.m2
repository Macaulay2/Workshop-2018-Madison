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
    	{Name => "Ayah Almousa",       Email => "aka66@cornell.edu",   HomePage => "http://www.math.cornell.edu/~aalmousa "},
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
	"SpaceCurves"
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
    "multiWinnow",
    "randomRationalCurve",
    "randomMonomialCurve",
    "randomCurveP1P2",
    "saturationZero",
    "Bound",
    "PreserveDegree",
    "ShowVirtualFailure",
    "GeneralElements"
    }

debug Core


--Given a ring and its free resolution, keeps only the summands in resolution of specified degrees
--See Theorem 4.1 of [BES]
multiWinnow = method();
--Input: F a free chain complex on Cox (X), alphas a list of degrees
--Output: A subcomplexs of summands generated only in degrees in the list alphas.
--If the list alphas contains only one element, the output will be summands generated in degree less than or equal to alpha.
multiWinnow (NormalToricVariety, ChainComplex, List) := (X, F, alphas) -> multiWinnow(ring X, F, alphas)
multiWinnow (Ring,               ChainComplex, List) := (S, F, alphas) ->(
    if any(alphas, alpha -> #alpha =!= degreeLength S) then error "degree has wrong length";
    L := apply(length F, i ->(
	    m := F.dd_(i+1); apply(alphas, alpha -> m = submatrixByDegrees(m, (,alpha), (,alpha))); m));
    chainComplex(L)
    );


resolveTail = method();
--Input: A chain complex
--Output: The resolution of the tail end of the complex appended to the chain complex
--It is not known if applying multiWinnow and then resolveTail yields a Virtual Resolution or not
--TODO: Write tests
--      Add length limit
resolveTail(ChainComplex) := (F) ->(
   N := 0;
   F / (m -> if m != 0 then N = N + 1);
   T := res coker syz F_(N - 1);
   F' := for i from min T to max T - 1 list T.dd_(i+1);
   chainComplex (F_{0..N - 1} | F')
);


--Given ideal J, irrelevant ideal, and a vector A, computes free resolution of J intersected with Ath power of the irrelevant ideal
--Only a Virtual resolution for 'sufficiently positive' powers of B
--See Theorem 5.1 of [BES]
--TODO: Fix, write tests

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
--Input: Ideal I (or module) - what the virtual resolution resolves
--       Ideal irr - the irrelevant ideal of the ring
--       Chain Complex C - proposed virtual resolution
--Output: Boolean - true if complex is virtual resolution, false otherwise
--TODO: need to fix for modules
isVirtual = method(Options => {ShowVirtualFailure => false})
isVirtual (Ideal, Ideal, ChainComplex) := Boolean => opts -> (I, irr, C) -> (
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
		    return false;
		    );
	    	if  ourSaturation(annHHi,irr) != ideal(sub(1,ring I)) then (
		    if opts.ShowVirtualFailure then (
			return (false,i);
			);
		    return false;
		    )
		)
	);
    true
    )

isVirtual (Module, Ideal, ChainComplex) := Boolean => opts -> (M, irr,C) ->(
    annM := ann(M);
    annHH0 := ann(HH_0(C));
    annMsat := ourSaturation(annM,irr);
    annHH0sat := ourSaturation(annHH0,irr);
    if not(annMsat == annHH0sat) then (
	if opts.ShowVirtualFailure  then return (false,0);
	return false;
	);
    for i from 1 to length(C) do (
	annHHi := ann HH_i(C);
	if annHHi != ideal(sub(1,ring M)) then (
		if annHHi == 0 then (
		    if opts.ShowVirtualFailure then return (false,i);
		    return false;
		    );
	    	if  ourSaturation(annHHi,irr) != ideal(sub(1,ring irr)) then (
		    if opts.ShowVirtualFailure then return (false,i);
		    return false;
		    )
		)
	);
    true
    )


findGensUpToIrrelevance = method(Options => {GeneralElements => false});
findGensUpToIrrelevance(ZZ,Ideal,Ideal):= List => opts -> (n,J,irr) -> (
--Input: ZZ n - size of subset of generators to check
--       Ideal J - ideal of ring
--       Ideal irr - irrelevant ideal
-- Output: all subsets of size of the generators of J that give
--         the same ideal as J up to saturation by the irrelevant ideal
--         If the option GeneralElements is set to true, then
--         before outputting the subsets, the ideal generatered by the
--         general elements is outputted
    R := ring(J);
    k := coefficientRing(R);
    Jsat := ourSaturation(J,irr);
    comps := decompose irr;
    if opts.GeneralElements == true then (
	degs := degrees(J);
	--place of all unique degrees
	allmatches := unique(apply(degs,i->positions(degs, j -> j == i)));
	--creates an ideal where if degrees of generators match
 	--  those generators are replaced by one generator that
	--  is a random combination of all generators of that degree
	K := ideal(apply(allmatches,i->sum(apply(i,
			j-> random(k) * J_(j)))));
	J = K;
	);
    lists := subsets(numgens(J),n);
    output := {};
    if opts.GeneralElements == true then output = {J};
    apply(lists, l -> (
	I := ideal(J_*_l);
	if ourSaturation(ourSaturation(I,comps_0),comps_1) == Jsat then (
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
    J' := ourSaturation(J,ideal(uVars#0,uVars#1));
    --J' := saturate(J,ideal(uVars#0,uVars#1),MinimalGenerators=>false);
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
curveFromP3toP1P2 (Ideal) := opts -> (J) ->(
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
--    K := saturate(C'+D,B,MinimalGenerators=>false);
    K := ourSaturation(C'+D,B);
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
	    C = curve(d,g,R);
	    if class(C) === Curve then C = ideal(C);
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

----------------------------------------------
-- Begining of the tests and the documentation
----------------------------------------------

load ("./tests.m2")
beginDocumentation()
load ("./doc.m2")


end--

--------------------------------------
-- Begining of the development section
--------------------------------------

restart
uninstallPackage "VirtualResolutions"
restart
installPackage "VirtualResolutions"
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
--needsPackage "SplendidComplexes"
--needsPackage "BGG"
needsPackage "TateOnProducts"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(1)
S = ring X
irr = ideal X

-- Correct
E = (coefficientRing S)[A_(0)..A_(3), SkewCommutative => true, Degrees=>degrees S]
Q = presentation(S^1)
D = res image symExt(Q, E)
cohomologyMatrix(D, {-3,-3},{3,3})

-- Not complete
I = intersect(ideal(x_0, x_2), ideal(x_1, x_3))
J = saturate(I,irr)

Q = presentation(S^1/I)
D = res image symExt(Q, E)
cohomologyMatrix(D, {-3,-3},{3,3})

-- Better
I' = ideal(x_0^2*x_2^3)
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

--little helper function
J = J'
numgens J
degs = degrees(J)
matches = {}
matches = apply(degs,i ->  apply(degs,j -> if i == j then j))
position(degs,i -> i==degs_0)
newdegs = drop(degs,{0,0})
degs == newdegs
length(newdegs)
length(degs)
matches = {}
while length(degs) > 0 do (
    postns = positions(degs,i->i==degs_0);
    if length(postns) > 1 then (
	matches = append(matches,postns);
	);
    degs = delete(degs_0,degs);
    )

--The bottom two lines are what I should replace the ideal with
-- for more general elements
allmatches = unique(apply(degs,i->positions(degs, j -> j == i)))
K = ideal(apply(allmatches,i->sum(apply(i,j->random(ZZ/32003) * J_(j)))))

matches = allmatches_(positions(allmatches,i->length(i)>1))
