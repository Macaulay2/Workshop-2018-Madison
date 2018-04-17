-*
restart
loadPackage("VirtualResolutions", Reload =>true)
installPackage "VirtualResolutions"
installPackage "CompleteIntersectionResolutions"
installPackage "BGG"
viewHelp "VirtualResolutions"
viewHelp "TateOnProducts"
viewHelp CompleteIntersectionResolutions
check "VirtualResolutions"
*-
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
        {Name => "David Eisenbud",     Email => "de@msri.org",         HomePage => "http://www.msri.org/~de/"},
        {Name => "Mahrud Sayrafi",     Email => "mahrud@berkeley.edu"}
    	},
    PackageExports => {
	"BGG",
	"TateOnProducts",
	"CompleteIntersectionResolutions",
	"NormalToricVarieties"
	},
    DebuggingMode => true,
    AuxiliaryFiles => false
    )

export{
--    "multiGradedRegularity"
    "findCorners",
    "multiWinnow",
    "HideZeros",
    "DegreeBounds",
    "isVirtual",
    "findGensUpToIrrelevance"
    }

debug Core

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

-- This is a temporary fast saturation. Keep this up to date
-- with any changes in Colon.m2 (hopefully we can just change
-- this to saturate(I,irr)
ourSaturation = (I,irr) -> (
    saturationByElimination(I,irr)
    )

-- This is the temporary fast saturation that Mike created
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


isVirtual = method();
-* I need to test this still
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
isVirtual (ChainComplex, Ideal, Ideal) := Boolean=> (C, I, irr) ->( 
    annHH0 := ideal(image(C.dd_1));
    Isat := ourSaturation(I,irr);
    annHH0sat := ourSaturation(annHH0,irr);
    if not(Isat == annHH0sat) then return (false,0);    
    for i from 1 to length(C) do (
	annHHi := ann HH_i(C);
	if annHHi != ideal(sub(1,ring I)) then (
		if annHHi == 0 then return (false,i);
	    	if  ourSaturation(annHHi,irr) != 0 then (
		    return (false,i);
		    )
		)
	);
    true
    )

findGensUpToIrrelevance = (J,n,irr) -> (
-- Input: saturated ideal J and ZZ n
-- Output: all subsets of size n of the generators of J that
--         give the same saturated ideal as J
    use ring(J);
    comps := decompose irr;
    lists := subsets(numgens(J),n);
    output := {};
    apply(lists, l -> (
	<< "doing " << l << endl;
	I := ideal(J_*_l);
	if elapsedTime ourSaturation(ourSaturation(I,comps_0),comps_1) == J then (
	    output = append(output,l);
	         );
	     )
	 );
     output
	    )


--------------------------
-- Begining of the documentation
------------------------
beginDocumentation()



-------------------------
-- Beginning of the TESTS
-------------------------


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
    P = presentation(truncate(T, M ** (ring M)^{D}));
    E = (coefficientRing S)[A_(0)..A_(numgens S - 1), SkewCommutative => true, Degrees=>degrees S];
    se = symExt(P, E);
    print se;
    C = res (image se, LengthLimit => N);
    print betti C;
    C' = res(coker transpose C.dd_(length C + min C), LengthLimit => 2 * length C);
    C' = C'[N];
--    C' := res(coker transpose C.dd_N, LengthLimit => 2 * N);    
    C'' = beilinsonWindow C';
    C''' = (sloppyTateExtension C'');
    cohomologyTable(C''' ** E^{{-1,-1}}, {-N,-N},{N,N})
    )


M= S^1;D = {0,0};T = {0,0};N = 4; -- works now with any N
M = S^{{-1,0}}**truncate({1,0}, S^1/S_0)
degrees M
multiGradedRegularity(M,D,T, N)
C'
C''
C'''
cohomologyTable (E^{{0,-1}}**C''',{-5,-5},{5,5})

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
load "badsaturations.m2"

S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}]
irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4))
I = paramCurve(1,3,4);
numgens I
findGensUpToIrrelevance(I,2,irr)
J = ideal(I_2,I_3);
r = res J
betti' r
isVirtual(r,J,irr)


I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = ourSaturation(I',irr)
J' = saturate(I',irr)
r' = res J'
betti' r'
q1 = winnowProducts(S,r',{2,1})
prune HH q1
isVirtual(q1,I',irr)
q2 = winnowProducts(S,r',{1,1})
isVirtual(q2,I',irr)

q3 = winnowProducts(S,r',{1,0})
isVirtual(q3,I',irr)
