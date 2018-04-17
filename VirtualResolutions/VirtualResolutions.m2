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
    "multiWinnow",
    "HideZeros",
    "DegreeBounds"
    }

debug Core

multiWinnow = method();
multiWinnow (NormalToricVariety, ChainComplex, List) := (X,F,alphas) ->(
    if any(alphas, alpha -> #alpha =!= degreeLength ring X) then error "degree has wrong length";
    L := apply(length F, i ->(
	    m := F.dd_(i+1);
	    apply(alphas, alpha -> m = submatrixByDegrees(m, (,alpha), (,alpha)));
	    m
	    ));
    chainComplex L
    );

---------------------------------
-- Beginning of the documentation
---------------------------------
beginDocumentation()



-------------------------
-- Beginning of the TESTS
-------------------------


end--

restart
installPackage "VirtualResolutions"
viewHelp "VirtualResolutions"
viewHelp "TateOnProducts"
check "VirtualResolutions"

---------------------------------

restart
needsPackage "SplendidComplexes"
needsPackage "VirtualResolutions"
R = ZZ/32003[a,b, Degrees => {{1,0}, {0,1}}]
I = ideal"a2,b2,ab"
C = res I
betti' C
compactMatrixForm = false
betti' C

---------------------------------

restart
needsPackage "VirtualResolutions"
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(2)
S = ring X
irr = ideal X
I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = saturate(I',irr);
hilbertPolynomial(X,J')
r' = res J'
betti' r'
compactMatrixForm = false
betti' r'

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
M = S^1/S_0
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


multiGradedRegularity(S^1 ++ S^{{2,3}}, {0,0}, {0,0}, 4)

H = multiGradedRegularity(S^1/I', {0,0}, {2,3}, 4)
m = diff((ring H)_0, H)

(rows, cols) = (new MutableList, new MutableList);
for r to numrows m - 1 do (
    (maxR, maxC) := (0, 0);
    for c to numcols m - 1 do (
	if m_(r, c) =!= 0 then (maxC = max(c, maxC); maxR = max(c, maxC));
    	))
