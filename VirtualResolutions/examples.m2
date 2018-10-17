---
--- Presentation in Madison
---

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
betti' winnow(X, C, {2,1})
betti' winnow(X, C, {1,2})
betti' multiWinnow(X, C, {{1,2}, {2,1}})


restart
needsPackage "SplendidComplexes"
needsPackage "VirtualResolutions"
debug needsPackage "TateOnProducts"

(X, E) = productOfProjectiveSpaces {1, 2}
irr = intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1), x_(1,2)))
I' = ideal(x_(0,0)^2*x_(1,0)^2+x_(0,1)^2*x_(1,1)^2+x_(0,0)*x_(0,1)*x_(1,2)^2, x_(0,0)^3*x_(1,2)+x_(0,1)^3*(x_(1,0)+x_(1,1)))
J' = saturate(I',irr);
r' = res J'
m = cohomologyMatrix(X^1/J', {0,0},{6,6})


I = intersect(ideal(x_(0,0), x_(1,0)), ideal(x_(0,1), x_(1,1)))
J = saturate(I,irr)
C = res J
betti' C
betti' multiWinnow(X, C, {{1,2}, {2,1}})
betti' multiWinnow(X, C, multigradedRegularity module J)

multigradedRegularity module J -- ??





-- Finding Multi Graded Regularity
restart
needsPackage "VirtualResolutions"
needsPackage "SplendidComplexes"
needsPackage "BGG"
needsPackage "TateOnProducts"
load "CapeCod.m2"

X = projectiveSpace(1)**projectiveSpace(1)
S = ring X
irr = ideal X

-- Better
I' = ideal(x_0^2*x_2^3)
J' = saturate(I',irr)

-- This is a temporary function, inputs and outputs are changing
multiGradedRegularity = method();
multiGradedRegularity (Module, List, List, ZZ) := (M, D, T, N) -> (
    S := ring M;
    P := presentation(truncate(T, M ** (ring M)^{D}));
    E := (coefficientRing S)[A_(0)..A_(numgens S - 1), SkewCommutative => true, Degrees=>degrees S];
    C := res image symExt(P, E);
    C = C;
    C' := res(coker transpose C.dd_(length C + min C), LengthLimit => 2 * length C);
    C'' := beilinsonWindow C';
    C''' := (sloppyTateExtension C'')[N];
    cohomologyTable(C''' ** E^{{-1,-1}}, {-5,-5},{5,5})
    )

H = multiGradedRegularity(S^1, {0,0}, {0,0}, 5)
m = diff((ring H)_0, H)

M = S^1/I'
H = multiGradedRegularity(M, {0,0}, {2,3}, 4)
m = diff((ring H)_0, H)
c = (pair -> {5 - first pair, last pair - 5}) \ findCorners m
L = multiWinnow(X, res M, c) --- error



----------------------------------------------
-- Examples from Leipzig
----------------------------------------------



---

restart
needsPackage "TateOnProducts"
needsPackage "VirtualResolutions"

N = {2,2}
(S, E) = productOfProjectiveSpaces N

M = cokernel matrix {{x_(1,0)^2*x_(1,1), x_(0,0)*x_(0,1)^3, x_(0,0)^2*x_(0,1)*x_(1,1)^2, x_(0,0)*x_(0,1)^2*x_(1,1)^2, x_(0,1)^3*x_(1,0)^2, x_(0,0)^3*x_(1,0)^3}}
--M = cokernel matrix {{x_(0,0)^2*x_(1,1), x_(0,0)^2*x_(0,1)^2, x_(0,0)^2*x_(1,0)^3, x_(0,0)^3*x_(1,0)^2, x_(0,1)^3*x_(1,0)^2, x_(0,1)^2*x_(1,0)*x_(1,1)^3}}
R = regularity M

(low, high) = ({1,0}, {5, 4})

m = cohomologyMatrix(M, low, high)
findCorners(m, low, high)

ht = cohomologyHashTable(M, low, high)
findCorners ht

---

restart
debug loadPackage "TateOnProducts"
needsPackage "VirtualResolutions"

n={1,2};
(S,E) = productOfProjectiveSpaces n
F=dual res((ker transpose vars E)**E^{{ 2,3}},LengthLimit=>4)

M = cohomologyMatrix(F,-{3,3},{4,4})
findCorners(M, -{3,3}, {4,4})

H = cohomologyHashTable(F,-{3,3},{4,4});
findCorners H

P = cohomologyPolynomialTable(F,-{3,3},{4,4})
findCorners P


betti F
tallyDegrees F
deg={2,1} 
m=upperCorner(F,deg);
tally degrees target m, tally degrees source m
Fm=(res(coker m,LengthLimit=>4))[sum deg+1]
betti Fm

M' = cohomologyMatrix(Fm,-{3,3},{4,4})
findCorners(M', -{3,3}, {4,4})



C = cornerComplex(Fm,{4,4})
C' = sloppyTateExtension C
cohomologyMatrix(C,-{3,3},{4,4})



-----

restart
debug loadPackage "TateOnProducts"
needsPackage "VirtualResolutions"

(S, E) = productOfProjectiveSpaces({2,2})
(low, high) = ({-3,-3},{3,3})


M = cohomologyMatrix(S^1++S^{{-2,3}}, low, high)



findCorners(diff((ring M)_0, M), low, high)


ht = cohomologyHashTable(S^1++S^{{-2,3}}, low, high)
findCorners ht








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
