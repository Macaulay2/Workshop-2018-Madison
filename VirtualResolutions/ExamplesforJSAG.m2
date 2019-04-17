--Example 2.2

restart
needsPackage "VirtualResolutions"
X = toricProjectiveSpace(1)**toricProjectiveSpace(1);
S = ring X; B = ideal X;
J = saturate(intersect(
    ideal(x_1 - 1*x_0, x_3 - 4*x_2),
    ideal(x_1 - 2*x_0, x_3 - 5*x_2),
    ideal(x_1 - 3*x_0, x_3 - 6*x_2)),
     B)

multigradedRegularity(X, module J)
multigradedRegularity(X, S/J)
minres = res J;
multigraded betti minres
vres = multiWinnow(X,minres,{{3,1}}) --(3,1) = (2,0) + (1,1)
multigraded betti vres
isVirtual(J,B,vres)
vres2 = multiWinnow(X,minres,{{2,0}})
isVirtual(J,B,vres2)


-- Trying to find example for intersectionRes
N=6
I = intersect apply(N,i -> ideal(random({1,0},S),random({0,1},S)));
J = saturate(I,B)
I == J
isVirtual(J,B,intersectionRes(J,B,{0,3}))

--example for Mike of spacecurves failing
restart
needsPackage "SpaceCurves"
curve(2,0)
curve(3,0)
curve(3,0,ZZ/2[x_0..x_3])
curve(3,0,ZZ/7[x_0..x_3])
curve(3,0,ZZ/11[x_0..x_3])


-- Same example as above, using productOfProjectiveSpaces instead!
restart
needsPackage "VirtualResolutions"

(S, E) = productOfProjectiveSpaces({1, 1});
B = intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1)));
J = saturate(intersect(
    ideal(x_(0,1) - 1*x_(0,0), x_(1,1) - 4*x_(1,0)),
    ideal(x_(0,1) - 2*x_(0,0), x_(1,1) - 5*x_(1,0)),
    ideal(x_(0,1) - 3*x_(0,0), x_(1,1) - 6*x_(1,0))),
    B)

multigradedRegularity(S, module J)

-- multigradedRegularity(X, comodule J) -- FIXME: this fails:
--VirtualResolutions.m2:446:13:(3):[2]: error: ring map applied to module with relations: use '**' or 'tensor' instead
--        M = (map(ring X, S, gens ring X))(M');

minres = res J;
multigraded betti minres
vres = multiWinnow(S,minres,{{3,1}}) --(3,1) = (2,0) + (1,1)
multigraded betti vres
isVirtual(J,B,vres)
vres2 = multiWinnow(S,minres,{{2,0}})
isVirtual(J,B,vres2)



-------------
-------------
-- Build P1xP2 and the irrelvant ideal
(S, E) = productOfProjectiveSpaces({1, 2});
B =  intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1), x_(1,2)));
--- construct a curve in P1xP2 from the twisted cubic
R = QQ[z_0,z_1,z_2,z_3];
I = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
J = curveFromP3toP1P2(I);
--- putting the curve J into our product of projective spaces and saturating ...
T = ring J;
F = map(S,T,(flatten entries vars S));
K = F(J);
K' = saturate(K,B);
minres = res K';
--- sanity check on the dimension
dim K' == 3
multigradedRegularity(S, module K')
vres = multiWinnow(S,minres,{{0,0}})

-------------
-------------
K = randomCurveP1P2(5,2)
dim K == 3
T = ring K;
B1 =  intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1), x_(1,2)));
K'  = saturate(K,B1);
multigradedRegularity(T, module K')

-- Build P1xP2 and the irrelvant ideal
(S, E) = productOfProjectiveSpaces({1, 2});
B2 =  intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1), x_(1,2)));
--- putting the curve J into our product of projective spaces and saturating ...
F = map(S,T,(flatten entries vars S));
I = F(K);
J = saturate(I,B2);

multigradedRegularity(S, module J)

minres = res J;
vres = multiWinnow(S,minres,{{2,2}})

multigraded betti minres
multigraded betti vres

--- sanity check on the dimension
dim K' == 3
multigradedRegularity(S, module K')
vres = multiWinnow(S,minres,{{2,2}})

-------------
-------------
I = randomRationalCurve(5,11);
dim I == 3
T = ring I;
-- Build P1xP2 and the irrelvant ideal
(S, E) = productOfProjectiveSpaces({1, 2});
B =  intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1), x_(1,2)));
--- putting the curve J into our product of projective spaces and saturating ...
F = map(S,T,(flatten entries vars S));
K = F(I);
K' = saturate(K,B);
minres = res K';
--- sanity check on the dimension
dim K' == 3
multigradedRegularity(S, module K')
vres = multiWinnow(S,minres,{{0,0}})
