
----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
------------- Example 2.2
----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
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

M = S^1/J
P = presentation M
multigradedRegularity(X, S^1/J)

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





----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
------------- Example 3.1
----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
R = QQ[z_0,z_1,z_2,z_3];
I = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
J = curveFromP3toP1P2(I)

dim J

----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
------------- Example 3.2
----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
I = randomCurveP1P2(7,3);
S = ring I;
dim I

B = intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1), x_(1,2)));
J = saturate(I,B);

multigradedRegularity(S, S^1/J)

minres = res J;
vres = multiWinnow(S,minres,{{3,5}});

multigraded betti minres
multigraded betti vres


----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
------------- Example 3.3
----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
I = randomRationalCurve(5,7);
dim I 
