------ Tests for randomRationalCurve
TEST ///
    assert (dim randomRationalCurve(2,3,ZZ/101) == 3)
    ///

TEST ///
    assert (degree randomRationalCurve(2,3,ZZ/101) == 2+3)
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
    assert (dim randomMonomialCurve(2,3,ZZ/101) == 3)
    ///

TEST ///
    assert (degree randomMonomialCurve(2,3,ZZ/101) == 2+3)
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
    assert (dim curveFromP3toP1P2(C) == 3)
    ///

TEST ///
    R = ZZ/101[z_0,z_1,z_2,z_3];
    C = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
    assert (dim curveFromP3toP1P2(C,PreserveDegree=>false) == 3)
    ///

------ Tests for randomCurveP1P2
TEST ///
    assert (dim randomCurveP1P2(3,0,ZZ/101) == 3)
    ///

TEST ///
    assert (degree randomCurveP1P2(3,0,ZZ/101) == 3+3)
    ///

TEST ///
    assert (dim randomCurveP1P2(5,2,ZZ/101,Bound=>10) == 3)
    ///

TEST ///
    assert (degree randomCurveP1P2(5,2,ZZ/101,Bound=>10) == 5+5)
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
    assert(isVirtual(I,irr,C) == true)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2,
	x_0*x_1*x_2^3+x_0*x_1*x_2^2*x_3-x_0^2*x_3^2*x_4+x_1^2*x_2*x_4^2+x_1^2*x_3*x_4^2,
	x_1^2*x_2^3+x_1^2*x_2^2*x_3-x_0*x_1*x_3^2*x_4-x_0^2*x_4^3}};
    C = chainComplex({d1});
    assert(isVirtual(I,irr,C) == false)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2,
	x_0*x_1*x_2^3+x_0*x_1*x_2^2*x_3-x_0^2*x_3^2*x_4+x_1^2*x_2*x_4^2+x_1^2*x_3*x_4^2,
	x_1^2*x_2^3+x_1^2*x_2^2*x_3-x_0*x_1*x_3^2*x_4-x_0^2*x_4^3}};
    C = chainComplex({d1});
    assert(isVirtual(I,irr,C) == false)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2}};
    C = chainComplex({d1});
    assert(isVirtual(I,irr,C) == false)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    d1 = matrix{{x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2}};
    C = chainComplex({d1});
    assert(isVirtual(I,irr,C) == false)
    ///

TEST ///
    S = ZZ/101[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(random({1,2},S),random({3,1},S),random({2,2},S));
    r = res I;
    assert(isVirtual(I,irr,r) == true)
    ///

-- problem with ourSaturation    
TEST ///
-- This one might take too long...
    S = ZZ/101[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(random({1,2},S),random({3,1},S),random({2,2},S));
    J = ourSaturation(I,irr);
    r = res J;
    assert(isVirtual(I,irr,r) == true)
    ///
    
-- problem with ourSaturation    
----- Tests for findGensUpToIrrelevance
TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    J = ourSaturation(I,irr);
    lst = {{0,1}};
    assert(findGensUpToIrrelevance(2,J,irr) == lst)
    ///

-- problem with ourSaturation    
TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    J = ourSaturation(I,irr);
    lst = {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 1, 4}, {0, 2, 4}, {0, 1,5},
	 {0, 3, 5}, {0, 4, 5}, {0, 1, 6}, {0, 1, 7}};
    assert(findGensUpToIrrelevance(3,J,irr) == lst)
    ///

TEST ///
    S = ZZ/32003[x_0,x_1,y_0,y_1, Degrees=>{2:{1,0},2:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(y_0,y_1));
    I = intersect(ideal(x_0,y_0),ideal(x_1,y_1));
    output = findGensUpToIrrelevance(2,I,irr,GeneralElements=>true);
    assert(length(output) == 3 and output_1 == {0,1} and output_2 == {1,2})
    ///
 
--- problem with ourSaturation    
TEST ///
    S = ZZ/32003[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
    J = ourSaturation(I,irr);
    output = findGensUpToIrrelevance(3,I,GeneralElements=>true);
    assert(length(output) == 5 and output_1 == {0,1,2} and
	    output_2 == {0,1,3} and output_3 == {0,2,3} and
	    output_4 = {0,1,4})
    ///

-- Test for intersectionRes
TEST ///
    debug needsPackage "TateOnProducts"
    N = {1,1,2} -- Example 5.7 of [BES] uses 1x1x2 and 6 points
    pts = 6
    (S, E) = productOfProjectiveSpaces N
    irr = intersect for n to #N-1 list (
    	ideal select(gens S, i -> (degree i)#n == 1)
    	)
    -- Generate ideal of 6 random points in P1xP1xP2
    I = saturate intersect for i to pts - 1 list (
  	print i;
  	P := sum for n to N#0 - 1 list ideal random({1,0,0}, S);
  	Q := sum for n to N#1 - 1 list ideal random({0,1,0}, S);
  	R := sum for n to N#2 - 1 list ideal random({0,0,1}, S);
  	P + Q + R
  	)
    assert isVirtual(I, irr, intersectionRes (I, irr, {2,1,0}))
    assert isVirtual(I, irr, intersectionRes (I, irr, {3,3,0}))
    ///
    
-- Tests for multiWinnow
    
TEST ///
    debug needsPackage "TateOnProducts"
    needsPackage "VirtualResolutions"
    N = {1,2}; -- Example 5.7 of [BES] uses 1x1x2 and 6 points
    (S, E) = productOfProjectiveSpaces N;
    irr = intersect for n to #N-1 list (
    	ideal select(gens S, i -> (degree i)#n == 1)
    	);
    I = intersect(ideal(x_(0,0), x_(1,0)), ideal(x_(0,1), x_(1,1)));
    J = saturate(I, irr);
    C = res J;
    D = multiWinnow(S, C, {{1,2}, {2,1}})
    assert isVirtual(J,irr,D)
    ///
    
TEST ///
    X = toricProjectiveSpace(1)**toricProjectiveSpace(1);
    S = ring X; B = ideal X;
    J = saturate(intersect(
    	    ideal(x_1 - 1*x_0, x_3 - 4*x_2),
    	    ideal(x_1 - 2*x_0, x_3 - 5*x_2),
    	    ideal(x_1 - 3*x_0, x_3 - 6*x_2)),
     	    B) 
    minres = res J;
    vres = multiWinnow(X,minres,{{3,1}}) --(3,1) = (2,0) + (1,1)
    assert isVirtual(J,B,vres)