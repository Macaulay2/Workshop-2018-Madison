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
-- This one might take too long...
    S = ZZ/101[x_0,x_1,x_2,x_3,x_4, Degrees=>{2:{1,0},3:{0,1}}];
    irr = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
    I = ideal(random({1,2},S),random({3,1},S),random({2,2},S));
    J = ourSaturation(I,irr);
    r = res J;
    assert(isVirtual(r,I,irr) == true)
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
