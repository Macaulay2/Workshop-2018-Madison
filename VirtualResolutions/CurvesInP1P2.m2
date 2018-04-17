newPackage ("CurvesP1P2",
    Version => "0.0",
    Date => "April 14, 2018",
    Headline => "Methods for generating curves in P1xP2",
    Authors =>{
    	{
	    Name => "Juliette Bruce", 
	    Email => "juliette.bruce@math.wisc.edu", 
	    HomePage => "http://www.math.wisc.edu/~juliettebruce/"},
	{
	    Name => "Mike Loper",
	    Email => "loper012@umn.edu",
	    HomePage => "http://www.math.umn.edu/~loper012"}
    	},
    DebuggingMode => true
    )

needsPackage "SimpleDoc"
needsPackage "RandomSpaceCurves";
export{
    "randomRationalCurve",
    "randomMonomialCurve",
    "curveFromP3toP1P2",
    "randomCurve",
    "saturationZero",
    }


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
    R := F[s,t];
    --- Defines P1xP2
    S1 := F[x_0, x_1];
    S2 := F[y_0,y_1,y_2];
    S = tensor(S1,S2);
    --- Defines P1x(P1xP2)
    U = tensor(R,S);   
    --- Defines graph of morphisms in P1x(P1xP2)
    M1 := matrix {apply(2,i->random({d,0,0},U)),{x_0,x_1}};
    M2 := matrix {apply(3,i->random({e,0,0},U)),{y_0,y_1,y_2}};
    J := minors(2,M1)+minors(2,M2);
    --- Computes saturation and then eliminates producing curve in P1xP2
    J' := saturate(J,ideal(s,t),MinimalGenerators=>false);
    sub(eliminate({s,t},J'),S)
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
    R := F[s,t];
    --- Defines P1xP2
    S1 := F[x_0, x_1];
    S2 := F[y_0,y_1,y_2];
    S = tensor(S1,S2);
    --- Defines P1x(P1xP2)
    U = tensor(R,S);  
    --- Choose random monomial to define map to P2.
    B := drop(drop(flatten entries basis({e,0,0},U),1),-1);
    f := (random(B))#0;
    --- Defines graph of morphisms in P1x(P1xP2)
    M1 := matrix {{s^d,t^d},{x_0,x_1}};
    M2 := matrix {{s^e,t^e,f},{y_0,y_1,y_2}};
    J := minors(2,M1)+minors(2,M2);
    --- Computes saturation and then eliminates producing curve in P1xP2
    J' := saturate(J,ideal(s,t),MinimalGenerators=>false);
    sub(eliminate({s,t},J'),S)
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
    S1 := coefficientRing ring J [x_0, x_1];
    S2 := coefficientRing ring J [y_0,y_1,y_2];
    S = tensor(S1,S2);
    --- Defines P3x(P1xP2)
    U = tensor(R,S);   
    urVars := apply(rVars,i->sub(i,U));
    uVars := flatten entries vars U;
    --- Place curve in P3x(P1xP2)
    C' := sub(J,U);
    --- Defines graph of projection
    M1 := matrix {{urVars#0,urVars#1},{x_0,x_1}};
    M2 := matrix {{urVars#1,urVars#2,urVars#3},{y_0,y_1,y_2}};
    D := minors(2,M1)+minors(2,M2);
    --- Intersects irrelevant ideal with base locus
    B1 := ideal(apply(4,i->uVars#i));
    B2 := ideal(apply(2,i->uVars#(4+i)));
    B3 := ideal(apply(3,i->uVars#(6+i)));
    B := intersect(B1,B2,B3,sub(BL,U));
    --- Computes saturation and then eliminates producing curve in P1xP2
    K := saturate(C'+D,B,MinimalGenerators=>false);
    sub(eliminate(urVars,K),S)
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
randomCurveP1P2 (ZZ,ZZ,Ring) := randomCurveP1P2 => opts -> (d,g,F)->(
    --- Defines P3
    R := F[z_0,z_1,z_2,z_3];
    rVars := flatten entries vars R;
    --- Base locus of porjection
    BL1 := ideal(z_0,z_1);
    BL2 := ideal(z_1,z_2,z_3);
    BL := intersect(BL1,BL2);
    --- Randomly generates curve in P3 until finds one not intersecting
    --- base locus of projection or until Bound is reached.
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
	      G = gb P; 
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
    	CurvesInP1P2
    Headline
    	Methods for generating curves in P1xP2
    Description
    	Text
	    This package contains methods for generating examples of curves in P1xP2.
    Caveat
        This package is underdevelopment.
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
    	curveFromP3toP1P2(J)
    Inputs
    	J:Ideal
	    defining a curve in P^3.
    Outputs
    	:Ideal
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

--------------------------
-- Begining of the TESTS
------------------------

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
    dim curveFromP3toP1P2(C) == 3
    ///
    
TEST ///
    R = ZZ/101[z_0,z_1,z_2,z_3];
    C = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
    dim curveFromP3toP1P2(C,PreserveDegree=>false) == 3
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
end--
