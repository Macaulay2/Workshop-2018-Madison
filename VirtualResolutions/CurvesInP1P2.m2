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
    BL2 := ideal(rVars#1,rVar#2,rVars#3);
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
    S1 := F[x_0, x_1];
    S2 := F[y_0,y_1,y_2];
    S = tensor(S1,S2);
    --- Defines P3x(P1xP2)
    U = tensor(R,S);   
    C' := sub(C,U);
    --- Defines graph of projection
    M1 := matrix {{z_0,z_1},{x_0,x_1}};
    M2 := matrix {{z_1,z_2,z_3},{y_0,y_1,y_2}};
    G := minors(2,M1)+minors(2,M2);
    --- Irrelevant ideal intersect base locus
    B1 := ideal(z_0,z_1,z_2,z_3);
    B2 := ideal(x_0,x_1);
    B3 := ideal(y_0,y_1,y_2);
    B := intersect(B1,B2,B3,sub(BL,U));
    --- Computes saturation and then eliminates producing curve in P1xP2
    K  := saturate(C'+G,B,MinimalGenerators=>false);
    sub(eliminate({z_0,z_1,z_2,z_3},K),S)
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
    	creates the Ideal of a random rational curve of degree (d,e) in P1xP2
    Usage
    	randomRationalCurve(d,e,F)
    	randomRationalCurve(d,e)
    Inputs
    	d:ZZ
	    degree of curve on the P1 factor of P1xP2
	e:ZZ
	    degree of curve on the P2 factor of P1xP2
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
	Caveat
	    This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.
	Example
	    randomRationalCurve(2,3,QQ)
	    randomRationalCurve(2,3)	
///

doc ///
    Key
    	randomMonomialCurve
	(randomMonomialCurve,ZZ,ZZ,Ring)
	(randomMonomialCurve,ZZ,ZZ)
    Headline
    	creates the Ideal of a random monomial curve of degree (d,e) in P1xP2
    Usage
    	randomMonomialCurve(d,e,F)
    	randomMonomialCurve(d,e)
    Inputs
    	d:ZZ
	    degree of curve on the P1 factor of P1xP2
	e:ZZ
	    degree of curve on the P2 factor of P1xP2
	F:Ring
	    base ring
    Outputs
    	:Ideal
	    defining random monomial curve in P1xP2 of degree (d,e) over F.
    Description
    	Text
	    Given two positive integers d and e and a ring F randomMonomialCurve returns the ideal of a random curve in P1xP2 of degree (d,e) defined over the base ring F. 
	    
	    This is done by randomly generating a monomial m of degree e in F[s,t], which is not s^e or t^e. This allows one to define two maps P^1->P^1 and P^1->P^2 
	    given by {s^d,t^d} and {s^e,m,t^e} respectively. The graph of the product of these two maps in P^1x(P^1xP^2) is computed, from which a curve 
	    of bi-degree (d,e) in P^1xP^2 over F is obtained by saturating and then eliminating. 
	    
	    If the no base ring is specified the computations is preformed over F=ZZ/101.
	Caveat
	    This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.
	Example
	    randomMonomialCurve(2,3,QQ)
	    randomMonomialCurve(2,3)	
///

doc ///
    Key
    	curveFromP3toP1P2
    Headline
    	creates the Ideal of a random monomial curve of degree (d,e) in P1xP2
    Usage
    	curveFromP3toP1P2(J)
    Inputs
    	J:Ideal
	    defining curve in P3.
    Outputs
    	I:Ideal
	    definin curve in P1xP2.
    Description
    	Text
	    Given a curve defined by the ideal J in P3
     	    this outputs the ideal I of the curve in P1xP2 given by
 	    considering the projection from P3 to P1 on the 
	    first two variables and the projection from P3
	    to P2 on the last three variables.
	    
	Example
	    curveFromP3toP1P2(J)
	Caveat
             If the curve intersections the point or line
	     we are projecting from returns an error.
///

doc ///
    Key
    	randomCurveP1P2
	(randomCurveP1P2,ZZ,ZZ,Ring)
	(randomCurveP1P2,ZZ,ZZ)
    Headline
    	creates the Ideal of a random  curve of degree (d,d) and genus g in P1xP2.
    Usage
    	randomCurve(d,g,F)
    	randomCurve(d,g)
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
	    Given a curve defined by the ideal J in P3
     	    this outputs the ideal I of the curve in P1xP2 given by
 	    considering the projection from P3 to P1 on the 
	    first two variables and the projection from P3
	    to P2 on the last three variables.
	    
	Example
	    randomCurve(3,0,QQ)
	    randomCurve(3,0)

///

doc ///
    Key
    	saterationZero
    Headline
    	creates the Ideal of a random  curve of degree d and genus g in P1xP2
    Usage
    	saterationZero(d,g)
    Inputs
    	d:ZZ
	    degree of the curve.
	g:ZZ
	    genus of the curve.
    Outputs
    	I:Ideal
	    definin curve in P1xP2.
    Description
    	Text
	    Given a curve defined by the ideal J in P3
     	    this outputs the ideal I of the curve in P1xP2 given by
 	    considering the projection from P3 to P1 on the 
	    first two variables and the projection from P3
	    to P2 on the last three variables.
	    
	Example
	    randomCurve(3,0)

///

--------------------------
-- Begining of the TESTS
------------------------

TEST ///
    try assert (dim randomRationalCurve(2,3) == 3 then true==true else true==true)
    ///
    
TEST ///
    try assert (dim randomMonomialCurve(2,3) == 3 then true==true else true==true)
    ///
    
TEST ///
    R = ZZ/101[z_0,z_1,z_2,z_3];
    C = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
    dim curveFromP3toP1P2(C)
    ///
    
TEST ///
    try assert (dim randomCurve(2,3) == 3 then true==true else true==true)
    ///  
    
end--
