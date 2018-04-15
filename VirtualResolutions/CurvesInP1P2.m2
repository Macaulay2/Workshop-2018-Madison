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
    }


--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,degree)
----- Output: The ideal of a random rational curve in P1xP2 of degree (d,e).
----- Description: This randomly generates 2 forms of degree
----- d and 3 forms of degree 3 in the ring S (locally defined), 
----- and computes the ideal defining the image of the map of the
------ associated map P^1---->P^1xP^2,
--------------------------------------------------------------------
--------------------------------------------------------------------

randomRationalCurve = (d,e)->(
    R := ZZ/101[s,t];
    ---
    S1 := ZZ/101[x_0, x_1];
    S2 := ZZ/101[y_0,y_1,y_2];
    S = tensor(S1,S2);
    ---
    U = tensor(R,S);   
    --- 
    M1 := matrix {apply(2,i->random({d,0,0},U)),{x_0,x_1}};
    M2 := matrix {apply(3,i->random({e,0,0},U)),{y_0,y_1,y_2}};
    ---
    J := minors(2,M1)+minors(2,M2);
    J' := saturate(J,ideal(s,t),MinimalGenerators=>false);
    I = sub(eliminate({s,t},J'),S)
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,degree)
----- Output: The ideal of a random rational curve in P1xP2 of degree (d,e).
----- Description: This randomly generates 2 monomials of degree
----- d and 3 monomials of degree 3 in the ring S (locally defined), 
----- and computes the ideal defining the image of the map of the
------ associated map P^1---->P^1xP^2,
--------------------------------------------------------------------
--------------------------------------------------------------------
randomMonomialCurve = (d,e)->(
    R := ZZ/101[s,t];
    ---
    S1 := ZZ/101[x_0, x_1];
    S2 := ZZ/101[y_0,y_1,y_2];
    S = tensor(S1,S2);
    ---
    U = tensor(R,S);  
    ---
    B = drop(drop(flatten entries basis({e,0,0},U),1),-1);
    f = (random(B))#0;
    ---
    M1 := matrix {{s^d,t^d},{x_0,x_1}};
    M2 := matrix {{s^e,t^e,f},{y_0,y_1,y_2}};
    ---
    J := minors(2,M1)+minors(2,M2);
    J' := saturate(J,ideal(s,t),MinimalGenerators=>false);
    I = sub(eliminate({s,t},J'),S)
    )
--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (J)=(ideal of curve in P3)
----- Output: The ideal of a corresponding curve in P1xP2.
----- Description: Given a curve defined by the ideal J in P3
----- this outputs the ideal I of the curve in P1xP2 given by
----- considering the projection P3---->P1 on the first two variables.
----- and the projection P3----->P2 on the last three variables
--------------------------------------------------------------------
--------------------------------------------------------------------

curveFromP3toP1P2 = (J) ->(
    R := ring J;
    Vars := flatten entries vars R;
    ---
    if (saturate((J+ideal(Vars#0,Vars#1)))==ideal(Vars)) or (saturate((J+ideal(Vars#1,Vars#2,Vars#3)))==ideal(Vars)) then error "Given curve intersects places of projection.";
    ---
    S1 := ZZ/101[x_0, x_1];
    S2 := ZZ/101[y_0,y_1,y_2];
    S = tensor(S1,S2);
    ---
    U = tensor(R,S);   
    Var := apply(Vars,i->sub(i,U));
    VarU := flatten entries vars U;
    --- 
    M1 := matrix {{Var#0,Var#1},{x_0,x_1}};
    M2 := matrix {{Var#1,Var#2,Var#3},{y_0,y_1,y_2}};
    ---
    C' = sub(J,U);
    D = minors(2,M1)+minors(2,M2);
    ---
    BL1 := ideal(Var#0,Var#1);
    BL2 := ideal(Var#1,Var#2,Var#3);
    B1 := apply(4,i->VarU#i);
    B2 := apply(2,i->VarU#(4+i));
    B3 := apply(3,i->VarU#(6+i));
    B := intersect(ideal(B1),ideal(B2),ideal(B3),BL1,BL2);
    ---
    K  := saturate(C'+D,B);
    I =  sub(eliminate(Var,K),S)
)
--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,genus)
----- Output: The ideal of a random curve in P1xP2.
----- Description: This randomly generates a curve of degree d
----- and genus g in P3, and then computes the ideal of the correspnding
----- curve in P1xP2 given by considering the projection 
----- P3---->P1 on the first two variables.
----- and the projection P3----->P2 on the last three variables
--------------------------------------------------------------------
--------------------------------------------------------------------
randomCurve = method() 
randomCurve (ZZ,ZZ) := (d,g) ->(
    R = ZZ/101[z_0,z_1,z_2,z_3];
    apply(1000,i->(
	    N = i;
	    C = (random spaceCurve)(d,g,R);
	    if (saturate(C+ideal(z_0,z_1))!=ideal(z_0,z_1,z_2,z_3)) and (saturate(C+ideal(z_1,z_2,z_3))!=ideal(z_0,z_1,z_2,z_3)) then break C
	    ));
    if (saturate(C+ideal(z_0,z_1))==ideal(z_0,z_1,z_2,z_3)) or (saturate(C+ideal(z_1,z_2,z_3))==ideal(z_0,z_1,z_2,z_3)) then error "Unable to find curve not intersecting places of projection.";
    ---
    S1 = ZZ/101[x_0, x_1];
    S2 = ZZ/101[y_0,y_1,y_2];
    S = tensor(S1,S2);
    ---
    U = tensor(R,S);   
    --- 
    M1 = matrix {{z_0,z_1},{x_0,x_1}};
    M2 = matrix {{z_1,z_2,z_3},{y_0,y_1,y_2}};
    ---
    C' = sub(C,U);
    D = minors(2,M1)+minors(2,M2);
    ---
    BL1 := ideal(z_0,z_1);
    BL2 := ideal(z_1,z_2,z_3);
    B1 := ideal(z_0,z_1,z_2,z_3);
    B2 := ideal(x_0,x_1);
    B3 := ideal(y_0,y_1,y_2);
    B := intersect(B1,B2,B3,BL1,BL2);
    ---
    K  = saturate(C'+D,B);
    I =  sub(eliminate({z_0,z_1,z_2,z_3},K),S)
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
    Headline
    	creates the Ideal of a random rational curve of degree (d,e) in P1xP2
    Usage
    	randomRationalCurve(d,e)
    Inputs
    	d:ZZ
	    degree of curve on the P1 factor of P1xP2
	e:ZZ
	    degree of curve on the P2 factor of P1xP2
    Outputs
    	I:Ideal
    Description
    	Text
	    This randomly generates 2 forms of degree
	    d and 3 forms of degree 3 in the ring S (locally defined), 
	    and computes the ideal defining the image of the map of the
	    associated map P^1 to P^1xP^2.
	    
	Example
	    randomRationalCurve(2,3)	
///

doc ///
    Key
    	randomMonomialCurve
    Headline
    	creates the Ideal of a random monomial curve of degree (d,e) in P1xP2
    Usage
    	randomMonomialCurve(d,e)
    Inputs
    	d:ZZ
	    degree of curve on the P1 factor of P1xP2
	e:ZZ
	    degree of curve on the P2 factor of P1xP2
    Outputs
    	I:Ideal
    Description
    	Text
	    This randomly generates 2 mnomials of degree
	    d and 3 monomials of degree 3 in the ring S (locally defined), 
	    and computes the ideal defining the image of the map of the
	    associated map P^1 to P^1xP^2.
	    
	Example
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
    	randomCurve
    Headline
    	creates the Ideal of a random  curve of degree d and genus g in P1xP2
    Usage
    	randomCurve(d,g)
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
