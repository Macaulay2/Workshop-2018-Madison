doc ///
    Key
    	isVirtual
	(isVirtual,Ideal,Ideal,ChainComplex)
    Headline
    	checks if a chain complex is a virtual resolution of a given ideal
    Usage
    	isVirtual(I,irr,C)
    Inputs
    	I:Ideal
	    ideal that the virtual resolution should resolve
	irr:Ideal
	    irrelevant ideal of the ring
	C:ChainComplex
	    chain complex we want to check is a virtual resolution
    Outputs
    	:Boolean
	    true if C is a virtual resolution of I
	    false if not
    Description
    	Text
	    Given an ideal I, irrelevant ideal irr, and chain c isVirtual returns true if
	    C is a virtual resolution of I. If not, it returns false.

	    This is done by checking that the saturation of I and the saturation of the annihilator of HH_0(C)
	    agree. Then checking that the higher homology groups of C are supported on the irrelevant ideal.

	    If debugLevel is larger than zero, the homological degree where isVirtual fails is printed.
	Example
	    R = ZZ/101[x,y];
       	    isVirtual(ideal(x),ideal(x,y),res ideal(x))
///

doc ///
    Key
    	findGensUpToIrrelevance
	(findGensUpToIrrelevance,ZZ,Ideal,Ideal)
    Headline
        creates a list of subsets of the minimal generators that generate a given ideal up to saturation
    Usage
    	findGensUpToIrrelevance(n,I,irr)
    Inputs
    	I:Ideal
	    ideal we are intereseted in
	n:ZZ
	    size of subset of minimal generators of I that may generate I up to saturation with irr
	irr:Ideal
	    irrelvant ideal
    Outputs
    	:List
	    all subsets of size n of generators of I that generate I up to saturation with irr
    Description
    	Text
	    Given an ideal I, integer n, and irrelevant ideal irr, findGensUpToIrrelevance searches through
	    all n-subsets of the generators of I. If a subset generates the same irr-saturated ideal as the
	    irr-saturation of I then that subset is added to a list. After running through all subsets, the list
	    is outputted.
	Example
	    R = ZZ/101[x_0,x_1,x_2,x_3,x_4,Degrees=>{2:{1,0},3:{0,1}}];
	    B = intersect(ideal(x_0,x_1),ideal(x_2,x_3,x_4));
	    I = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3));
	    findGensUpToIrrelevance(2,I,B)
    Caveat
	    If no subset of generators generates the ideal up to saturation, then the empty list is outputted
///

doc ///
    Key
        [findGensUpToIrrelevance, GeneralElements]
    Headline
        what does this do?
    Description
      Text
            what do I do?
    SeeAlso
        findGensUpToIrrelevance
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

	    If no base ring is specified the computations are performed over F=ZZ/101
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

	    If no base ring is specified the computations are performed over F=ZZ/101.
	Example
	    randomMonomialCurve(2,3,QQ)
    Caveat
        This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.
///

doc ///
    Key
    	curveFromP3toP1P2
        (curveFromP3toP1P2,Ideal)
    Headline
    	creates the Ideal of a curve in P^1xP^2 from the ideal of a curve in P^3
    Usage
    	I=curveFromP3toP1P2(J)
    Inputs
    	J:Ideal
	    defining a curve in P^3.
    Outputs
    	I:Ideal
	    defining a curve in P^1xP^2.
    Description
    	Text
	    Given an ideal J defining a curve C in P^3 curveFromP3toP1P2 procudes the ideal of the curve in P^1xP^2 defined as follows: Consider the projections P^3->P^2 and P^3->P^1
	    from the point [0:0:0:1] and the line [0:0:s:t] respective. The product of these defines a map from P^3 to P^1xP^2. The curve produced by curveFromP3toP1P2 is the image of the input curve under this map.

	    This computation is done by first constructing the graph in P^3x(P^1xP^2) of the product of the two projections P^3->P^2 and P^3->P^1 defined above. This graph is then
	    intersected with Cx(P^1xP^3). A curve in P^1xP^2 is then obtained from this by saturating and then eliminating.

	    Note the curve in P^1xP^2 will have degree and genus equal to the degree and genus of C as long as C does not intersect the base locus of the projection. If the option
	    PreserveDegree => true curveFromP3toP1P2 will check whether C intersects the base locus, and if it does will return an error. If PreserveDegree => false this check is not
	    performed and the output curve in P^1xP^2 may have degree and genus different from C.
	Example
	    R = ZZ/101[z_0,z_1,z_2,z_3];
            J = ideal(z_0*z_2-z_1^2, z_1*z_3-z_2^2, z_0*z_3-z_1*z_2);
	    curveFromP3toP1P2(J)
    Caveat
        This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.
///

doc ///
    Key
        [curveFromP3toP1P2, PreserveDegree]
    Headline
        what does this do?
    Description
      Text
            what do I do?
    SeeAlso
        curveFromP3toP1P2
///

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
	    randomCurveP1P2(3,0)
	    randomCurveP1P2(3,0,QQ)
    Caveat
        This globaly defines a ring S=F[x_0,x_1,y_0,y_1,y_2] in which the resulting ideal is defined.
///

doc ///
    Key
        [randomCurveP1P2, Bound]
    Headline
        what does this do?
    Description
      Text
            what do I do?
    SeeAlso
        randomCurveP1P2
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
	    saturationZero returns true otherwise it returns false. This is done without computing the saturation of M by B.
	    Instead we check whether for each generator of B some power of it annihilates the module M. We do this
	    generator by generator.

	    If M is an ideal saturationZero checks whether the saturation comodule of M by B is zero.

///

doc ///
    Key
    	intersectionRes
	(intersectionRes, Ideal, Ideal, List)
    Headline
        Returns a potential virtual resolution of a zero-dimensional subscheme
    Usage
    	intersectionRes(I, irr, A)
    Inputs
	J:Ideal
        irr:Ideal
    	A:List
    Outputs
    	:ChainComplex
    Description
    	Text
            Given a saturated ideal J of a zero-dimensional subscheme, irrelevant ideal irr, and a vector A,
	    intersectionRes computes a free resolution of J intersected with A-th power of the irrelevant ideal.
	    See Theorem 5.1 of [BES].
    	Example
    	    debug needsPackage "TateOnProducts"
     	    "Following Example 5.7 of [BES]: 6 points in P1xP1xP2"
    	    N = {1,1,2}
    	    pts = 6
	    "Generate P1xP1xP2"
    	    (S, E) = productOfProjectiveSpaces N
	    "Find the irrelevant ideal"
    	    irr = intersect for n to #N-1 list (
    		ideal select(gens S, i -> (degree i)#n == 1)
    		)
    	    "Generate ideal of 6 general points in P1xP1xP2"
    	    I = saturate intersect for i to pts - 1 list (
  		print i;
  		P := sum for n to N#0 - 1 list ideal random({1,0,0}, S);
  		Q := sum for n to N#1 - 1 list ideal random({0,1,0}, S);
  		R := sum for n to N#2 - 1 list ideal random({0,0,1}, S);
  		P + Q + R
  		)
	    "Find the virtual resolution"
	    C = intersectionRes (I, irr, {2,1,0})
	    "Confirm that this is a virtual resolution"
    	    isVirtual(I, irr, C)
    Caveat
        The output is only a virtual resolution for 'sufficiently positive' vector A.
///
