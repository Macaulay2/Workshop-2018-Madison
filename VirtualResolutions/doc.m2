doc ///
  Key
    VirtualResolutions
  Headline
    Compute virtual resolutions
  Description
    Text
     While graded minimal free resolutions work well for studying quasicoherent 
     sheaves over projective space, over a product of projective spaces or, more generally, 
     over smooth projective toric varieties, graded minimal free resolutions over the Cox ring 
     seem too restricted by algebraic structure that is unimportant geometrically. By allowing 
     a limited amount of homology, virtual resolutions offer a more flexible alternative for 
     studying toric subvarieties when compared to minimal graded free resolutions.
     
     Introduced by Berkesch, Erman, and Smith in {\em Virtual resolutions for a product of projective spaces} 
     (see arXiv:1703.07631) if $X$ is a smooth toric variety, $S$ the Cox ring of $X$
     graded by the Picard group of $X$, and $B\subset S$ the irrelevant ideal of $X$ then
     a virtual resolution of a graded $S$-module $M$ is a complex of graded free $S$-modules, which
     sheafifies to a resolution of the associated sheaf.
 
     The goal of this package is provide tools for constructing and working with 
     virtual resolutions for products of projective spaces. In particular, it implements
     a number of the methods for constructing virtual resolutions for products of projective
     spaces introduced by Berkesch, Erman, and Smith. The package also contains a number of
     methods for constucting curves in $\mathbb{P}^1\times\mathbb{P}^2$ as these are
     a natural source for interesting virtual resolutions. 
       
     As a running example consider the three points $([1:1],[1:4])$, $([1:2],[1:5])$, and $([1:3],[1:6])$
     in $\mathbb{P}^1 \times \mathbb{P}^1$. 
	     
    Example
     X = toricProjectiveSpace(1)**toricProjectiveSpace(1);
     S = ring X; 
     B = ideal X;
     J = saturate(intersect(
         ideal(x_1 - x_0, x_3 - 4*x_2),
         ideal(x_1 - 2*x_0, x_3 - 5*x_2),
         ideal(x_1 - 3*x_0, x_3 - 6*x_2)), B);
     minres = res J;
     multigraded betti minres 
    Text
     As dscribed in Theorem 4.1 of Berkesch, Erman, and Smith's 
     paper one may construct a virutal resolution of a module from its graded minimal free resolution and
     an element of the multigraded Castelnuovo-Mumford regularity of the module. (See Maclagan and Smith's paper 
     {\em Multigraded Castelnuovo-Mumford regularity} for the definition of multigraded regularity.) 
     Building on the TateOnProducts package this package contains a function allowing one
     too compute the minimal elements of the multigraded Castelnuovo-Mumford regularity of a $B$-saturated module.
     
     Continuing the example from above, we see that $(3,1)$ is an element of the multigraded
     regularity of $J$. From this we can compute a virtual resolution of $S/I$.
    Example
     multigradedRegularity(X, module J)
     vres = multiWinnow(X,minres,{{3,1}}) 
     multigraded betti vres
    Text
     Notice that this virtual resolution of $S/J$ is much shorter and thinner than the graded minimal
     free resolution of $S/J$. This is a common theme, i.e. virtual resolutions tend to be much
     shorter and less wide than graded minimal free resolutions over the Cox ring.
     
     In addition to the functions highlighted above the VirtualResolutions package contains
     a number of other tools for constructing and studying virutal resolutions. In particular,
     there are functions to construct virtual resolutions for zero dimensionsal subschemes, to
     check whether a complex is a virtual resolution, and to consturct curves in $\mathbb{P}^1\times\mathbb{P}^2$.
///

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
        combines generators of same degree into a general linear combination
    Description
        Text
            If GeneralElements is set to true, findGensUpToIrrelevance will replace the given ideal with
	    an ideal where all generators of the same degree are combined into a general linear combination 
	    of those generators, then run findGensUpToIrrelevance on the new ideal. The first element in the
	    output will be the new ideal, followed by the subsets of generators that will generate the original
	    ideal up to saturation.
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
        Determines if curve is disjoint from base locuses
    Description
      Text
            When set to true curveFromP3toP1P2 will check whether or not the given curve
	    in P^3 intersects the base locus of the projections maps used in this function.
	    If this option is set to true and the given curve does intersect the base locus
	    an error is returned. 
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
        Limit number of attempts for randomCurveP1P2
    Description
      Text
           When randomCurveP1P2 generates a random curve in P^3 using the SpaceCurves package it is possible the resulting
	   curve will intersect the base locuses of the projections used to construct the curve in P^1 x P^2. If the curve
	   does intersect the base locuses it will generate a new random curve in P^3. The option Bound limits the number
	   of attempts to find a curve disjoing from the base locuses before quiting. By defualt Bound is set to 1000.
    SeeAlso
        randomCurveP1P2
///

doc ///
    Key
    	intersectionRes
	(intersectionRes, Ideal, Ideal, List)
    Headline
        Returns a virtual resolution of a zero-dimensional subscheme
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
        The output is only a virtual resolution for inputs that are zero-dimensional subschemes.
///

-*
doc ///
    Key
        multiWinnow
        (multiWinnow, Ring,               ChainComplex, List)
        (multiWinnow, NormalToricVariety, ChainComplex, List)
    Headline
        Creates a virtual resolution from a free resolution by keeping only summands of specified degrees.
    Usage
    	multiWinnow(R,C,L)
	multiWinnow(X,C,L)
    Inputs
    	R:Ring
	X:NormalToricVariety
	C:ChainComplex
	L:List  	
    Outputs
    	:ChainComplex
    Description
        Text
          Given a ring and its free resolution, keeps only the summands in resolution of specified degrees.
	  If the specified degrees are in the multigraded regularity, then the output is a virtual resolution. 
	  See Theorem 4.1 of [BES] for further details.
	  If the list alphas contains only one element, the output will be summands generated in degree less than or equal to alpha.
        Example
	"Generate P1xP1"
	X = toricProjectiveSpace(1)**toricProjectiveSpace(1);
	S = ring X; B = ideal X;
	"Generate the ideal of 3 general points in P1xP1"
	J = saturate(intersect(
    		ideal(x_1 - 1*x_0, x_3 - 4*x_2),
    		ideal(x_1 - 2*x_0, x_3 - 5*x_2),
    		ideal(x_1 - 3*x_0, x_3 - 6*x_2)),
     	    B) 
	"Compute its minimal free resolution and a virtual resolution"
  	minres = res J;
  	vres = multiWinnow(X,minres,{{3,1}}) --(3,1) = (2,0) + (1,1)
	"Check that vres is indeed virtual"
	isVirtual(J,B,vres)
///
*-