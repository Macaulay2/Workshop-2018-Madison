newPackage(
	"Sumset",
    	Version => "0.1", 
    	Date => "April 14, 2018",
    	Authors => {{Name => "Brandon Boggess", 
		  Email => "bboggess@math.wisc.edu", 
		  HomePage => "http://www.math.wisc.edu/~bboggess/"},
	      {Name => "Justin Chen", 
		  Email => "jchen@math.berkeley.edu", 
		  HomePage => "http://www.math.berkeley.edu/~jchen/"},
	      {Name => "Wanlin Li", 
		  Email => "wanlin@math.wisc.edu", 
		  HomePage => "http://www.math.wisc.edu/~wanlin/"}},
	Headline => "computing sumsets",
    	DebuggingMode => false
    	)


export {
    "sumset",
    "idealFromPt",
    "idealFromPts"
}

sumset = method()
sumset (Ideal, Ideal) := Ideal => (I1, I2) -> (
    (R1, R2) := (I1, I2)/ring;
    k := coefficientRing R1;
    (t,u,v) := (symbol t, symbol u, symbol v);
    S := k[t_1..t_(#gens R1)];
    R := k[u_1..u_(#gens R1),v_1..v_(#gens R2)];
    R1vars := take(gens R, #gens R1);
    R2vars := take(gens R, -#gens R2);
    I := (map(R,R1,R1vars))(I1) + (map(R,R2,R2vars))(I2);
    ker map(R/I, S, R1vars + R2vars)
)        
	
idealFromPt = method()
idealFromPt (List, Ring) := Ideal => (L, R) -> (
    if not #L == #gens R then error "Expected number of coordinates to equal dimension of the ring";
    ideal apply(#L, i -> (gens R)#i - sub(L#i,R))
)

idealFromPts = method()
idealFromPts (List, Ring) := Ideal => (L, R) -> intersect apply(L, l -> idealFromPt(l, R))

doc ///
    Key
    	Sumset
    Headline
    	a package for computing sumsets
    Description
    	Text
    	    Given two zero-dimensional subschemes of affine n-space, 
	    the sumset is the image of the addition map. 
	Example
	    k = ZZ/101
	    R = k[x1,x2,x3,x4]
	    I1 = idealFromPts({{0,0,0,0},{1,2,4,8},{1,1,1,1}},R)
    	    I2 = idealFromPts({{1,-1,1,-1},{1,3,9,27},{1,0,0,0}},R)
	    S = sumset(I1,I2)
	    pts = minimalPrimes S
	    intersect pts == S
///

doc ///
    Key
        sumset
        (sumset,Ideal,Ideal)
    Headline
        Computes the ideal defining the sumset of two zero dimensional
        subschemes of affine sapce
    Usage
        sumset(I1, I2)
    Inputs
        I1:Ideal
            in a polynomial ring defining a zero dimensional
            closed subscheme of affine space
        I2:Ideal
            defining a second zero dimensional subscheme
    Outputs:
        :Ideal
    Description
///

doc ///
    Key
    	idealFromPt
    Headline
    	produce an ideal from a point
    Usage
        idealFromPt(P,R)
    Inputs
    	P:List
	    of coordinates of a point
	R:Ring
	    which the ideal is contained in
    Outputs
    	:Ideal
	    in the ring R
    Description
    	Text
    	    Given a point via its list of coordinates,
	    this method produces the ideal of functions vanishing at that point. 
	Example
	    k = ZZ/101
	    R = k[x,y]
	    P = {1,1}
	    idealFromPt(P)
    SeeAlso
    	idealFromPts
///

doc ///
    Key
        idealFromPts
        (idealFromPts,List,Ring)
    Headline
        Computes the vanishing ideal of a finite set of points in affine space
        over a given ring
    Usage
        IdealFromPoints(L, R)
    Inputs
        L:List
            of coordinates of points in affine space
        R:Ring
            which coordinates are contained in
    Outputs
        :Ideal
            in polynomial ring over R
    SeeAlso
        idealFromPt
///

TEST ///
k = ZZ/101
R = k[a,b]
I = idealFromPts({{1,0},{0,1}},R)
assert(I == ideal(a*b, a+b-1))
T = k[t_1,t_2]
J = intersect(ideal(t_1-1,t_2-2),ideal(t_1-2,t_2-1))
S = sumset(I, idealFromPt({1,1},R))
assert((map(T,ring S,gens T))(S) == J)
///

TEST ///
R = QQ[x,y]
I = ideal(x^2,y^2,random(1,R))
J = ideal((x-1)^2,y^3)
S = sumset(I,J)
assert(#minimalPrimes S == 1)
///

TEST ///
k = ZZ/5
R = k[x,y]
I1 = ideal(y^2 - x^3 + x, x)
I2 = ideal(y^2 - x^3 + x, x - 2)
S = sumset(I1,I2)
minimalPrimes S
///

	
end--

restart
loadPackage("Sumset",Reload=>true)
check "Sumset"
