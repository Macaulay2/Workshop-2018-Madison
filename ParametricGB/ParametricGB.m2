newPackage(
        "ParametricGB",
        Version => "0.1", 
        Date => "April 16, 2018",
        Authors => {{Name => "Thomas Baath",
		     Email => "kb548@cornell.edu"},
		    {Name => "Dylan Peifer", 
                     Email => "djp282@cornell.edu", 
                     HomePage => "https://www.math.cornell.edu/~djp282"},
		    {Name => "David Swinarski",
		     Email => "dswinarski@fordham.edu"}},
        Headline => "Compute parametric Groebner bases",
        DebuggingMode => true
        )

export {"isConsistent", "minimalDicksonBasis", "comprehensiveGB"}

isConsistent = method()
isConsistent(List, List) := Boolean => (E, N) -> (
    -- E = a list of polynomials in k[U]
    -- N = a list of polynomials in k[U]
    -- returns if V(E) \ V(N) is empty (i.e. the constraints are inconsistent)

    if #E == 0 then return true;
    for f in N do (
	if f % (ideal E) == 0 then continue;
	if not isInRadical(f, ideal E) then return true;
	);
    false
    )

isInRadical = method()
isInRadical(RingElement, Ideal) := Boolean => (f, I) -> (
    -- f = a polynomial
    -- I = a polynomial ideal
    -- returns if f is in the radical of I

    y := local y;
    R := ring I;
    Ry := (coefficientRing R)(monoid [gens R, y]);
    phi := map(Ry, R, drop(first entries vars Ry, -1));
    y = (gens Ry)_-1;
    ideal(gens phi(I), 1 - phi(f)*y) == 1
    )
isInRadical(ZZ, Ideal) := Boolean => (f, I) -> (
    -- f = a polynomial (with no variable terms)
    -- I = a polynomial ideal
    -- returns if f is in the radical of I

    isInRadical(sub(f, ring I), I)
    )

minimalDicksonBasis = method()
minimalDicksonBasis(List) := List => (G) -> (
    -- G = a list of polynomials
    -- returns minimal Dickson basis (Def 4.3, page 133)

    J:=flatten entries mingens ideal(apply(G, g-> leadMonomial g));
    P:=partition(i -> leadMonomial(i),G);
    return apply(J, m -> first(P#m))
)

prod = (A,B) -> (
   if A=={} then return B;
   if B=={} then return A;     
   return unique flatten apply(A, a -> apply(B, b -> a*b))
)

comprehensiveGB = method(Options => {Verbosity => 0})
comprehensiveGB(List, List, List) := List => opts -> (E, N, F) -> (
    -- E = a list of polynomials
    -- N = a list of polynomials
    -- F = a list of polynomials

    -- Step 1
    if not isConsistent(E,N) then return {};
    if opts.Verbosity > 0 then (
	print concatenate("I am CGS on E=",toString(E),", N=",toString(N),", F=",toString(F)) << endl;
    );
    -- Step 2
    R:=ring(first F);
    y:=getSymbol "y";
    Ry:=R(monoid [y]);
    y=Ry_0;
    L1:=apply(F, f -> f*y);
    L2:=apply(E, e -> e*y-e);
    G0:= flatten entries gens gb ideal(join(L1,L2));
    -- Step 3
    G:=select(G0, g -> coefficient(y,g)!=0);
    if opts.Verbosity > 0 then (
    	print concatenate("G=",toString(G))<< endl;
    );
    G1st:=apply(G, g-> coefficient(y,g));
    if opts.Verbosity > 0 then (
    	print concatenate("G1st=",toString(G1st))<< endl;
    );
    -- Step 4
    if member(1_Ry,G1st) then (
        return {E,N,{first select(G, g-> coefficient(y,g)==1_Ry)}}	
    );
    -- Step 5
    Gry:=select(G, g-> first coefficients(coefficient(y,g)) == matrix {{1_R}});
    if opts.Verbosity > 0 then (
    	print concatenate("Gry=",toString(Gry)) << endl;
    );
    Gr:=apply(Gry, g -> lift(coefficient(y,g),coefficientRing(R)));
    Gr = unique join(Gr,E);
    if opts.Verbosity > 0 then (
    	print concatenate("Gr=",toString(Gr)) << endl;
    );
    -- Step 6
    CGS:={};
    if isConsistent(E,prod(Gr,N)) then (
	CGS = {{flatten entries mingens ideal(E),prod(Gr,N),Gry}}	
    );
    if opts.Verbosity > 0 then (
    	print concatenate("CGS at end of Step 6 = ",toString CGS) << endl;
    );
    -- Step 7
    if not isConsistent(Gr,N) then return CGS;
    -- Step 8
    Gm:=minimalDicksonBasis(select(G1st, g-> not member(g,apply(Gr, h -> h*1_R))));
    if opts.Verbosity > 0 then (
    	print concatenate("Gm=",toString(Gm)) << endl;
    );
    Gmy:=select(G, g-> not member(g,Gry));
    Gmy=select(Gmy, g-> member(coefficient(y,g),Gm)); 
    if opts.Verbosity > 0 then (
    	print concatenate("Gmy=",toString(Gmy)) << endl;
    );
    -- Step 9
    H:=unique apply(Gm, g-> leadCoefficient(g));
    if opts.Verbosity > 0 then (
    	print concatenate("H=",toString(H)) << endl;
    );
    h:=0;
    if H!={} then h=lcm(H) else h=1;
    if isConsistent(Gr,prod(N,{h})) then (
        CGS = append(CGS,{flatten entries mingens ideal(Gr),prod(N,{h}),Gmy});	
    );
    if opts.Verbosity > 0 then (
    	print concatenate("CGS at end of Step 9 = ",toString CGS) << endl;
    );
    newE:={};
    newN:={};
    newF:={};
    L:=for i from 0 to #H-1 list (
	newE=flatten entries mingens ideal(append(Gr,H_i));
	newN=prod(N,{product apply(i-1, j -> H_j)});
	newF=select(G, g -> not member(g,Gry));
	newF = apply(newF, g -> coefficient(y,g)+coefficient(1_Ry,g));
	if opts.Verbosity > 0 then (
	    print concatenate("i=",toString(i),",{E,N,F}=",toString {newE,newN,newF}) << endl;
        );
	comprehensiveGB(newE,newN,newF)	
    );
    return unique join(CGS,flatten L)
)

beginDocumentation()

end--

doc ///
Key
  ParametricGB
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

-- Example 1
-- See KSW 2013 section 5 p. 138
restart
needsPackage "ParametricGB"
R = QQ[a,b,c][x1,x2]
E = {}
N = {1_(coefficientRing(R))}
F = {a*x1 - b, b*x2 - a, c*x1^2 - x2, c*x2^2 - x1}
cgb = comprehensiveGB(E, N, F)
#cgb
checkedcgb = ///{{{}, {b*c^2-b, a*c^2-a, b^3*c-a^3, a^3*c-b^3, a^6-b^6}, {(b*c^2-b)*y, (a*c^2-a)*y, (b^3*c-a^3)*y, (a^3*c-b^3)*y, (a^6-b^6)*y}}, {{b*c^2-b, a*c^2-a, b^3*c-a^3, a^3*c-b^3, a^6-b^6}, {b}, {(b*x2-a)*y, (b*x1-a*c*x2)*y}}, {{b, a}, {c}, {(c*x2^2-x1)*y, (c*x1^2-x2)*y}}, {{c, b, a}, {1}, {x2*y-c*x1^2, x1*y-c*x2^2}}}///;
assert(toString(cgb) === checkedcgb)
cgb_0
cgb_1
cgb_2
cgb_3

-- Example 2
-- Family containing the twisted cubic
restart
needsPackage "ParametricGB"
R=QQ[c_1,c_2][x_0..x_3]
E={}
N={1_(coefficientRing(R))}
F={c_1*x_0*x_2-c_2*x_1^2, c_1*x_0*x_3-c_2*x_1*x_2, c_1*x_1*x_3-c_2*x_2^2}
cgs= comprehensiveGB(E, N, F)
#cgs
cgs_0   -- This is stupid
cgs_1   -- The generic fiber
cgs_2   -- c_2 = 0, c_1 \neq 0
cgs_3   -- c_1 = c_2 = 0
cgs_4   -- c_1(c_1-c_2) = 0, c_2 \neq 0
cgs_5   -- 

R=QQ[c_1,c_2][x_0..x_3]
isConsistent({c_1},{c_2})
isConsistent({c_1},{c_1^2*c_2})

G={c_1*x_1*x_2-x_3^2,x_1*x_2^2+x_3^3,x_1^2+x_2^2+x_3^2}
minimalDicksonBasis(G)
