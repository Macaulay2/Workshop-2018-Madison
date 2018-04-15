newPackage(
	"RichSubspaces",
    	Version => "0.1", 
    	Date => "April 15, 2018",
    	Authors => {{Name => "Brandon Boggess", 
		  Email => "bboggess@math.wisc.edu", 
		  HomePage => "http://www.math.wisc.edu/~bboggess/"},
	      {Name => "Justin Chen", 
		  Email => "jchen@math.berkeley.edu", 
		  HomePage => "http://www.math.berkeley.edu/~jchen/"},
	      {Name => "Wanlin Li", 
		  Email => "wanlin@math.wisc.edu", 
		  HomePage => "http://www.math.wisc.edu/~wanlin/"}},
	Headline => "computing the moduli space of m-rich k-planes of a zero dimensional scheme",
    	DebuggingMode => false
    	)


export {
    "richMatrix",
    "richSubspace"
}

richMatrix = method()
richMatrix (Ideal, ZZ, ZZ, List) := Ideal => (I, m, k, coords) -> (
    coords = sort coords;
    n := #gens ring I;
    if k > n then error(k | " should be less than " | n);
    if not (#coords == k and all(coords, i -> 0 <= i and i <= n-1)) then
        error("Expected " | k | " coordinates between 0 and " | (n-1));
    (x, p) := (symbol x, symbol p);
    R := (coefficientRing ring I)[apply(delete(coords, subsets(n, k)), s -> p_s)][x_0..x_(n-1)];
    S := R/((map(R,ring I,{x_0..x_(n-1)}))(I));
    B := basis S;
    A := matrix apply(k, i -> 
	apply(n, j -> (
		if member(j, coords) then ( if position(coords, c -> c == j) == i then 1_S else 0 )
		else p_(sort(append(coords_(delete(i, toList(0..<k))), j)))
    	)
    ));
    eqns := flatten entries(A * transpose matrix{gens S});
    matrix{flatten apply(eqns, e -> 
	    apply(flatten entries(matrix{{e}}*B), entry -> 
		last coefficients(entry, Monomials => flatten entries B)))}
)

richSubspace = method()
richSubspace (Ideal, ZZ, ZZ, List) := Ideal => (I, m, k, coords) -> richSubspace(I, m, richMatrix(I, m, k, coords))
richSubspace (Ideal, ZZ, Matrix) := Ideal => (I, m, M) -> (
    N := submatrixByDegrees(M, (min delete({0,0}, degrees target M), max degrees target M), (min delete({0,0}, degrees source M), max degrees source M));
    d := numcols basis comodule I;
    if d - m + 1 > min(numcols N, numrows N) then ideal 0_(ring M)
    else ideal mingens minors(d - m + 1, N)
)

TEST ///
k = ZZ/5
n = 4
R = k[x_0..x_(n-1)]
I = ideal(delete(x_3^2, flatten entries basis(2, R))) + ideal(x_3^3)
X4 = richSubspace(I, 4, 2, {0,1})
assert(toString X4 === "ideal(p_{1, 3},p_{0, 3})")
X5 = richSubspace(I,5,2,{0,1})
assert(X5 == ideal 1_(ring X5))
///

TEST /// -- Caution: IN PROGRESS!
R = ZZ/5[x_0..x_4]
I = ideal(basis (3,R))
numcols basis comodule I
M = richMatrix(I,7,2,{0,1})
richSubspace(I,7,2,{0,1})
///

end--


restart
loadPackage("RichSubspaces",Reload=>true)
check "RichSubspaces"

