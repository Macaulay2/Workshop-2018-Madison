--Implements the affine Buchberger-Möller algorithm
--R is a polynomial ring with coefficients in a field K
--phi:R->K^s is a linear map whose kernel I is an ideal
--returns a Gröbner basis of I
--The implementation follows Kreuzer-Robbiano,
--Computational Commutative Algebra 2, Thm. 6.3.10
--but phi generalizes evaluation at points for other use cases
affineBM = (R,phi) -> (
    G := {}; --holds Gröbner basis
    inG := {}; --holds generators of initial ideal
    O := {}; --holds standard monomials (basis of quotient)
    S := {}; --holds polynomials for intermediate steps
    L := {1_R}; --start with 1
    K := coefficientRing R;
    s := #(phi 1_R); --dimension of codomain of phi
    M := map(K^0,K^s,0); --an s by 0 matrix over K
    --we introduce a hash table H to hold positions of
    --pivots of M, keys are columns, values are rows
    H := new MutableHashTable;
    while L != {} do (
	t := min L;
	L = drop(L,1);
	w := map(K^1,K^s,{phi t});
	--reduce w against rows of matrix M
	(v,a,q) := reduceVector(w,M,H);
	g := dotProductLists(a,S);
	--if v==0 we have a GB element
	if v == 0 then (
	    G = G | {t-g};
	    inG = inG | {t};
	    --remove redundant elements
	    L = select(L,u->u % t != 0);
	    )
	--if v!=0 we don't have a GB element, we modify some data
	else (
	    --add a row to M and record new pivot position
	    H#q = numRows M;
	    M = M || v;
	    --we found a polynomial not evaluating to zero
	    --its leading coefficient becomes a standard monomial
	    S = S | {t-g};
	    O = O | {t};
	    --add new monomials to list
	    U := apply(sort gens R,u->u*t);
	    J := promote(ideal(L|inG),R);
	    --remove redundant elements
	    L = sort(L | select(U,u->u % J != 0));
	    );
	);
    return (G,inG,O);
    )

--returns dot product of two lists with elements in a ring
dotProductLists = (u,v) -> sum(apply(u,v,(i,j)->i*j))

--this function reduces a row vector w againts the rows
--of a matrix M
--H is a mutable hash table recording the positions of the
--pivots of M
--row reduction is done in the naive way (think linear algebra 1)
--the function returns the reduced vector w,
--a list of coefficients used in front of rows of M to reduce,
--and if w!=0, the position of first non zero entry of w
--(which is used later as a new pivot)
reduceVector = (w,M,H) -> (
    p := position(flatten entries w, u -> u != 0);
    K := ring M;
    a := new MutableMatrix from map(K^1,K^(numRows M),0);
    while p =!= null do (
	if H#?p then (
	    c := (w_(0,p))/(M_(H#p,p));
	    w = w-c*M^{H#p};
	    a_(0,H#p) = c;
	    p = position(flatten entries w, u -> u != 0);
	    )
	else break;
	);
    return (w,flatten entries a,p);
    )

evaluationMap = (L,R) ->(    --R is a polynomial ring, L is list of points
    K := coefficientRing R;  --P is a list of evaluation maps
    P := for p in L list(    --phi applies a polynomial f to the list of evalution maps P
	map(K,R,p)    	     --and returns phi
	);
    phi := f->apply(P, u->u(f));
    return phi;
    )

evaluateDerivatives = (X,mu,f) -> (
    R := ring f;
    K := coefficientRing R;
    L := for i to #X-1 list (
	phi := map(K,R,X_i);
	for m in flatten entries basis(0,mu_i-1,R) list phi(diff(m,f))
	);
    return flatten L;
    )

createEvaluationMap = (X,mu,R) -> (
    f -> evaluateDerivatives(X,mu,f)
    )

affinePoints = (X,R) -> (
    
    )

end

--some sample computations for fat points
--and comparison with the intersection method

R=QQ[x,y]
X={{0,0},{0,-1},{1,0},{1,1},{-1,1}}
mu={6,7,8,9,10}
load "bm.m2"
phi=createEvaluationMap(X,mu,R)
time (G,inG,O)=affineBM(R,phi);
I=ideal G;
time J=intersect(apply(X,mu,(p,m)->(ideal((gens R)-p))^m));
I==J

restart
R=QQ[x_1..x_5]
X=entries random(QQ^10,QQ^5);
mu={2,3,4,2,3,4,2,3,4,1};
load "bm.m2"
phi=createEvaluationMap(X,mu,R)
time (G,inG,O)=affineBM(R,phi);
g=forceGB matrix{G};
I=ideal G;
time J=intersect(apply(X,mu,(p,m)->(ideal((gens R)-p))^m));
I==J

