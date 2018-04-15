--Implements the affine Buchberger-Möller algorithm
--R is a polynomial ring with coefficients in a field K
--phi:R->K^s is a linear map whose kernel I is an ideal
--returns a Gröbner basis of I
--implementation follows Kreuzer-Robbiano,
--Computational Commutative Algebra 2
--but phi generalizes evaluation at points
--CURRENTLY THIS IS JUST A SKELETON
affineBM = (R,phi,s) -> (
    G := {}; --holds Gröbner basis
    inG := {}; --holds gens of initial ideal
    O := {}; --holds standard monomials (basis of quotient)
    S := {}; --holds polynomials for intermediate steps
    L := {1_R}; --start with 1
    K := coefficientRing R;
    M := map(K^s,K^0,0); --an s by 0 matrix over K
    while L != {} do (
	t := min L;
	L = drop(1,L);
	(v,a) := reduceVector(phi(t),M);
	if v == 0 then (
	    G = G | {t-a*s};
	    inG = inG | {t};
	    L = select(L,u->u % t != 0);
	    )
	else (
	    M = M | v;
	    S = S | {t-a*s};
	    O = O | {t};
	    U := apply(gens R,u->u*t);
	    L = L | select(U,u->u % ideal(L|inG) != 0);
	    );
	);
    return (G,inG,O);
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
	for m in flatten entries basis(0,mu_i,R) list phi(diff(m,f))
	);
    return flatten L;
    )

createEvaluationMap = (X,mu,R) -> (
    f -> evaluateDerivatives(X,mu,f)
    )
