

Packages:
Polyhedra


--inputs: list of vectors that span a d-dimensional subspace of RR^n
--output: linear equations that describe the hyperplanes
generateEquations = (L) -> (
    dimAmbient := #(L#0);
    dimSubspace := #L;
    R := RR[vars(0..dimSubspace-1)];
    equations := new List;
    variables := vars(R);
    V := variables;
    i := 0;
    for i from 0 to dimAmbient-1 do (
	g := 0;
    	j := 0;
	for j from 0 to dimSubspace-1 do (
	    g = g + V_(0,j) * L#j#i;
	    );
	equations = append(equations,g);
	);
    equations
    )

--input: vector v
--output: sign vector of v
sgn = (v) -> (
    signVector = apply(v, i -> (
	    sign := 0;
	    if i < 0 then  sign = -1 * i//i
	    else if i > 0 then sign = i//i;
	    sign
	    )
	);
    signVector
    )

M = {{1,1,0,-1},{0,2,1,-1}}
N = {{1,2,3,4,5},{0,2,4,6,8},{1,-1,1,-1,1}}
