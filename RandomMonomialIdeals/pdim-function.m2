isProjDimMaximum = method(TypicalValue=>Boolean);
isProjDimMaximum (MonomialIdeal) := M -> (
    n := #gens(ring M);
    G := apply(flatten entries mingens M, e -> flatten exponents e);
    subsetsG := subsets(G,n);
    for ss in subsetsG do(
	--check whether ss is a dominant set
	b := true;
	Dom := {};
	LCM := {};
	for i from 0 to n-1 do (
            iMax := max(apply(ss, e -> e_i));
            iDom := select(ss, g -> g_i == iMax);
            if #iDom>1 then(
		b = false;
		);
            Dom = append(Dom, flatten iDom);
	    LCM = append(LCM, iMax);
            );
        if #Dom>#(unique Dom) then(
	    b = false;
	    );
	--if it was dominant, check for a strong divisor
	if b then (
	    if (
	        all(G, g -> member(g,ss) or not g <= apply(LCM, a -> max(0, a-1)))
	        ) 
	    then (
	        return true;
	        );
	    );
	);
    false
    )

R = QQ[x,y,z,w];
M = monomialIdeal(x^3*y*z*w,x*y^3*z*w,x*y*z^3*w,x*y*z*w^3,x^4*y^4);
isProjDimMaximum M
M = monomialIdeal(x^3*y*z*w,x*y^3*z*w,x*y*z^3*w,x*y*z*w^3,x^2*y^2);
isProjDimMaximum M
