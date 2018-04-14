-- Program Kapur, Sun, Wang 2013
-- Algorithm CGSMainPoly, page 137

-- Kapur, Sun, Wang 2010 Definition 2.3
-- See also Section 5, Paragraph 1
isConsistent = (E,N) -> (
    if E == {} then return true;
    I:=radical ideal(E);
    for n in N do (
	if (n%I) != 0 then return true
    );
    return false
)

{* Test
R=QQ[c_1,c_2][x_0..x_3]
isConsistent({c_1},{c_2})
isConsistent({c_1},{c_1^2*c_2})
*}


hDividesT = (h,t) -> (
    e1 := first exponents(h);
    e2 := first exponents(t);
    for i from 0 to #e1-1 do (
	if e1_i > e2_i then return false
    );
    return true
);

{* Test
hDividesT(x_1*x_2-x_3^2,x_1*x_2^2+x_3^3)
*}

-- Minimal Dickson Basis 
-- Def. 4.3, page 133
MDBasis = (G) -> (
    J:=flatten entries mingens ideal(apply(G, g-> leadMonomial g));
    P:=partition(i -> leadMonomial(i),G);
    return apply(J, m -> first(P#m))
)

{* Test
G={c_1*x_1*x_2-x_3^2,x_1*x_2^2+x_3^3,x_1^2+x_2^2+x_3^2}
MDBasis(G)
*}

prod = (A,B) -> (
   return unique flatten apply(A, a -> apply(B, b -> a*b))
)

CGSMainPoly = (E,N,F) -> (
    -- Step 1
    if not isConsistent(E,N) then return {};
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
    G1st:=apply(G, g-> coefficient(y,g));
    -- Step 4
    if member(1_Ry,G1st) then (
        return {E,N,{first select(G, g-> coefficient(y,g)==1_Ry)}}	
    );
    -- Step 5
    Gry:=select(G, g-> first coefficients(coefficient(y,g)) == matrix {{1_R}});
    Gr:=apply(Gry, g -> lift(coefficient(y,g),coefficientRing(R)));
    Gr = unique join(Gr,E);
    -- Step 6
    CGS:={};
    if isConsistent(E,prod(Gr,N)) then (
	CGS = {{E,prod(Gr,N),Gry}}	
    );
    -- Step 7
    if not isConsistent(Gr,N) then return CGS;
    -- Step 8
    Gm:=MDBasis(select(G1st, g-> not member(g,apply(Gr, h -> h*1_R))));
    Gmy:=select(G, g-> not member(g,Gry));
    Gmy=select(Gmy, g-> member(coefficient(y,g),Gm)); 
    -- Step 9
    H:=unique apply(Gm, g-> leadCoefficient(g));
    h:=lcm(H);
    if isConsistent(Gr,prod(N,{h})) then (
        CGS = append(CGS,{Gr,prod(N,{h}),Gmy});	
    );
    newE:={};
    newN:={};
    newF:={};
    L:=for i from 0 to #H-1 list (
	newE=append(Gr,H_i);
	newN=prod(N,product apply(i-1, j -> H_j));
	newF=select(Gr, g -> not member(g,Gry));
	newF = apply(newF, g -> coefficient(y,g)+coefficient(1_Ry,g));
        CGSMainPoly(newE,newN,newF)	
    );
    return prepend(CGS,L)
)


end 

restart

load "ParametricGB.m2";


R=QQ[c_1,c_2][x_0..x_3]
E={c_1}
N={c_2}
F={c_1*x_1^2-c_2*x_0*x_2,c_1*x_1*x_2-c_2*x_0*x_3,c_1*x_2^2-c_2*x_1*x_3}
CGSMainPoly(E,N,F)

R=QQ[c_1,c_2][x_0..x_3]
E={}
N={}
F={c_1*x_1^2-c_2*x_0*x_2,c_1*x_1*x_2-c_2*x_0*x_3,c_1*x_2^2-c_2*x_1*x_3}
CGSMainPoly(E,N,F)
