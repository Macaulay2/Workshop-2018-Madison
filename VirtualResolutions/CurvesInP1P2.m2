restart



--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,degree)
----- Output: The ideal of a random rational curve in P1xP2 of degree (d,e).
----- Description: This randomly generates 2 monomials of degree
----- d and 3 monomials of degree 3 in the ring S (locally defined), 
----- and computes the kernel of the ring map associated to the corresponding map
----- P^1---->P^1xP^2,
--------------------------------------------------------------------
--------------------------------------------------------------------

randomRationalCurve = (d,e)->(
    R := ZZ/101[s,t];
    ---
    S1 := ZZ/101[x_0, x_1];
    S2 := ZZ/101[y_0,y_1,y_2];
    S = tensor(S1,S2);
    ---
    U = tensor(R,S);   
    --- 
    M1 := matrix {apply(2,i->random({d,0,0},U)),{x_0,x_1}};
    M2 := matrix {apply(3,i->random({e,0,0},U)),{y_0,y_1,y_2}};
    ---
    J := minors(2,M1)+minors(2,M2);
    J' := saturate(J,ideal(s,t),MinimalGenerators=>false);
    I = sub(eliminate({s,t},J'),S)
    )

randomMonomialCurve = (d,e)->(
    R := ZZ/101[s,t];
    ---
    S1 := ZZ/101[x_0, x_1];
    S2 := ZZ/101[y_0,y_1,y_2];
    S = tensor(S1,S2);
    ---
    U = tensor(R,S);  
    ---
    B = drop(drop(flatten entries basis({e,0,0},U),1),-1);
    f = (random(B))#0;
    ---
    M1 := matrix {{s^d,t^d},{x_0,x_1}};
    M2 := matrix {{s^e,t^e,f},{y_0,y_1,y_2}};
    ---
    J := minors(2,M1)+minors(2,M2);
    J' := saturate(J,ideal(s,t),MinimalGenerators=>false);
    I = sub(eliminate({s,t},J'),S)
    )

randomCurve = (d,g) ->(
    R = ZZ/101[z_0,z_1,z_2,z_3];
    R1 := ZZ/101[x_0, x_1];
    R2 := ZZ/101[y_0,y_1,y_2];
    map(R,R1,{z_0,z_1})
    map(R,R2,{z_0,z_1,z_2})
    )