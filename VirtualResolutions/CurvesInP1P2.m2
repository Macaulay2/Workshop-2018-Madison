restart



--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,e)=(degree,degree)
----- Output: The ideal of a random rational curve in P1xP2 of degree (d,e).
----- Description: This randomly generates 2 monomials of degree
----- d and 3 monomials of degree 3 in the ring S (locally defined), 
----- and computes the kernel of the ring map associated to the corresponding map
----- P^1---->P^n,
--------------------------------------------------------------------
--------------------------------------------------------------------

randomRC = (d,e)->(
    S := ZZ/101[s,t]
    R1 := ZZ/101[x_0, x_1];
    R2 := ZZ/101[y_0,y_1,y_2];
    R = tensor(R1,R2)    
    F1 := apply(2,i->random(d,S));
    F2 := apply(3,i->random(e,S));
    F := F1|F2;
    K = ker map(S,R,F)
    )

