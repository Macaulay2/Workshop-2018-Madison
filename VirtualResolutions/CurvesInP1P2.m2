restart
S = ZZ/101[x,y]


--------------------------------------------------------------------
--------------------------------------------------------------------
----- Input: (d,n)=(degree,ambient space dimension)
----- Output: The Betti table corresponding to a random degree d
----- monomial curve in P^n.
----- Description: This randomly generates (n+1) monomials of degree
----- d in the ring S (globally defined), computes the kernel of the
----- ring map associated to the corresponding map P^1---->P^n,
----- and then returns the Betti table of the kernel of this map.
--------------------------------------------------------------------
--------------------------------------------------------------------

randomRC = (d,n)->(
    F = apply(n+1,i->random(d,S));
    K = ker map(S,ZZ/101[z_0..z_n],F);
    minimalBetti K
    )

