
restart
loadPackage "NormalToricVarieties"

alphaGens = (alpha,P,S)->(
    basisAlpha := basis(alpha,S);
    psi := map(ZZ,S,P);
    kernelGens := gens ker psi basisAlpha;
    flatten entries( basisAlpha*kernelGens)    
    )

--------------------------------------------------------------------------------------------------
--pointIdeal takes as input a ring S, a list of multidegrees alphalist, and a point in products of 
--pojective spaces P.  This function is primarily used as a subfunction pntIdeal to compute the 
--ideal that vanishes at a single point P.
--------------------------------------------------------------------------------------------------
pointIdeal = (S,alphalist,P)->(
  ideal(flatten apply(alphalist,l->alphaGens(l,P,S))))

--------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------------------------
pntsIdeal = method(Options=>{MinGens=>false,dmg=>false})
pntsIdeal(Matrix,List) := opts -> (M,plist) -> (
   --Computes a list of each projective space we will use to find the cartesian product of our
   --projective spaces
    projlist:=plist/projectiveSpace;
   --n is the length of this list and is needed to find the number of standard basis vectors
   --used to create alphalist, this is used in the pointIdeal function
    n:=length(projlist);   
   --Compute X which is the product of the projective spaces from projlist and then create the 
   --ring S for X
    X:=projlist#0;   
    for i from 1 to n-1 do X=X**projlist#i;  
    S:=ring X;
   --Make a list of the rows of M
    e:=entries M;
   --Define alpha list to be the list of standard basis vectors of length n
    alphalist:=entries id_(ZZ^n);
   --Intersect the pointIdeals for each point in the list of points e
   intIdeal:= e/pointIdeal_(S,alphalist)//intersect;
   if opts.MinGens then return mingens intIdeal;
   if opts.dmg then return degrees intIdeal;
   intIdeal)


-------------------------------------------------------------------------------------------------
--Here is a test
-------------------------------------------------------------------------------------------------

pdims={2,3,4,5}
M=random(ZZ^3,ZZ^18)
pntsIdeal(M,pdims)



