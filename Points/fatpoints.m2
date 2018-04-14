--this function computes the defining ideal of fat points
--the coordinates are the columns of M
--the multiplicities are in the list mu
--R is the coordinate ring of the ambient affine space
fatPoints = (M,mu,R) -> (
    --list of ideals of individual points
    L := for p in entries transpose M list ideal((gens R)-p);
    L = apply(L,mu,(I,m)->I^m);
    return intersect L;
    )