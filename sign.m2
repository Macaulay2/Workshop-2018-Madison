{*
Packages used: Polyhedra

Methods:

sgn
Description: Applies the sign function to each component of a vector
Input: v, a column vector (as a matrix or element of a free module)
Output: signVector, a list

signMatrices: Lists all diagonal nxn matrices with entries in {0,1,-1}
Input: n, an integer
Output: listMatrices, a list of matrices

signSpace: Computes all non-zero sign vectors of a linear subspace given 
by the span of the columns of a matrix M
Input: M, a matrix
Output: signs, a list of sign vectors (as lists)

Example:
M = transpose matrix {{{1,1,0,-1},{0,2,1,-1}}
transpose matrix signSpace(M) = 
| -1 -1 -1 -1 -1 -1 -1 1  1  0  1  0  1  1  1  1  |
| -1 -1 -1 1  1  0  1  -1 -1 -1 0  1  1  1  -1 1  |
| -1 0  1  1  1  1  1  -1 -1 -1 -1 1  -1 0  -1 1  |
| 1  1  1  -1 0  1  1  -1 0  1  -1 -1 -1 -1 1  -1 |
*}


sgn = (v) -> (
    V := matrix v;
    signVector := new List;
    for i from 0 to numRows(V) - 1 do (
	if V_(i,0) > 0 then signVector = append(signVector, 1)
	else if V_(i,0) < 0 then signVector = append(signVector, -1)
	else signVector = append(signVector,0)
	);
    signVector
    )


signMatrices = (n) -> (
    minus1 := toList(1..n);
    minus1 = apply(minus1, i -> -1);
    plus1 := apply(minus1, i -> 1);
    listMatrices := toList(minus1..plus1);
    listMatrices  = apply(listMatrices, v -> diagonalMatrix v );
    listMatrices
    )


signSpace = (M) -> (
    signVectors := new List;
    listCones := new List;
    listRays := new List;
    interiorVectors := new List;
    listSignMatrices := signMatrices(numRows M);
    listCones = apply(listSignMatrices, v -> (v * M));
    listCones = apply(listCones, A -> coneFromHData(A));
    listCones = unique(listCones);
    listRays = apply(listCones, i -> rays(i));
    listRays = apply(listRays, i -> if zero i then 0 else i);
    listRays = delete(0, listRays);
    interiorVectors = apply(listRays, C -> (
	    S := C_0;
	    for j from 1 to numColumns C - 1 do (
	    	S = S + C_j);
	    S
	    )
	);
    signVectors = apply(interiorVectors, v -> sgn(M * v));
    signVectors = unique(signVectors);
    signVectors
    )
 

M = transpose matrix {{1/1,1,0,-1},{0,2,1,-1}}
M' = transpose matrix {{1,1,0,-1},{0,2,1,-1}}
N = transpose matrix {{1/1,2,3,4,5},{0,2,4,6,8},{1,-1,1,-1,1}}
P = matrix {{1,2},{3,4}}
L = matrix {{0,0},{0,0},{0,0},{0,0},{0,0}}
v = matrix {{1},{2},{0},{-5},{2}}
X = matrix {{1,0,0},{-1,0,0},{0,1,0},{0,-1,0}}
Y = matrix {{-1/1,-1,0,0,-1,-1},{0,0,-1,-1,0,0},{-1,0,0,0,0,0},{0,-1,-1,0,-1,0},{0,0,0,-1,0,-1},{1,0,0,0,1,0},{0,1,0,0,0,1},{0,0,1,0,0,0},{0,0,0,1,0,0}}


Example: signSpace(Y)
ZZ^9 <--- ZZ^2236
