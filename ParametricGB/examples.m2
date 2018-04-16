-- list of examples for testing parametric Groebner computations
-- source: KSW = Kapur, Sun, Wang "An efficient method for computing comprehensive Groebner bases"

-- example 1, KSW Example 5.1
restart
needsPackage "ParametricGB"

KK = QQ
R = QQ[a,b,c][x,y]
F = {a*x - b, b*y - a, c*x^2 - y, c*y^2 - x}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 2, KSW S1
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c][x,y]
F = {a*x^4*y + x*y^2 + b*x, x^3 + 2*x*y + c*y, x^2*y + b*x^2}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 3, KSW S2
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c][x,y]
F = {a*x^2*y^3 + a*y + b*y, x^2*y^2 + x*y + 2*x, a*x^2 + b*y + 2*x}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 4, KSW S3
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x,y]
F = {a*x^4 + c*x^2 + y, b*x^3 + x^2 + y + 2, c*x^2 + d*x + y}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 5, KSW S4
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x,y,z]
F = {a*x^3*y + c*x*z^2, x^4*y + 3*d*y + z, c*x^2 + b*x*y, x^2*y^2 + x^2, x^5 + y^5}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 6, KSW S5
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c][x,y]
F = {y^3 + b*x, a*x^2*y + b*x*y + c*x, y^2 + b*x^2*y + c*x*y}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 7, KSW S6
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x]
F = {d*x^4 + a*x^3 + b*x^2 + c*x + d, 4*b*x^3 + 3*a*x^2 + 2*b*x + c}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 8, KSW S7
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x,y,z,w]
F = {a*x^2 + b*y*z, c*w^2 + b*y + z, (x-z)^2 + (y-w)^2, 2*d*x*w - 2*b*y*z}

elapsedTime comprehensiveGB({}, {1}, F)

-- example 9, KSW P3P
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[p,q,r,a,b][x,y]
F = {(1-a)*y^2 - a*x^2 - p*y + a*r*x*y + 1, (1-b)*x^2 - b*y^2 - q*x + b*r*x*y + 1}

elapsedTime comprehensiveGB({}, {1}, F)
