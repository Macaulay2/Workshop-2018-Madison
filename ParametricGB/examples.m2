-- This file contains a collection of examples for benchmarking the
-- ParametricGB package. Each example has timings in seconds for the two walk
-- strategies and Macaulay2's standard gb function. Timings were performed on a
-- 2.3GHz i7-3615QM using Macaulay2 1.11.
--
-- sources:
--   KSW = Kapur, Sun, Wang, "An efficient method for computing comprehensive Groebner bases"


-- example 1, KSW Example 5.1
-- cgs: 0.0393493
-- cgb: 0.0438907
restart
needsPackage "ParametricGB"

KK = QQ
R = KK[a,b,c][x,y]
F = {a*x - b, b*y - a, c*x^2 - y, c*y^2 - x}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 2, KSW S1
-- cgs: 0.0964213
-- cgb: 9.61966
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c][x,y]
F = {a*x^4*y + x*y^2 + b*x, x^3 + 2*x*y + c*y, x^2*y + b*x^2}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 3, KSW S2
-- cgs: 0.0863808
-- cgb: 0.36782
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c][x,y]
F = {a*x^2*y^3 + a*y + b*y, x^2*y^2 + x*y + 2*x, a*x^2 + b*y + 2*x}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 4, KSW S3
-- cgs: 0.0980266
-- cgb: 
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x,y]
F = {a*x^4 + c*x^2 + y, b*x^3 + x^2 + y + 2, c*x^2 + d*x + y}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 5, KSW S4
-- cgs: 1.38622
-- cgb:
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x,y,z]
F = {a*x^3*y + c*x*z^2, x^4*y + 3*d*y + z, c*x^2 + b*x*y, x^2*y^2 + x^2, x^5 + y^5}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 6, KSW S5
-- cgs: 0.604736
-- cgb:
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c][x,y]
F = {y^3 + b*x, a*x^2*y + b*x*y + c*x, y^2 + b*x^2*y + c*x*y}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 7, KSW S6
-- cgs: 0.312092
-- cgb:
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x]
F = {d*x^4 + a*x^3 + b*x^2 + c*x + d, 4*b*x^3 + 3*a*x^2 + 2*b*x + c}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 8, KSW S7
-- cgs: 2.25879
-- cgb:
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[a,b,c,d][x,y,z,w]
F = {a*x^2 + b*y*z, c*w^2 + b*y + z, (x-z)^2 + (y-w)^2, 2*d*x*w - 2*b*y*z}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

-- example 9, KSW P3P
-- cgs: 2477.95 (2449.58 in isConsistent)
-- cgb:
restart
needsPackage "ParametricGB"

KK = ZZ/32003
R = KK[p,q,r,a,b][x,y]
F = {(1-a)*y^2 - a*x^2 - p*y + a*r*x*y + 1, (1-b)*x^2 - b*y^2 - q*x + b*r*x*y + 1}

CGS = elapsedTime comprehensiveGroebnerSystem F;
CGB1 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Module");
CGB2 = elapsedTime comprehensiveGroebnerBasis(F, Strategy => "Polynomial");

