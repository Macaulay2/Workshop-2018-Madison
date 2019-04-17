------------------------------------------------
-- Code for Multigraded Betty Tally Presentation
-- this will be removed once multigraded is done
------------------------------------------------

MultigradedBettiTally = new Type of BettiTally
MultigradedBettiTally.synonym = "multigraded Betti tally"
MultigradedBettiTally List := (B,l) -> applyKeys(B, (i,d,h) -> (i,d-l,h))

-- Helper function for pretty-printing the hash table
rawMultigradedBettiTally = B -> (
    if keys B == {} then return 0;
    N := max apply(pairs B, (key, n) -> ((i,d,h) := key; length d));
    R := ZZ[vars(0..N-1)];
    H := new MutableHashTable;
    (rows, cols) := ({}, {});
    scan(pairs B,
        (key, n) -> (
	    (i,d,h) := key;
	    key = (h, i);
	    (rows, cols) = (append(rows, h), append(cols, i));
	    if compactMatrixForm then (
		m := n * R_d;
	        if H#?key then H#key = H#key + m else H#key = m;
		) else (
		s := toString n | ":" | toString d;
                if H#?i then H#i = H#i | {s} else H#i = {s};
		);
	    ));
    (rows, cols) = (sort unique rows, sort unique cols);
    if compactMatrixForm then (
        T := table(toList (0 .. length rows - 1), toList (0 .. length cols - 1),
            (i,j) -> if H#?(rows#i,cols#j) then H#(rows#i,cols#j) else 0);
        -- Making the table
        xAxis := toString \ cols;
        yAxis := (i -> toString i | ":") \ rows;
        T = applyTable(T, n -> if n === 0 then "." else toString raw n);
        T = prepend(xAxis, T);
        T = apply(prepend("", yAxis), T, prepend);
        ) else (
        T = table(toList (0 .. length rows - 1), sort keys H,
            (i,k) -> if i < #H#k then H#k#i else null);
        T = prepend(sort keys H,T);
        );
    T
    )

net MultigradedBettiTally := B -> netList(rawMultigradedBettiTally B, Alignment => Right, HorizontalSpace => 1, BaseRow => 1, Boxes => false)

-- Converts a BettiTally into a MultigradedBettiTally, which supports better pretty-printing
-- Note: to compactify the pretty-printed output, set compactMatrixForm to false.
multigraded = method(TypicalValue => MultigradedBettiTally)
multigraded BettiTally := bt -> new MultigradedBettiTally from bt
