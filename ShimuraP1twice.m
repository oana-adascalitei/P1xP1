// given a positive integer n, returns the sequence of divisors d | n such that GCD(d,n/d) = 1.
HallDivisors := function(n) 
    assert n ge 1;
    return [d : d in Divisors(n) | GCD(d,Integers()!(n/d)) eq 1 and d ne 1];
end function;

// quot_genus.m
// the main function, quot_genus, computes for a given indefinite rational 
// quaternion discriminant D, positive integer N coprime to D, and Hall divisor m
// of DN, the genus of the quotient Shimura curve X_0^D(N)/<w_m>


// phi_from_fact
// Given natural N, factorization of N (list of pairs (p,a)), computes phi(N) 

phi_from_fact := function(N,F)
    P := N;
    for i in [1..#F] do
        P := P*(1-1/(F[i][1]));
    end for;
    return P;
end function;



// psi_from_fact 
// Given natural N, factorization of N (list of pairs (p,a)), computes psi(N)

psi_from_fact := function(N,F)
    M := 1;
        for i in [1..#F] do
            M := M * (F[i][1]+1)*F[i][1]^(F[i][2]-1);
        end for;
    return M;
end function;



// e1_from_fact: Given factorizations F_D and F_N of a rational quaternion discriminant D and
// a natural number N which is coprime to D, respectively, returns e_1(D,N)

e1_from_facts := function(F_D,F_N,N)
    if (N mod 4) eq 0 then
        return 0;
    else
        P := 1;
        for i in [1..#F_D] do
            P := P*(1-KroneckerSymbol(-4,F_D[i][1]));
        end for;
        for i in [1..#F_N] do
            P := P*(1+KroneckerSymbol(-4,F_N[i][1]));
        end for;
        return P;
    end if; 
end function;



// e3_from_fact: Given factorizations F_D and F_N of a rational quaternion discriminant D and
// a natural number N which is coprime to D, respectively, returns e_3(D,N)

e3_from_facts := function(F_D,F_N,N)
    if (N mod 9) eq 0 then
        return 0;
    else
        P := 1;
        for i in [1..#F_D] do
            P := P*(1-KroneckerSymbol(-3,F_D[i][1]));
        end for;
        for i in [1..#F_N] do
            P := P*(1+KroneckerSymbol(-3,F_N[i][1]));
        end for;
        return P;
    end if; 
end function;



// genus

genus := function(D,N)
    FD := Factorization(D);
    FN := Factorization(N);
    return (1+phi_from_fact(D,FD)*psi_from_fact(N,FN)/12 - e1_from_facts(FD,FN,N)/4 - e3_from_facts(FD,FN,N)/3);
end function; 



// psi_p 
// Given natural N, prime p, computes psi_p(N) as in Ogg83 Thm 2

psi_p := function(N,p)
    k := Valuation(N,p);
    if k eq 0 then 
        return 1;
    else 
        return p^k + p^(k-1); 
    end if;
end function; 



// count_local_embeddings
// Counts number of local embeddings of order R of discriminant f^2*delta_K into order of level N in 
// quaternion algebra B of discriminant D, via Ogg83 Theorem 2 

count_local_embeddings := function(D,N,p,delta_K,f)

    assert IsDivisibleBy(D*N,p);
    
    if (f mod p eq 0) then 
        symbol_R_p := 1;
    else
        symbol_R_p := KroneckerSymbol(delta_K,p);
    end if; 

    if (D mod p) eq 0 then // case i
        return 1 - symbol_R_p;

    elif (N mod p) eq 0 then 

        k := Valuation(N,p); //3
        l := Valuation(f,p); //0

        if k eq 1 then // case ii
            return 1 + symbol_R_p;

        elif k ge (2+2*l) then  // case iii a
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*psi_p(f,p); 
            else
                return 0;
            end if; 

        elif k eq (1+2*l) then  // case iii b
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*psi_p(f,p);
            elif KroneckerSymbol(delta_K,p) eq 0 then
                return p^l;
            else 
                return 0;
            end if;

        elif k eq 2*l then  // case iii c
            return p^(l-1)*(p+1+KroneckerSymbol(delta_K,p));

        elif (f^2 mod p*N) eq 0 then // case iii d
            if (k mod 2) eq 0 then
                return p^k+p^(k-1);
            else
                return 2*p^k;
            end if;

        end if;
    end if;
end function; 



// count_fixed_points
// given quaternion discriminant D, N coprime to D, m || DN, delta_K, and f, 
// computes number of f^2*delta_K-CM fixed points of w_m on X_0^D(N)
// by Eichler's Theorem, see Thm 1 in Ogg83 and eqn 4 in Ogg83

count_fixed_points := function(D,N,m,delta_K,f)
    P := 1;
    for pair in Factorization(Integers()!(D*N/m)) do 
        p := pair[1];
        P := P*count_local_embeddings(D,N,p,delta_K,f);
    end for;

    return ClassNumber(delta_K*f^2)*P;
end function; 



// sqfree_part
// given positive integer m, returns the sqfree part of m
sqfree_part := function(m)
    S := 1;
    for pair in Factorization(m) do
        v := Valuation(m,pair[1]);
        if (v mod 2) eq 1 then 
            S := S*pair[1];
        end if;
    end for;

    return S;
end function; 

// gens_to_identifier: given DN an integer and gens a set of Hall divisors of DN,
// returns the identifier for W = <w_m | m in gens>, by which we mean the ordered sequence of
// Hall divisors m so that {w_m | m in identifier} is the full set of nontrivial elements of W
gens_to_identifier := function(DN,gens)

     G := Setseq(gens);
     prods := Subsets(gens,2);
     while #prods gt 0 do
    	newprod := [];
    	for p in prods do
    	    A := (&*p) div GCD(p)^2;
    	    if (A notin G) and (A notin newprod) then
              	Append(~newprod,A);
    	    end if;
    	end for;

    	if #newprod gt 0 then
    	    prods := {{a,b} : a in G, b in newprod} join Subsets(Seqset(newprod),2);
    	    G := G cat newprod;
    	else
    	    prods := {};
    	end if;

     end while;

     // if 1 was not included in the original generating set, add it to the identifier G
     if not (1 in G) then 
          Append(~G,1);
     end if;

     Sort(~G); 

     return G;
end function;

// quot_genus
// given quaternion discriminant D, N coprime to D, and W a subgroup of W_0(D,N) given
// by a list [m_1, ..., m_n] of all m such that w_m in W, computes
// the genus of X_0^D(N)/W
// by Riemann--Hurwitz, also see Ogg83 eqn 3


fixed_by_AL := function(D,N,W)

    g := genus(D,N); // genus of the top curve
    //first make sure W is an identifier
    W := SequenceToSet(W);
    W := gens_to_identifier(D*N,W);
    deg := #W; // degree of quotient map
    assert #W eq 1 or PrimeDivisors(#W) eq [2];

    fixed_number := 0; // initializing fixed point count

    for m in [m : m in W | m ne 1] do
        
        if m eq 2 then 
            fixed_number := fixed_number + count_fixed_points(D,N,m,-4,1) + count_fixed_points(D,N,m,-8,1); 

        elif (m mod 4) eq 3 then 
            disc_K := -1*sqfree_part(m); // K = Q(sqrt(-m))
            _,f := IsSquare(Integers()!(m/sqfree_part(m)));
            fixed_number := fixed_number + count_fixed_points(D,N,m,disc_K,f) + count_fixed_points(D,N,m,disc_K,2*f);

        else
            disc_K := -4*(sqfree_part(m)); // K = Q(sqrt(-m))
            _,f := IsSquare(Integers()!(m/sqfree_part(m)));
            fixed_number := fixed_number + count_fixed_points(D,N,m,disc_K,f); 

        end if;
    end for;


    return fixed_number;
end function;

quot_genus := function(D,N,W)

    g := genus(D,N); // genus of the top curve
    //first make sure W is an identifier
    W := SequenceToSet(W);
    W := gens_to_identifier(D*N,W);
    deg := #W; // degree of quotient map
    assert #W eq 1 or PrimeDivisors(#W) eq [2];

    fixed_number := 0; // initializing fixed point count

    for m in [m : m in W | m ne 1] do
        
        if m eq 2 then 
            fixed_number := fixed_number + count_fixed_points(D,N,m,-4,1) + count_fixed_points(D,N,m,-8,1); 

        elif (m mod 4) eq 3 then 
            disc_K := -1*sqfree_part(m); // K = Q(sqrt(-m))
            _,f := IsSquare(Integers()!(m/sqfree_part(m)));
            fixed_number := fixed_number + count_fixed_points(D,N,m,disc_K,f) + count_fixed_points(D,N,m,disc_K,2*f);

        else
            disc_K := -4*(sqfree_part(m)); // K = Q(sqrt(-m))
            _,f := IsSquare(Integers()!(m/sqfree_part(m)));
            fixed_number := fixed_number + count_fixed_points(D,N,m,disc_K,f); 

        end if;
    end for;


    return (1/(2*deg))*(2*g-2 - fixed_number)+1;
end function;


all_pairs := [];

Ds := [D : D in [6..87640] | IsSquarefree(D) and IsEven(#PrimeDivisors(D))];

for D in Ds do
    print D;
    all_pairs := all_pairs cat [[D,N]: N in [1..Floor(87640/D)] | GCD(D,N) eq 1];
end for;

all_bidegrees := [
[4,4],
[4,5],
[4,6],
[4,7],
[4,8],
[4,9],
[4,10],
[4,11],
[4,12],
[5,5],
[5,6],
[5,7],
[5,8],
[5,9],
[5,10],
[5,11],
[6,6],
[6,7],
[6,8],
[6,9],
[6,10],
[6,11],
[7,7],
[7,8],
[7,9],
[7,10],
[8,8],
[8,9],
[8,10],
[9,9],
[9,10],
[10,10]
];

someodd := [pair : pair in all_bidegrees | IsOdd(pair[1]) or IsOdd(pair[2])];

old_candidates := [ [ [] : j in [1..12] ] : i in [1..12] ];

for pair in all_bidegrees do
    print pair;
    a := pair[1]; b := pair[2];
    old_candidates[a,b] := [p: p in all_pairs | genus(p[1],p[2]) eq (a-1)*(b-1)];
end for;


initial := &+[#old_candidates[pair[1],pair[2]] : pair in all_bidegrees]; 
print "number of initial candidates",initial; //457

candidates := old_candidates;

counter := 0;
for pair in all_bidegrees do
    print pair;
    a := pair[1]; b := pair[2];

    for DN in candidates[a,b] do
        D := DN[1]; N := DN[2];
        HD := [m: m in HallDivisors(D*N) | m gt 1];
        min := Min([quot_genus(D,N,[m]) : m in HD]);
        if b*0+2*min + (b-1)*1 lt (a-1)*(b-1) then
            print D,N,"done"; 
            counter := counter + 1;
            print DN, "is excluded";
            candidates[a,b] := Exclude(candidates[a,b],[D,N]);
        end if;
    end for;
end for;


print "done after double Castelnuovo--Severi:",counter; //339



counter := 0;
for pair in someodd do
    //print pair;
    a := pair[1]; b := pair[2];
    if IsOdd(a) then d := a; else d := b;
    end if;

    for DN in candidates[a,b] do
        D := DN[1]; N := DN[2];
        HD := [m: m in HallDivisors(D*N) | m gt 1];
        min := Min([quot_genus(D,N,[m]) : m in HD]);
        if d*0+2*min + (d-1)*1 lt (a-1)*(b-1) then
        //print D,N,"done"; 
        counter := counter + 1;
        print DN, "is excluded";
        candidates[a,b] := Exclude(candidates[a,b],[D,N]);
        end if;
    end for;
end for;


print "done after odd gonality check:",counter; //4


counter := 0;
for pair in someodd do
    print pair;
    a := pair[1]; b := pair[2];
    if IsOdd(a) then d := a; else d := b;
    end if;
        for DN in candidates[a,b] do
            print data;
            D := DN[1]; N := DN[2];
            HD := [m: m in HallDivisors(D*N) | m gt 1];
        for m in HD do
            HDm := [m1: m1 in HallDivisors(D*N) | m1 gt 1 and m1 ne m];
            min := Min([quot_genus(D,N,[m,m1]) : m1 in HDm]);
            if d*0+4*min + (d-1)*3 lt (a-1)*(b-1) then
                counter := counter + 1;
                print DN, "is excluded";
                candidates[a,b] := Exclude(candidates[a,b],[D,N]);
            end if;
        end for;
    end for;
end for;

print "done after depth two quotient Castelnuovo--Severi with odd gonality:",counter; //0


candidates[4,4] := Exclude(candidates[4,4],[6,35]);
candidates[4,4] := Exclude(candidates[4,4],[10,21]);


//geometrically tetragonal, Italian paper: (14,17)

//not geometrically tetragonal, Italian paper: 
//(422,1),(10,67),(10,103),(14,41),(15,31),(33,8),(33,13)
//(123,2),(129,2),(305,1),(393,1),(526,1),(501,1),(33,19)
//(51,8),(85,4),(106,7),(469,1)

candidates[4,4] := Exclude(candidates[4,4],[14,17]);

candidates[4,6] := Exclude(candidates[4,6],[77,2]);

candidates[4,7] := Exclude(candidates[4,7],[422,1]);
candidates[4,7] := Exclude(candidates[4,7],[454,1]);

candidates[4,8] := Exclude(candidates[4,8],[6,95]);
candidates[4,8] := Exclude(candidates[4,8],[10,67]);
candidates[4,8] := Exclude(candidates[4,8],[14,41]);
candidates[4,8] := Exclude(candidates[4,8],[15,31]);
candidates[4,8] := Exclude(candidates[4,8],[33,8]);
candidates[4,8] := Exclude(candidates[4,8],[33,13]);
candidates[4,8] := Exclude(candidates[4,8],[69,5]);
candidates[4,8] := Exclude(candidates[4,8],[82,5]);
candidates[4,8] := Exclude(candidates[4,8],[123,2]);
candidates[4,8] := Exclude(candidates[4,8],[129,2]);
candidates[4,8] := Exclude(candidates[4,8],[305,1]);
candidates[4,8] := Exclude(candidates[4,8],[393,1]);
candidates[4,8] := Exclude(candidates[4,8],[514,1]);
candidates[4,8] := Exclude(candidates[4,8],[526,1]);

candidates[4,9] := Exclude(candidates[4,9],[586,1]);

candidates[4,10] := Exclude(candidates[4,10],[14,53]);
candidates[4,10] := Exclude(candidates[4,10],[38,17]);
candidates[4,10] := Exclude(candidates[4,10],[133,2]);
candidates[4,10] := Exclude(candidates[4,10],[158,3]);
candidates[4,10] := Exclude(candidates[4,10],[166,3]);
candidates[4,10] := Exclude(candidates[4,10],[489,1]);
candidates[4,10] := Exclude(candidates[4,10],[501,1]);


candidates[4,12] := Exclude(candidates[4,12],[6,155]);
candidates[4,12] := Exclude(candidates[4,12],[6,161]);
candidates[4,12] := Exclude(candidates[4,12],[6,197]);
candidates[4,12] := Exclude(candidates[4,12],[10,63]);
candidates[4,12] := Exclude(candidates[4,12],[10,91]);
candidates[4,12] := Exclude(candidates[4,12],[10,103]);
candidates[4,12] := Exclude(candidates[4,12],[15,28]);
candidates[4,12] := Exclude(candidates[4,12],[15,32]);
candidates[4,12] := Exclude(candidates[4,12],[15,47]);
candidates[4,12] := Exclude(candidates[4,12],[26,21]);
candidates[4,12] := Exclude(candidates[4,12],[33,19]);
candidates[4,12] := Exclude(candidates[4,12],[34,15]);
candidates[4,12] := Exclude(candidates[4,12],[34,23]);
candidates[4,12] := Exclude(candidates[4,12],[46,17]);
candidates[4,12] := Exclude(candidates[4,12],[51,8]);
candidates[4,12] := Exclude(candidates[4,12],[51,11]);
candidates[4,12] := Exclude(candidates[4,12],[85,4]);
candidates[4,12] := Exclude(candidates[4,12],[106,7]);
candidates[4,12] := Exclude(candidates[4,12],[161,2]);
candidates[4,12] := Exclude(candidates[4,12],[201,2]);
candidates[4,12] := Exclude(candidates[4,12],[437,1]);
candidates[4,12] := Exclude(candidates[4,12],[451,1]);
candidates[4,12] := Exclude(candidates[4,12],[469,1]);
candidates[4,12] := Exclude(candidates[4,12],[485,1]);
candidates[4,12] := Exclude(candidates[4,12],[802,1]);
candidates[4,12] := Exclude(candidates[4,12],[1518,1]);



//unsure: (38,5),(133,1),(177,1),(62,5),(94,3),(217,1),(382, 1)
//(51,7),(301,1),(505,1)



//(394,1),(694,1),(6,157),(22,25) are not geometrically tetragonal, hence gonality is at least 5

//(34,7) is tetragonal

//quot_genus(34,7,[17,34*7]); //0


// for pair in [pair : pair in all_bidegrees | candidates[pair[1],pair[2]] ne []] do
//     print pair;
//     a := pair[1]; b := pair[2];

//     for data in candidates[a,b] do
//         D := data[1]; N := data[2];
//         HD := [m: m in HallDivisors(D*N) | m gt 1];
//             min := Min([quot_genus(D,N,[m]) : m in HD]);
//             if a*0+2*min + (a-1)*2 lt (a-1)*(b-1) then
//                 print data,min;
//             end if;
//     end for;
// end for;


// for pair in [pair : pair in all_bidegrees | candidates[pair[1],pair[2]] ne []] do
//     print "========";
//     print pair;
//     a := pair[1]; b := pair[2];

//     for data in candidates[a,b] do
//         D := data[1]; N := data[2];
//         HD := [m: m in HallDivisors(D*N) | m gt 1];
//             min := Min([quot_genus(D,N,[m]) : m in HD]);
//             if (a-1)*(b-1)-2*min+1 gt a then
//                 print data,min,"gonality of quotient is implied";
//             end if;
//     end for;
// end for;

candidates[4,12] := Exclude(candidates[4,12],[505,1]);

// candidates[6,10] := Exclude(candidates[6,10],[69,8]);
// candidates[6,10] := Exclude(candidates[6,10],[685,1]);
// candidates[6,10] := Exclude(candidates[6,10],[134,7]);
// candidates[6,10] := Exclude(candidates[6,10],[685,1]);
// candidates[6,10] := Exclude(candidates[6,10],[62,17]);
// candidates[6,10] := Exclude(candidates[6,10],[22,49]);
// candidates[6,10] := Exclude(candidates[6,10],[15,67]);
// candidates[6,10] := Exclude(candidates[6,10],[14,89]);
// candidates[6,10] := Exclude(candidates[6,10],[6,271]);
// candidates[6,10] := Exclude(candidates[6,10],[6,277]);
// candidates[6,10] := Exclude(candidates[6,10],[38,29]);
// candidates[6,10] := Exclude(candidates[6,10],[58,19]);
// candidates[6,10] := Exclude(candidates[6,10],[82,13]);
// candidates[6,10] := Exclude(candidates[6,10],[134,7]);
// candidates[6,10] := Exclude(candidates[6,10],[209,2]);
// candidates[6,10] := Exclude(candidates[6,10],[267,2]);
// candidates[6,10] := Exclude(candidates[6,10],[274,3]);
// candidates[6,10] := Exclude(candidates[6,10],[589,1]);

// candidates[8,9] := Exclude(candidates[8,9],[1366,1]);

// candidates[8,10] := Exclude(candidates[8,10],[38,41]);
// candidates[8,10] := Exclude(candidates[8,10],[889,1]);



// candidates[6,9] := Exclude(candidates[6,9],[982,1]);

Left := [];
for pair in all_bidegrees do
    a := pair[1]; b := pair[2];
    if candidates[a,b] ne [] then
        print "------";
        print pair,candidates[a,b];

        Left := Left cat candidates[a,b];
    end if;
end for;

print "we are left with",#Left,"stubborn cases";


for pair in [pair : pair in all_bidegrees | pair[1] eq pair[2]] do
        a := pair[1];
    for DN in candidates[a,a] do
        D := DN[1]; N := DN[2];
        if IsOdd(a) then 
            possible := [2,2*a];
        else possible := [0,4,2*a];
        end if;
        HD := [m: m in HallDivisors(D*N) | m gt 1];
        for m in HD do
            if fixed_by_AL(D,N,[m]) in possible eq false then
                print DN, "is excluded";
                candidates[a,a] := Exclude(candidates[a,a],DN);
            end if;
        end for;
    end for;
end for;




for pair in [pair : pair in all_bidegrees | pair[1] ne pair[2]] do
        a := pair[1]; b := pair[2];
    for DN in candidates[a,b] do
        D := DN[1]; N := DN[2];
        if IsOdd(a) then
            if IsOdd(b) then 
                possible := [2];
            else possible := [2,2*a];
            end if;
        end if;

        if IsEven(a) then
            if IsOdd(b) then
                possible := [2,2*b];
            else possible := [0,4,2*a,2*b];
            end if;
        end if;

        HD := [m: m in HallDivisors(D*N) | m gt 1];
        for m in HD do
            if fixed_by_AL(D,N,[m]) in possible eq false then
                print DN, "is excluded";
                candidates[a,b] := Exclude(candidates[a,b],DN);
            end if;
        end for;
    end for;
end for;

Left := [];
for pair in all_bidegrees do
    a := pair[1]; b := pair[2];
    if candidates[a,b] ne [] then
        print "------";
        print pair,candidates[a,b];
        Left := Left cat candidates[a,b];

    end if;
end for;

print "we are left with",#Left,"stubborn cases";

//we are left with 29 stubborn cases;

// Left;
// [
//     [ 34, 7 ],
//     [ 38, 5 ],
//     [ 133, 1 ],
//     [ 145, 1 ],
//     [ 177, 1 ],
//     [ 226, 1 ],
//     [ 62, 5 ],
//     [ 94, 3 ],
//     [ 217, 1 ],
//     [ 267, 1 ],
//     [ 382, 1 ],
//     [ 51, 7 ],
//     [ 301, 1 ],
//     [ 394, 1 ],
//     [ 694, 1 ],
//     [ 6, 157 ],
//     [ 622, 1 ],
//     [ 6, 271 ],
//     [ 6, 277 ],
//     [ 38, 29 ],
//     [ 58, 19 ],
//     [ 21, 32 ],
//     [ 38, 31 ],
//     [ 39, 23 ],
//     [ 745, 1 ],
//     [ 1365, 1 ],
//     [ 889, 1 ],
//     [ 955, 1 ],
//     [ 1149, 1 ]
// ]
