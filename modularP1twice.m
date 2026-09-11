// HallDivisors := function(n) 
//     assert n ge 1;
//     return [d : d in Divisors(n) | GCD(d,Integers()!(n/d)) eq 1];
// end function;

HallDivisors := function(n) 
    assert n ge 1;
    return [d : d in Divisors(n) | GCD(d,Integers()!(n/d)) eq 1 and d ne 1];
end function;

allpairs := [
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
[9,10],
[10,10]
];

someodd := [pair : pair in allpairs | IsOdd(pair[1]) or IsOdd(pair[2])];


old_candidates := [ [ [] : j in [1..11] ] : i in [1..11] ];

for pair in allpairs do
	//print pair;
	a := pair[1]; b := pair[2];
	old_candidates[a,b] := [N : N in [1..10^5] | GenusX0NQuotient(N,[]) eq (a-1)*(b-1)];
end for;

initial := &+[#S : S in old_candidates];
//initial; //121

candidates := old_candidates;


counter := 0;

print "begin filter using odd degree:";
for pair in someodd do
	//print pair;
	a := pair[1]; b := pair[2];
	if IsOdd(a) then d := a; 
	else d := b;
	end if;

	for N in candidates[a,b] do 
		//print N;
		HD := [m: m in HallDivisors(N) | m gt 1];
    	min:= Min([GenusX0NQuotient(N,[m]) : m in HD]);
    	if d*0+2*min + (d-1)*1 lt (a-1)*(b-1) then
        //print N,"done";
        counter := counter + 1;
        candidates[a,b] := Exclude(candidates[a,b],N);
        print N,"is excluded";
    end if;
	end for;
end for;

print "done after odd gonality check:",counter;

//37 done


print "begin double Castelnuovo--Severi:";
counter := 0;
for pair in allpairs do
	//print pair;
	a := pair[1]; b := pair[2];

	for N in candidates[a,b] do
		//print N;
		HD := [m: m in HallDivisors(N) | m gt 1];
    	min := Min([GenusX0NQuotient(N,[m]) : m in HD]);
    	if b*0+2*min + (b-1)*1 lt (a-1)*(b-1) then
        //print N,"done"; 
    	counter := counter + 1;
     candidates[a,b] := Exclude(candidates[a,b],N);
     print N,"is excluded";
    end if;
	end for;
end for;

print "done after double Castelnuovo--Severi:",counter;

//51 done

left := 0;
for pair in allpairs do
	a := pair[1]; b := pair[2];
	if candidates[a,b] ne [] then
		print "------";
		print pair,candidates[a,b];
		left := left + #candidates[a,b];
	end if;
end for;

//left; 52

counter := 0;
for pair in someodd do
	//print pair;
	a := pair[1]; b := pair[2];
	if IsOdd(a) then d := a; 
	else d := b;
	end if;
	for N in [N : N in candidates[a,b] | #PrimeDivisors(N) ne 1] do
		print N;
		HD := [m: m in HallDivisors(N) | m gt 1];
		for m in HD do
			HDm := [m1: m1 in HallDivisors(N) | m1 gt 1 and m1 ne m];
			min := Min([GenusX0NQuotient(N,[m,m1]) : m1 in HDm]);
    		if d*0+4*min + (d-1)*3 lt (a-1)*(b-1) then
        		//print N,"done"; 
        		counter := counter + 1;
     			candidates[a,b] := Exclude(candidates[a,b],N);
     		end if;
     	end for;
	end for;
end for;

print "done after depth two quotient Castelnuovo--Severi with odd gonality:",counter;

//N-O: C-gonality of X_0(197) is 8

candidates[5,5] := Exclude(candidates[5,5],197);

//N-O: Proposition Proposition 5.23. C-gonality of X_0(172) is at least 6

candidates[5,6] := Exclude(candidates[5,6],172);
candidates[5,8] := Exclude(candidates[5,8],250);
candidates[5,9] := Exclude(candidates[5,9],268);
candidates[5,9] := Exclude(candidates[5,9],397);

print "Najman-Orlic exlcude further five cases";

Left := [];
for pair in allpairs do
	a := pair[1]; b := pair[2];
	if candidates[a,b] ne [] then
		print "------";
		print pair,candidates[a,b];
		Left := Left cat candidates[a,b];

	end if;
end for;

//#Left; 46

print "we are left with",#Left,"stubborn cases";

/*
------
[ 5, 5 ]
[ 162 ] (stubborn) //gon_C = 5,6 in NO
------
[ 5, 8 ]
[ 250 (stubborn) ]
------
[ 5, 9 ]
[ 268 (stubborn), 397 (stubborn) ]
------
[ 6, 6 ]
[ 180 (stubborn), 182 (stubborn), 212 (stubborn), 216 (stubborn), 237 (stubborn), 265 (stubborn), 307 (stubborn), 313 (stubborn) ]
------
[ 6, 7 ]
[ 373 (stubborn) ] //prime
------
[ 6, 8 ]
[ 228 (stubborn), 234 (stubborn), 292 (stubborn), 304 (stubborn), 333 (stubborn), 403 (stubborn), 433 (stubborn), 529 (stubborn) ]
------
[ 6, 9 ]
[ 332 (done), 487 (done) ]
------
[ 6, 10 ]
[ 322 (done), 345 (done), 385 (done), 417 (stubborn), 423 (done), 475 (done), 547 (stubborn) ]
------
[ 6, 11 ]
[ 613 (stubborn) ]
------
[ 7, 7 ]
[ 298 (stubborn)]
------
[ 7, 8 ] //Corollary 4.5. in N-O
[ 346 (stubborn) ]
------
[ 7, 9 ]
[ 394 (stubborn), 625 (stubborn) ]
------
[ 7, 10 ]
[ 653 (stubborn)]
------
[ 8, 8 ]
[ 340 (stubborn), 384 (stubborn), 453 (stubborn), 484 (stubborn), 512 (stubborn) ]
------
[ 8, 10 ]
[ 514 (stubborn), 769 (done) ]
------
[ 9, 10 ]
[ 586 (stubborn), 877 (stubborn) ]
------
[ 10, 10 ]
[ 480 (stubborn), 640 (stubborn), 664 (stubborn), 715 (stubborn), 977 (stubborn) ]



for N in [512 ] do
	HD := [m : m in HallDivisors(N)| m ne 1];
	print 1, GenusX0NQuotient(N,[]);
	for m in HD do
		print m, GenusX0NQuotient(N,[m]); 
	end for;
	print "========";
end for;

*/

print "fixed points obstructions:";

for pair in [pair : pair in allpairs | pair[1] eq pair[2]] do
		a := pair[1];
	for N in candidates[a,a] do
		if IsOdd(a) then 
			possible := [2,2*a];
		else possible := [0,4,2*a];
		end if;
		HD := [m: m in HallDivisors(N) | m gt 1];
		for m in HD do
			if AtkinLehnerNumberOfFixedPoints(N,m) in possible eq false then
				print N, "is excluded";
				candidates[a,a] := Exclude(candidates[a,a],N);
			end if;
		end for;
	end for;
end for;


for pair in [pair : pair in allpairs | pair[1] ne pair[2]] do
		a := pair[1]; b := pair[2];
	for N in candidates[a,b] do
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

		HD := [m: m in HallDivisors(N) | m gt 1];
		for m in HD do
			if AtkinLehnerNumberOfFixedPoints(N,m) in possible eq false then
				print N, "is excluded";
				candidates[a,b] := Exclude(candidates[a,b],N);
			end if;
		end for;
	end for;
end for;



Left := [];
for pair in allpairs do
	a := pair[1]; b := pair[2];
	if candidates[a,b] ne [] then
		print "------";
		print pair,candidates[a,b];
		Left := Left cat candidates[a,b];

	end if;
end for;

#Left; //19

// Left;
// [ 212, 216, 237, 307, 304, 433, 529, 417, 547, 653, 384, 512, 514, 586, 664, 
// 977 ]

// [ 212, 216, 237, 307, 304, 433, 529, ??332, 417, ??423, 547, 653, 384, 512, 514, 
// ??769, 586, 664, 977 ]


// candidates[6,9] := Exclude(candidates[6,9],332);
// candidates[6,9] := Exclude(candidates[6,9],487);

// candidates[6,10] := Exclude(candidates[6,10],322);
// candidates[6,10] := Exclude(candidates[6,10],345);
// candidates[6,10] := Exclude(candidates[6,10],385);
// candidates[6,10] := Exclude(candidates[6,10],423);
// candidates[6,10] := Exclude(candidates[6,10],475);

// candidates[6,11] := Exclude(candidates[6,11],613);
// candidates[7,9] := Exclude(candidates[7,9],625);

// candidates[8,10] := Exclude(candidates[8,10],769);