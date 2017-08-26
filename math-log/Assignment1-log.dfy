method Main() {
	var l, n := FindLog(1);

	l, n := FindLog(8);
	print("\nlog of 8 is ");
	print l; // == 3
}

function PowersOfTwo(d: nat) : nat { if d == 0 then 1 else 2*PowersOfTwo(d-1) }


method FindLog(N: nat) returns (l: nat, n: nat)
	requires 1 <= N
	ensures PowersOfTwo(l) <= N < PowersOfTwo(l+1)
{
	n := N;
	assert 1 <= N == n;
	// TODO: continue here... using the predicate Inv (defined below) as a loop invariant;
	// the precondition is "1 <= N == n", the postcondition is "2^l <= N < 2^(l+1)",
	// and the frame is "l,n"; note that you are not allowed to change this specification!

	// Step 1:  strengthen postcond. 1.1
	assert  1 <= N;
	l,n := FL1(N,n);
	assert Inv(l,n,N);
	L1(N,l,n);
	assert PowersOfTwo(l) <= N < PowersOfTwo(l+1);
}


method FL1(N: nat ,n0: nat) returns (l: nat, n: nat)
	requires 1 <= N
	requires n0 == N
	ensures Inv(l,n,N)
{
	n := n0;
	//Step 2 : leading ssignmen 8.5 and assignment 1.3
	assert n==N && 1 <= N && 0==0;
	l := 0;
	assert l == 0;
	l,n := FL2(N,n,l);
	assert Inv(l,n,N);
}

method FL2(N: nat ,n0: nat, l0: nat) returns (l: nat, n: nat)
	requires 1 <= N
	requires n0 == N
	requires l0 == 0
	ensures Inv(l,n,N)
{
	l := l0;
	n := n0;
	//weaken pre Cond 1.2
	assert 1<=N && n == N == n0 && l == 0 == l0;
	l,n := FL22(N,n,l);
	assert Inv(l,n,N) && n==1;
}

method FL22(N: nat ,n0: nat, l0: nat) returns (l: nat, n: nat)
	requires 1 <= N
	requires n0 == N
	requires l0 == 0
	ensures Inv(l,n,N) && n==1
{
	l,n := l0,n0;
	assert 1 <=N && n==N && l == 0;
	// Step 3 : iteration 5.5
	assert Inv(l,n,N);
	while(2 <= n )
		invariant Inv(l,n,N)
		decreases n
	{
		ghost var n1: nat := n;
		ghost var l1: nat := l;
		assert Inv(l,n,N) && 2 <= n == n1 <= N && l1 == l;
		l,n := FL3(N,n,l);
		assert  Inv(l,n,N) && 0 < n == n1/2 && 0 < l==l1+1;
	}
	assert n == 1 && Inv(l,n,N);
}

 method FL3(N: nat ,n0: nat, l0: nat) returns (l: nat, n: nat)
	requires Inv(l0,n0,N) 
	requires 1 < N
	requires 2 <= n0 <= N
	ensures Inv(l,n,N) && 0 < n == n0/2 && 0 < l == l0+1
{
	l,n := l0,n0;
	assert l0 == l;
	assert 2 <= n == n0;
	// Step 4: following assignment 3.5
	assert Inv(l,n,N) && 1 < N ;
	l,n := FL4(N,n,l);
	assert Inv(l+1,n/2,N) && l == l0 && n == n0;
	l:= l0 +1;
	n:= n0/2;
	assert  Inv(l,n,N) && 0 < n == n0/2 && 0 < l==l0+1 ;
}

	method FL4(N: nat ,n0: nat, l0: nat) returns (l: nat, n: nat)
	requires Inv(l0,n0,N) && 1 < N && 2 <= n0 
	ensures Inv(l+1,n/2,N) && l0==l && n0==n
{
	l,n := l0,n0;
	//step 5: contract frame 5.4
	assert l0 == l;
	assert n0 == n;
	assert 2 <= n;
	assert Inv(l,n,N) && 1 < N;
	L4(N,l,n);
	assert Inv(l+1,n/2,N) && l0==l && n0==n;
}

	

lemma L4(N: nat ,l: nat, n: nat)
	requires  1 < N //pre1
	requires n>=2 // pre2
	requires Inv(l,n,N) // pre3
	ensures  Inv(l+1,n/2,N) // post1
	

lemma L1(N: nat ,l: nat, n: nat)
	requires 1 <= N
	requires Inv(l,n,N)
	ensures PowersOfTwo(l) <= N < PowersOfTwo(l+1)
		

predicate Inv(l: nat, n: nat, N: nat)
{
	n * PowersOfTwo(l) <= N < (n + 1) * PowersOfTwo(l) && 1 <= n
}
