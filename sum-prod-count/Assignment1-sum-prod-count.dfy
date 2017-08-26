method Main() {
	var a: array<int> := new int[4];
	a[0] := 7;
	a[1] := -2;
	a[2] := 3;
	a[3] := -2;
	assert a[..] == [7,-2,3,-2];

	var s, p, c := SumProdAndCount(a, -2);
	assert a[0] == 7 && a[1] == -2 && a[2] == 3 && a[3] == -2;
	assert s == RecursiveSum(a, 0); // == 6
	assert p == RecursivePositiveProduct(a, 0); // == 21
	assert c == RecursiveCount(-2, a, 0); // == 2
	print "\nThe sum of all elements in [7,-2,3,-2] is ";
	print s;
	print "\nThe product of all positive elements in [7,-2,3,-2] is ";
	print p;
	print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
	print c;
}

function RecursiveSum(a: array<int>, from: nat) : int
	reads a
	requires a != null
	requires from <= a.Length
	decreases a.Length-from
{
	if from == a.Length then 0
	else a[from] + RecursiveSum(a, from+1)
}

function RecursivePositiveProduct(a: array<int>, from: nat) : int
	reads a
	requires a != null
	requires from <= a.Length
	decreases a.Length-from
{
	if from == a.Length then 1
	else if a[from] <= 0 then RecursivePositiveProduct(a, from+1)
	else a[from] * RecursivePositiveProduct(a, from+1)
}

function RecursiveCount(key: int, a: array<int>, from: nat) : int
	reads a
	requires a != null
	requires from <= a.Length
	decreases a.Length-from
{
	if from == a.Length then 0
	else if a[from] == key then 1+RecursiveCount(key, a, from+1)
	else RecursiveCount(key, a, from+1)
}

method SumProdAndCount(a: array<int>, key: int) returns (s: int, p: int, c: nat)
	requires a != null &&  0 < a.Length
	ensures s == RecursiveSum(a, 0)
	ensures p == RecursivePositiveProduct(a, 0)
	ensures c == RecursiveCount(key, a, 0)
{
	// Step 1 : introduce local variable 6.1 + strengthen postcond. 1.1
	var i: nat;
	assert a != null &&  0 < a.Length;
	i,s,p,c := SPC1a(a,key);
	assert Inv(a,key,i,s,p,c) && i == 0;
	L1(a,key,i,s,p,c);
	assert s == RecursiveSum(a, 0);
	assert p == RecursivePositiveProduct(a, 0);
	assert c == RecursiveCount(key, a, 0);
}

lemma L1(a: array<int> ,key: int,i: nat ,s: int , p: int , c: nat )
	requires Inv(a,key,i,s,p,c) && i == 0
	ensures s == RecursiveSum(a, 0)
	ensures p == RecursivePositiveProduct(a, 0)
	ensures c == RecursiveCount(key, a, 0)
	{}

predicate InvSum(a: array<int> ,i: nat ,s: int)
reads a
{
	a!=null && i <= a.Length && s == RecursiveSum(a,i)
}

predicate InvProduct(a: array<int> ,i: nat ,p: int)
reads a
{
	a!=null && i <= a.Length && p == RecursivePositiveProduct(a,i)
}

predicate InvCount(a: array<int> ,key: int,i: nat ,c: nat)
reads a
{
	a!=null && i <= a.Length && c == RecursiveCount(key,a,i)
}

predicate Inv(a: array<int> ,key: int,i: nat ,s: int , p: int , c: nat )
reads a
{
	a!=null && i <= a.Length && s == RecursiveSum(a,i) && p == RecursivePositiveProduct(a,i) && c == RecursiveCount(key,a,i)
}

	//check p value and go to the relevant method for c
method SPC1a(a: array<int> ,key: int) returns (i: nat ,s: int , p: int , c: nat)
	requires a != null &&  0 < a.Length
	ensures Inv(a,key,i,s,p,c) && i == 0
	{
		// Step 2 : rewrite precond + leading assignment 8.5
		assert a != null &&  0 < a.Length && 1==1 && a[a.Length-1] == a[a.Length-1];
		//init vars 
		i := a.Length -1 ;
		assert i == a.Length-1;
		s := a[a.Length - 1];
		assert s == a[a.Length - 1];

		i,s,p,c := SPC1aP(a,key,i,s);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}

method SPC1aP(a: array<int> ,key: int,i0: nat ,s0: int) returns (i: nat ,s: int , p: int , c: nat)
	requires a != null &&  0 < a.Length
	requires i0 == a.Length-1 && s0 == a[a.Length - 1]
	ensures Inv(a,key,i,s,p,c) && i == 0
{
	i,s := i0,s0;
	assert a != null &&  0 < a.Length;
	assert i == a.Length-1 && s == a[a.Length - 1];
	assert a[a.Length-1] == a[a.Length-1];
	//alternation 4.1
	if(a[a.Length-1] > 0){
		p := a[a.Length-1];
		assert p == a[a.Length-1] && a[a.Length-1] > 0;
		i,s,p,c := SPC1c0(a,key,i,s,p); // check c if  p == a[a.Length-1]
	}
	else{
		p:=1;
		assert p == 1 && a[a.Length-1] <= 0;
		i,s,p,c := SPC1c1(a,key,i,s,p); // check c if p == 1
	}
	assert Inv(a,key,i,s,p,c) && i == 0;
}

// p == a[a.length]
method SPC1c0(a: array<int> ,key: int,i0: nat ,s0: int,p0: int) returns (i: nat ,s: int , p: int , c: nat)
	requires a != null &&  0 < a.Length
	requires 0 < a[a.Length-1]
	requires p0 == a[a.Length-1]
	requires i0 == a.Length-1
	requires s0 == a[a.Length-1]
	requires a[a.Length-1] > 0
	ensures Inv(a,key,i,s,p,c) && i == 0
{
	i,s,p := i0,s0,p0;
	assert a != null &&  0 < a.Length;
	assert 0 < a[a.Length-1];
	assert p == a[a.Length-1];
	assert i == a.Length-1;
	assert s == a[a.Length-1] ;
	//alternation 4.1
	assert a[a.Length-1] == a[a.Length-1];
	if(a[a.Length-1] == key ){
		c := 1;
		assert c==1;
		assert a != null &&  0 < a.Length;
		assert 0 < a[a.Length-1];
		assert p == a[a.Length-1];
		assert i == a.Length-1;
		assert s == a[a.Length-1] ;
		i,s,p,c := SPC2c(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}
	else{
		c:=0;
		assert c == 0;
		assert a != null &&  0 < a.Length;
		assert 0 < a[a.Length-1];
		assert p == a[a.Length-1];
		assert i == a.Length-1;
		assert s == a[a.Length-1] ;
		i,s,p,c := SPC2d(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}
	assert Inv(a,key,i,s,p,c) && i == 0;
}


// p == 1
method SPC1c1(a: array<int> ,key: int,i0: nat ,s0: int,p0: int) returns (i: nat ,s: int , p: int , c: nat)
	requires a != null &&  0 < a.Length
	requires 0 >= a[a.Length-1]
	requires p0 == 1
	requires i0 == a.Length-1
	requires s0 == a[a.Length-1]
	ensures Inv(a,key,i,s,p,c) && i == 0
{
	i,s,p := i0,s0,p0;
	assert a != null &&  0 < a.Length;
	assert 0 >= a[a.Length-1];
	assert p == 1;
	assert i == a.Length-1;
	assert s == a[a.Length-1] ;
	//alternation 4.1
	assert a[a.Length-1] == a[a.Length-1];
	if(a[a.Length-1] == key ){
		c := 1;
		assert c==1;
		assert a != null &&  0 < a.Length;
		assert 0 >= a[a.Length-1];
		assert p == 1;
		assert i == a.Length-1;
		assert s == a[a.Length-1] ;
		i,s,p,c := SPC2a(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}
	else{
		c:=0;
		assert c == 0;
		assert a != null &&  0 < a.Length;
		assert 0 >= a[a.Length-1];
		assert p == 1;
		assert i == a.Length-1;
		assert s == a[a.Length-1] ;
		i,s,p,c := SPC2b(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}
	assert Inv(a,key,i,s,p,c) && i == 0;
}

	

method initS(a: array<int>) returns (s: int)
	requires  a != null &&  0 < a.Length
	requires a[a.Length-1] == a[a.Length-1]
	ensures s == a[a.Length-1]
{
	//assignment 1.3
	assert a != null &&  0 < a.Length;
	assert a[a.Length-1] == a[a.Length-1];
	s := a[a.Length-1];
	assert s == a[a.Length-1];
}

method initP(a: array<int>) returns (p: int)
	requires  a != null &&  0 < a.Length
	requires a[a.Length-1] == a[a.Length-1]
	ensures p == a[a.Length-1] || p == 1
{
	//alternation 4.1
    assert a != null &&  0 < a.Length;
	assert a[a.Length-1] == a[a.Length-1];
	if(a[a.Length-1] > 0){
		p := a[a.Length-1];
	}
	else{
		p:=1;
	}
	assert p == a[a.Length-1] || p == 1;
}

method initC(a: array<int> , key: int) returns (c: nat)
	requires  a != null &&  0 < a.Length
	requires a[a.Length-1] == a[a.Length-1]
	ensures c <= 1
{
	//alternation 4.1
	assert  a != null &&  0 < a.Length;
	assert a[a.Length-1] == a[a.Length-1];
	if(a[a.Length-1] == key ){
		c := 1;
	}
	else{
		c:=0;
	}
	assert c <= 1;
}

// a: step 2 for p==1 && c==1
method SPC2a(a: array<int> ,key: int,i0: nat ,s0: int , p0: int , c0: nat) returns (i: nat ,s: int , p: int , c: nat)
	requires  a != null &&  0 < a.Length
	requires key == a[a.Length-1];
	requires 0 >= a[a.Length-1]
	requires i0 == a.Length-1
	requires s0 == a[a.Length - 1]
	requires p0 ==1 
	requires c0 == 1
	ensures Inv(a,key,i,s,p,c) && i == 0
	{
		i,s,p,c := i0,s0,p0,c0;
		// Step3: weaken preCond 1.2
		assert  a != null &&  0 < a.Length;
		assert key == a[a.Length-1];
		assert 0 >= a[a.Length-1];
		assert i == a.Length-1;
		assert s == a[a.Length - 1];
		assert p ==1; 
		assert c == 1;
		L3a(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c);
		i,s,p,c := SPC3(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}

// b: step 2 for p==1 && c==0
method SPC2b(a: array<int> ,key: int,i0: nat ,s0: int , p0: int , c0: nat) returns (i: nat ,s: int , p: int , c: nat)
	requires  a != null &&  0 < a.Length
	requires 0 >= a[a.Length-1]
	requires key != a[a.Length-1]
	requires i0 == a.Length-1
	requires s0 == a[a.Length - 1]
	requires p0 ==1 
	requires c0 == 0
	ensures Inv(a,key,i,s,p,c) && i == 0
	{
		i,s,p,c := i0,s0,p0,c0;
		// Step3: weaken preCond 1.2
		assert  a != null &&  0 < a.Length;
		assert key != a[a.Length-1];
		assert 0 >= a[a.Length-1];
		assert i == a.Length-1;
		assert s == a[a.Length - 1];
		assert  p ==1; 
		assert c == 0;
		L3b(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c);
		i,s,p,c := SPC3(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}

// c: step 2 for p==a[a.Length-1] && c==1
method SPC2c(a: array<int> ,key: int,i0: nat ,s0: int , p0: int , c0: nat) returns (i: nat ,s: int , p: int , c: nat)
	requires  a != null &&  0 < a.Length
	requires 0 < a[a.Length-1]
	requires key == a[a.Length-1]
	requires i0 == a.Length-1
	requires s0 == a[a.Length - 1]
	requires p0 == a[a.Length-1] 
	requires c0 == 1
	ensures Inv(a,key,i,s,p,c) && i == 0
	{
		i,s,p,c := i0,s0,p0,c0;
		// Step3: weaken preCond 1.2
		assert  a != null &&  0 < a.Length;
		assert 0 < a[a.Length-1];
		assert key == a[a.Length-1];
		assert i == a.Length-1;
		assert s == a[a.Length - 1];
		assert p == a[a.Length-1]; 
		assert c == 1;
		L3c(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c);
		i,s,p,c := SPC3(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}

// d: step 2 for p==a[a.Length-1] && c==0
method SPC2d(a: array<int> ,key: int,i0: nat ,s0: int , p0: int , c0: nat) returns (i: nat ,s: int , p: int , c: nat)
	requires  a != null &&  0 < a.Length
	requires i0 == a.Length-1
	requires s0 == a[a.Length - 1]
	requires p0 == a[a.Length-1]
	requires c0 == 0
	requires key != a[a.Length-1]
	requires 0 < a[a.Length-1]
	ensures Inv(a,key,i,s,p,c) && i == 0
	{
		i,s,p,c := i0,s0,p0,c0;
		// Step3: weaken preCond 1.2
		assert  a != null &&  0 < a.Length;
		assert i == a.Length-1;
		assert s == a[a.Length - 1];
		assert p == a[a.Length-1]; 
		assert c == 0 && p == a[a.Length-1] && s == a[a.Length - 1] && i == a.Length-1;
		assert key != a[a.Length-1];
		assert 0 < a[a.Length-1];
		L3d(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c);
		i,s,p,c := SPC3(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && i == 0;
	}

//lemma for p == 1 && c == 1
lemma L3a(a: array<int> ,key: int,i: nat ,s: int , p: int , c: nat )
	requires  a != null &&  0 < a.Length
	requires 0 >= a[a.Length-1]
	requires key == a[a.Length-1]
	requires i == a.Length-1
	requires s == a[a.Length - 1]
	requires p ==1;
	requires c == 1
	ensures Inv(a,key,i,s,p,c)
	{}
	
//lemma for p == 1 && c == 0
lemma L3b(a: array<int> ,key: int,i: nat ,s: int , p: int , c: nat )
	requires  a != null &&  0 < a.Length
	requires 0 >= a[a.Length-1]
	requires key != a[a.Length-1]
	requires i == a.Length-1
	requires s == a[a.Length - 1]
	requires p ==1;
	requires c==0
	ensures Inv(a,key,i,s,p,c)
	{}

//lemma for p == a[a.Length - 1] && c == 1
lemma L3c(a: array<int> ,key: int,i: nat ,s: int , p: int , c: nat )
	requires  a != null &&  0 < a.Length
	requires 0 < a[a.Length-1]
	requires key == a[a.Length-1]
	requires i == a.Length-1
	requires s == a[a.Length - 1]
	requires p == a[a.Length-1]
	requires c == 1
	ensures Inv(a,key,i,s,p,c)
	{}
	
//lemma for p == a[a.Length - 1] && c == 0
lemma L3d(a: array<int> ,key: int,i: nat ,s: int , p: int , c: nat )
	requires  a != null &&  0 < a.Length
	requires i == a.Length-1
	requires key != a[a.Length-1]
	requires 0 < a[a.Length-1]
	requires s == a[a.Length - 1]
	requires p == a[a.Length-1]
	requires c==0
	ensures Inv(a,key,i,s,p,c)
	{}
	//SPC3 --> STEP4 ITERATION

method SPC3(a: array<int> ,key: int,i0: nat ,s0: int , p0: int , c0: nat) returns (i: nat ,s: int , p: int , c: nat)
	requires Inv(a,key,i0,s0,p0,c0)
	ensures Inv(a,key,i,s,p,c) && i == 0
{
	i,s,p,c := i0,s0,p0,c0;
	//Step 4 : iteration 5.5
	assert Inv(a,key,i,s,p,c);
	while(i != 0 )
		invariant Inv(a,key,i,s,p,c)
		decreases i
	{
		ghost var i1: nat := i;
		assert Inv(a,key,i,s,p,c) && i != 0 && i == i1;
		i,s,p,c := SPC4(a,key,i,s,p,c);
		assert Inv(a,key,i,s,p,c) && 0 <= i < i1 <= a.Length;
	}
	assert Inv(a,key,i,s,p,c) && i == 0;
}


method SPC4(a: array<int> ,key: int,i0: nat ,s0: int , p0: int , c0: nat) returns (i: nat ,s: int , p: int , c: nat)
	requires Inv(a,key,i0,s0,p0,c0) && i0 != 0
	ensures Inv(a,key,i,s,p,c) && 0 <= i < i0 <= a.Length
{
	i,s,p,c := i0,s0,p0,c0;
	// step 5: following assignment 3.5
	assert Inv(a,key,i,s,p,c) && i != 0 ;
	i,s,p,c := SPC5(a,key,i,s,p,c);
	assert Inv(a,key,i-1,s,p,c) && 0 <= i - 1 < i0 <= a.Length;
	i := i - 1;
	assert Inv(a,key,i,s,p,c) && 0 <= i < i0 <= a.Length;
}


method SPC5(a: array<int> ,key: int,i0: nat ,s0: int , p0: int , c0: nat) returns (i: nat ,s: int , p: int , c: nat)
	requires Inv(a,key,i0,s0,p0,c0) && i0 != 0
	ensures  i0 == i && Inv(a,key,i-1,s,p,c) && 0 <= i - 1 < i0 <= a.Length
{
	i,s,p,c := i0,s0,p0,c0;
	// Step 6: contract frame 5.4
	assert Inv(a,key,i,s,p,c) && i != 0 && i0 == i && i>0 ;
	s,p,c := SPC6(a,key,i,s,p,c);
	assert  i > 0 && Inv(a,key,i-1,s,p,c) && 0 <= i - 1 < i0 <= a.Length;
}

method SPC6(a: array<int> ,key: int,i: nat ,s0: int , p0: int , c0: nat) returns (s: int , p: int , c: nat)
	requires Inv(a,key,i,s0,p0,c0) && i != 0
	ensures Inv(a,key,i-1,s,p,c) && 0 <= i - 1 < i <= a.Length
{
	s,p,c := s0,p0,c0;
	// Step 7 : strengthen postCond 5.1
	assert Inv(a,key,i,s,p,c) && i != 0;
	s,p,c := SPC7(a,key,i,s,p,c);
	assert Inv(a,key,i-1,s,p,c);
	assert i != 0;
	L7(a,key,i,s,p,c);
	assert Inv(a,key,i-1,s,p,c) && 0 <= i - 1 < i <= a.Length;
}
//a key i c 
method SPC7(a: array<int> ,key: int,i: nat ,s0: int , p0: int , c0: nat) returns (s: int , p: int , c: nat)
	requires Inv(a,key,i,s0,p0,c0) && i != 0
	ensures Inv(a,key,i-1,s,p,c)
{
	s,p,c := s0,p0,c0;
	//step 8 : contract frame 5.4
	assert Inv(a,key,i,s,p,c) && i != 0 ;

	assert InvSum(a,i,s);
	s:= calcS(a,i,s);
	assert InvSum(a,i-1,s);

	assert InvProduct(a,i,p);
	p:= calcP(a,i,p);
	assert InvProduct(a,i-1,p);

	assert InvCount(a,key,i,c);
	c:= calcC(a,key,i,c);
	assert InvCount(a,key,i-1,c);

	assert Inv(a,key,i-1,s,p,c);
}



lemma L7(a: array<int> ,key: int,i: nat ,s: int , p: int , c: nat)
	requires i != 0 
	requires Inv(a,key,i-1,s,p,c)
	ensures Inv(a,key,i-1,s,p,c) 
	{}
	


	method calcS(a: array<int>, i: nat , s0: int) returns (s: int)
	requires InvSum(a,i,s0) && i != 0
	ensures	InvSum(a,i-1,s)
{
	//assignment 1.3
	assert InvSum(a,i,s0) && i != 0 ;
	s := s0 + a[i-1];
	assert s == s0 + a[i-1];
}

method calcP(a: array<int>, i: nat , p0: int) returns (p: int)
	requires  i != 0 &&  InvProduct(a,i,p0);
	ensures InvProduct(a,i-1,p)
{
	//alternation 4.1
    assert i != 0 &&  InvProduct(a,i,p0);
	if(a[i-1] > 0){
		p := p0 * a[i-1];
		assert p == p0 * a[i-1];
	}
	else{
		p:=p0;
		assert p == p0;
	}
	assert InvProduct(a,i-1,p);
}

method calcC(a: array<int> , key: int, i: nat , c0: nat) returns (c: nat)
	requires  i != 0 &&  InvCount(a,key,i,c0)
	ensures InvCount(a,key,i-1,c)
{
	//alternation 4.1
	assert  i != 0 &&  InvCount(a,key,i,c0);
	if(a[i-1] == key ){
		c := c0 + 1;
		assert c == c0 + 1;
	}
	else{
		c := c0;
		assert c == c0;
	}
	assert InvCount(a,key,i-1,c);
}