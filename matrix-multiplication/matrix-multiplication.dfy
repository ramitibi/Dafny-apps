method Main()
{
	var m1: array2<int>, m2: array2<int>, m3: array2<int>;
	m1 := new int[2,3];
	m2 := new int[3,1];
	m1[0,0] := 1; m1[0,1] := 2; m1[0,2] := 3;
	m1[1,0] := 4; m1[1,1] := 5; m1[1,2] := 6;
	m2[0,0] := 7;
	m2[1,0] := 8;
	m2[2,0] := 9;
	m3 := Multiply(m1, m2);
	PrintMatrix(m1);
	print "\n*\n";
	PrintMatrix(m2);
	print "\n=\n";
	PrintMatrix(m3);
}

method PrintMatrix(m: array2<int>)
	requires m != null
{
	var i: nat := 0;
	while (i < m.Length0)
	{
		var j: nat := 0;
		print "\n";
		while (j < m.Length1)
		{
			print m[i,j];
			print "\t";
			j := j + 1;
		} 
		i := i + 1;
	} 
	print "\n";
}

predicate canMultiply(m1: array2<int>, m2: array2<int>, m3: array2<int>){
	m1 != null && m2 != null && m1.Length1 == m2.Length0  &&
	m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1 &&
	m1.Length0 > 0 && m1.Length1 > 0 && m2.Length0 > 0 && m2.Length1 > 0
}

predicate canMultiplyNoM3(m1: array2<int>, m2: array2<int>){
	m1 != null && m2 != null && m1.Length1 == m2.Length0  &&
	m1.Length0 > 0 && m1.Length1 > 0 && m2.Length0 > 0 && m2.Length1 > 0
}

predicate MM(m1: array2<int>, m2: array2<int>, m3: array2<int>)
{ 
	m1 != null && m2 != null && m3 != null &&
	m1.Length1 == m2.Length0 && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1 &&
	forall i,j :: 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ==> m3[i,j] == RowColumnProduct(m1,m2,i,j)
}

function RowColumnProduct(m1: array2<int>, m2: array2<int>, row: nat, column: nat): int
	requires m1 != null && m2 != null && m1.Length1 == m2.Length0
	requires row < m1.Length0 && column < m2.Length1 
{
	RowColumnProductFrom(m1, m2, row, column, 0)
}

function RowColumnProductFrom(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat): int
	requires m1 != null && m2 != null && k <= m1.Length1 == m2.Length0
	requires row < m1.Length0 && column < m2.Length1
	decreases m1.Length1 - k
{
	if k == m1.Length1 then 0 else m1[row,k]*m2[k,column] + RowColumnProductFrom(m1, m2, row, column, k+1)
}

function RowColumnProductFromBack(m1: array2<int>, m2: array2<int>, row: nat, column: nat, n:nat): int
    requires canMultiplyNoM3(m1, m2)
    requires row < m1.Length0 && column < m2.Length1 && n <= m1.Length1
{
  if n == 0 then 0 else
    RowColumnProductFromBack(m1, m2, row, column, n-1) + m1[row,n-1]*m2[n-1,column] 
}


predicate LoopRow(m1: array2<int>, m2: array2<int>, m3: array2<int>, row:nat)
  requires canMultiply(m1, m2, m3)
  requires row <= m1.Length0 
{ 
    forall i:nat,j:nat :: i < row && j < m2.Length1 ==> m3[i,j] == RowColumnProductFromBack(m1,m2,i,j,m1.Length1)
}


method Multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
	requires m1 != null && m2 != null
	requires m1.Length0 > 0 && m1.Length1 > 0 && m2.Length0 > 0 && m2.Length1 > 0
	requires m1.Length1 == m2.Length0
	
	ensures MM(m1, m2, m3)
{
	m3 := new int[m1.Length0, m2.Length1];
	assert m1 != null && m2 != null && m3 != null;
	assert m1.Length1 == m2.Length0 && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1;
	// TODO: continue here, multiplying m1 by m2 placing the result in m3 such that MM(m1, m2, m3) will become true

	//strengthen postCond 1.1 and introduce local var 6.1
	var row:nat :=0;
	assert row == 0;

	//iteration 5.5
	while(row != m1.Length0)
		invariant row <= m1.Length0
		invariant LoopRow(m1,m2,m3,row)
		decreases m1.Length0 - row
	{
		ghost var row0 := row;
		assert row0 == row;
		assert row <= m1.Length0 && LoopRow(m1,m2,m3,row) && row != m1.Length0;

		secondLoop(m1,m2,m3,row);
		assert ColmLoop(m1,m2,m3,row,m2.Length1);

		calc{
		LoopRow(m1,m2,m3,row);
		==
			forall i:nat,j:nat :: i < row && j < m2.Length1 ==> m3[i,j] == RowColumnProductFromBack(m1,m2,i,j,m1.Length1);
		==>
			ColmLoop(m1,m2,m3,row,m2.Length1);
		==
			forall c:nat :: c < m2.Length1 ==> m3[row,c] == RowColumnProductFromBack(m1,m2,row,c,m1.Length1);
		==>			 
			LoopRow(m1,m2,m3,row+1);			
		}
		assert LoopRow(m1,m2,m3,row+1);
		//following assignment 3.5 
		row:= row + 1;
		assert m1.Length0 - row0 > m1.Length0 - row;
		assert row <= m1.Length0 && LoopRow(m1,m2,m3,row);
	}
	assert row == m1.Length0;
	assert LoopRow(m1,m2,m3,m1.Length0);

	matrixRows(m1,m2,m3);

	assert MM(m1, m2, m3);
}


lemma matrixRows(m1: array2<int>, m2: array2<int>, m3: array2<int>)
   requires canMultiply(m1,m2,m3)
   requires LoopRow(m1, m2, m3, m1.Length0)
   ensures MM(m1, m2, m3)
{
    assert forall r:nat,c:nat :: r < m1.Length0 && c < m2.Length1 ==> m3[r,c] == RowColumnProductFromBack(m1,m2,r,c,m1.Length1);

    forall r:nat,c:nat | r < m1.Length0 && c < m2.Length1
      ensures m3[r,c] == RowColumnProduct(m1,m2,r,c)
    {
      assert m3[r,c] == RowColumnProductFromBack(m1,m2,r,c,m1.Length1);
      matrixRows2(m1, m2, m3, r, c);  
    }
 
    assert forall r:nat,c:nat :: r < m3.Length0 && c < m3.Length1 ==> m3[r,c] == RowColumnProduct(m1,m2,r,c); 
}   


lemma matrixRows2(m1: array2<int>, m2: array2<int>, m3: array2<int>, r:nat, c:nat)
   requires canMultiply(m1,m2,m3)
   requires r < m1.Length0 && c < m2.Length1;
   requires m3[r,c] == RowColumnProductFromBack(m1,m2,r,c,m1.Length1)
   ensures m3[r,c] == RowColumnProduct(m1,m2,r,c)
{
  assert RowColumnProduct(m1,m2,r,c) == RowColumnProductFrom(m1,m2,r,c,0);
 
  var i:nat := 0;
  var total := RowColumnProductFromBack(m1,m2,r,c,m1.Length1);
  while i < m1.Length1
     invariant i <= m1.Length1
     invariant total == RowColumnProductFromBack(m1,m2,r,c,m1.Length1-i) + RowColumnProductFrom(m1,m2,r,c,m1.Length1-i)
  {
    i := i+1;
  }
}

predicate ColmLoop(m1: array2<int>, m2: array2<int>, m3: array2<int>,row:nat,colm:nat)
  requires canMultiply(m1, m2, m3)
  requires row < m1.Length0 && colm <= m2.Length1  
{ 
    forall c:nat :: c < colm ==> m3[row,c] == RowColumnProductFromBack(m1,m2,row,c,m1.Length1)
}


method secondLoop(m1: array2<int>, m2: array2<int>, m3: array2<int>, row:nat)
	requires canMultiply(m1, m2, m3)
	requires  row < m1.Length0
	modifies m3
	ensures ColmLoop(m1,m2,m3,row,m2.Length1)
{
	//introduce local var 
	var colm:nat :=0;
	assert colm == 0 && colm < m2.Length1;
	assert canMultiply(m1, m2, m3) && row <= m1.Length0;
	
	//iteration 5.5
	while(colm != m2.Length1)
		invariant colm <= m2.Length1
		invariant ColmLoop(m1,m2,m3,row,colm)
		decreases m2.Length1 - colm
	{
		ghost var colm1:= colm;
		assert colm == colm1;
		assert colm <= m2.Length1 && ColmLoop(m1,m2,m3,row,colm) && colm != m2.Length1;

		thirdLoop(m1,m2,m3,row,colm);
		assert m3[row,colm] == RowColumnProductFromBack(m1,m2,row,colm,m1.Length1);

		calc{
			m3[row,colm] == RowColumnProductFromBack(m1,m2,row,colm,m1.Length1);
		==>
			ColmLoop(m1,m2,m3,row,colm);
		==> 
			ColmLoop(m1,m2,m3,row,colm + 1);
		}
		assert ColmLoop(m1,m2,m3,row,colm+1);
		
		//following assignment 3.5
		colm := colm + 1;
		assert m2.Length1 - colm1 > m2.Length1 - colm;
		assert ColmLoop(m1,m2,m3,row,colm);
	}
	assert colm ==  m2.Length1;
	assert ColmLoop(m1,m2,m3,row,m2.Length1);

}




predicate LoopI(m1: array2<int>, m2: array2<int>, m3: array2<int>,row:nat,colm:nat,n:nat)
   requires canMultiply(m1, m2, m3)
   requires row < m1.Length0 && colm < m2.Length1 && n<=m1.Length1
{ 
   m3[row,colm] == RowColumnProductFromBack(m1, m2, row, colm, n)
}


method thirdLoop(m1: array2<int>, m2: array2<int>, m3: array2<int>,row:nat,colm:nat)
	requires canMultiply(m1, m2, m3)
	requires  row < m1.Length0
	requires colm < m2.Length1
	modifies m3
	ensures forall x :: x < m1.Length1 ==> LoopI(m1,m2,m3,row,colm,m1.Length1)
	ensures  m3[row,colm] == RowColumnProductFromBack(m1,m2,row,colm,m1.Length1)

{

	//introduce local var 6.1
	var i: nat :=0;
	assert i == 0;
	assert canMultiply(m1, m2, m3) && row < m1.Length0 && colm < m2.Length1;

	//assignment 1.3
	m3[row,colm] := 0;

	//iteration 5.5
	while( i != m1.Length1 )
		invariant i <= m1.Length1
		invariant LoopI(m1,m2,m3,row,colm,i)
		decreases m1.Length1 - i
	{
		ghost var i1 := i;
		assert i1 == i;
		assert  i != m1.Length1 && i < m1.Length1 && LoopI(m1,m2,m3,row,colm,i);

		multiplyI(m1,m2,m3,row,colm,i);
		assert LoopI(m1,m2,m3,row,colm,i+1);

		//following assignment 3.5
		i := i + 1;
		assert m1.Length1 - i1 > m1.Length1 - i;
		assert i <= m1.Length1 && LoopI(m1,m2,m3,row,colm,i);
	}
	assert i == m1.Length1;
	assert LoopI(m1,m2,m3,row,colm,m1.Length1);

	thirdToSecond(m1,m2,m3,row,colm);

	assert m3[row,colm] == RowColumnProductFromBack(m1,m2,row,colm,m1.Length1);

}

lemma thirdToSecond(m1: array2<int>, m2: array2<int>, m3: array2<int>, row:nat, colm:nat)
	requires canMultiply(m1, m2, m3)
	requires  row < m1.Length0
	requires colm < m2.Length1 
	requires  LoopI(m1,m2,m3,row,colm,m1.Length1)
	ensures  m3[row,colm] == RowColumnProductFromBack(m1,m2,row,colm,m1.Length1);
{

	calc{
		LoopI(m1,m2,m3,row,colm,m1.Length1);
	==>
		m3[row,colm] == RowColumnProductFromBack(m1, m2, row, colm, m1.Length1);
	}

}

method multiplyI(m1: array2<int>, m2: array2<int>, m3: array2<int>, row:nat, colm:nat, i:nat)
	requires canMultiply(m1, m2, m3)
	requires  row < m1.Length0
	requires colm < m2.Length1
	requires  i < m1.Length1
	requires LoopI(m1,m2,m3,row,colm,i)
	modifies m3
    ensures LoopI(m1,m2,m3,row,colm,i+1)
	{
		//assignment 1.3
		assert LoopI(m1,m2,m3,row,colm,i);
		m3[row,colm] := m3[row,colm] + (m1[row,i] * m2[i,colm]);

		calc{
			LoopI(m1,m2,old(m3),row,colm,i);
		==
			old(m3[row,colm]) == RowColumnProductFromBack(m1, m2, row, colm, i);
		==>
			m3[row,colm] == old(m3[row,colm]) + (m1[row,i] * m2[i,colm])
		==>
			 m3[row,colm] == RowColumnProductFromBack(m1, m2, row, colm, i+1);
		==
			LoopI(m1,m2,m3,row,colm,i+1);
		}
		assert LoopI(m1,m2,m3,row,colm,i+1);
	}