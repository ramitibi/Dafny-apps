method Main() 
{
     // intro local var - 6.1
     var a := new int[6]; // 3 element array of ints
	 var p :nat;
     a[0], a[1], a[2], a[3], a[4], a[5] := 8, 6, 4 , 10 ,-2 ,7;
     qSort(a);

     print a[0];
	 print " ";
	 print a[1];
	 print " ";
	 print a[2];
	 print " ";
     print a[3];
	 print " ";
     print a[4];
	 print " ";
     print a[5];
     
}


predicate Sorted(a: array<int>)
	requires a != null
	requires a.Length > 0
	reads a
{
	Sorted2(a,0,a.Length - 1)
}



method qSort(a: array<int>)
requires a != null
requires a.Length > 0
modifies a
ensures Sorted(a)
{
	quickSort(a,0,a.Length - 1);
}

predicate Sorted2(a: array<int>, from: nat, to: nat)
	requires a != null
	requires from <= a.Length
	reads a
{
	forall i,j: nat :: from <= i < j <= to < a.Length ==> a[i] <= a[j]
}



method quickSort(a: array<int>, lo: nat, hi: nat)
	requires a != null
	requires 0 <= lo <= hi < a.Length
	requires 0 <= lo <= hi < a.Length-1 ==> forall j :: lo <= j <= hi ==> a[j] <= a[hi +1];
    requires 0 < lo <= hi <= a.Length-1 ==> forall j :: lo <= j <= hi ==> a[lo - 1] <= a[j];
	modifies a
	ensures Sorted2(a,lo,hi)
	ensures 0 <= lo <= hi < a.Length-1 ==> forall j :: lo <= j <= hi ==> a[j] <= a[hi +1];
    ensures 0 < lo <= hi <= a.Length-1 ==> forall j :: lo <= j <= hi ==> a[lo - 1] <= a[j];
    ensures forall x :: 0 <= x < lo || hi < x < a.Length ==> a[x] == old(a[x])
	decreases hi - lo
{
	
	//alternation 4.1
	if( hi > lo){
		var p:= Partition(a,lo,hi);
		//check if the pivot is equal to lo or hi or between them
		//alternaion 4.1	
		if( p == lo)
		{
			quickSort(a,p+1,hi);
		}
		else
		{
			//alteranation 4.1
			if( p == hi )
			{
				quickSort(a,lo,p-1);
			}
			else
			{
				quickSort(a,lo,p-1);
				assert Sorted2(a,lo,p-1);
				quickSort(a,p+1,hi);
				assert Sorted2(a,p+1,hi);
			}
		}
	    
				
	}

}



predicate Swapped(q0: seq<int>, q1: seq<int>, i: nat, j: nat)
	requires 0 <= i < |q0| == |q1|
	requires 0 <= j < |q1|
{
	q0[i] == q1[j] && q0[j] == q1[i] && (forall k :: 0 <= k < |q0| && k != i && k != j ==> q0[k] == q1[k])
}

method Swap(a: array<int>, i: nat, j: nat)
	requires a != null
	requires 0 <= i < a.Length
	requires 0 <= j < a.Length
	modifies a
	ensures Swapped(a[..], old(a[..]), i, j)
{
	a[i], a[j] := a[j], a[i];
	assert Swapped(a[..], old(a[..]), i, j);
}


method Partition(a: array<int>, lo: nat, hi: nat) returns (pivot: nat)
	requires a!=null && 0 < a.Length 
	requires 0 <= lo <= hi < a.Length
	requires 0 <= lo <= hi < a.Length-1 ==> forall j :: lo <= j <= hi ==> a[j] <= a[hi +1];
    requires 0 < lo <= hi <= a.Length-1 ==> forall j :: lo <= j <= hi ==> a[lo - 1] <= a[j];
	modifies a
	ensures 0 <= lo <= pivot <= hi < a.Length
    ensures forall x :: lo <= x < pivot ==> a[x] <= a[pivot]
    ensures forall x ::  pivot < x <= hi ==> a[x] >= a[pivot]
	ensures forall x :: 0 <= x < lo || hi < x < a.Length ==> a[x] == old(a[x])
	ensures 0 <= lo <= hi < a.Length -1==> forall j :: lo <= j <= hi ==> a[j] <= a[hi +1];
    ensures 0 < lo <= hi <= a.Length-1 ==> forall j :: lo <= j <= hi ==> a[lo - 1] <= a[j];
{ 
	pivot := lo;
	//introduce local var 6.1 + assignment 1.3
	var j:nat := lo;
	assert j==lo && pivot == lo;
	assert a!=null && 0 < a.Length && 0 <= lo <= hi < a.Length;

	//iteration 5.5
	while(j < hi)
		invariant lo <= pivot <= j <= hi
	    invariant  forall x :: lo <= x < pivot ==> a[x] <= a[hi] 
		invariant forall x :: pivot <= x < j ==> a[x] >= a[hi]
		invariant forall x :: 0 <= x < lo || hi < x < a.Length ==> a[x] == old(a[x])
		invariant 0 <= lo <= hi < a.Length-1 ==> forall j :: lo <= j <= hi ==> a[j] <= a[hi +1];
		invariant 0 < lo <= hi <= a.Length-1 ==> forall j :: lo <= j <= hi ==> a[lo - 1] <= a[j];
		decreases hi - j
	{
		assert j < hi;
	    ghost var j1:nat;
		j1 := j;
		assert j == j1;
		if(a[j] <= a[hi]){
			Swap(a,pivot,j);
			//assignment 1.3
			pivot := pivot + 1;
			//following assignment 3.5
			j := j + 1;
			
		}
		else{//skip command 3.2
			assert a[j] > a[hi];
			//following assignment 3.5
			j := j + 1;
			assert a[j-1] > a[hi];
		} 
		assert forall x :: lo <= x < pivot ==> a[x] <= a[hi] ;
		assert forall x :: pivot <= x < j ==> a[x] >= a[hi];
		assert hi - j1 > hi - j;
	}
	assert j == hi;
	Swap(a,hi,pivot);

	assert forall x :: pivot <= x < hi ==> a[x] >= a[pivot];
	assert forall x :: lo <= x < pivot ==> a[x] <= a[pivot];

    assert forall x :: lo <= x < pivot <= hi ==> a[x] <= a[pivot];
    assert forall x :: lo <= pivot < x <= hi ==> a[x] >= a[pivot];
}