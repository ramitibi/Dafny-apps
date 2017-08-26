// Source: Carroll Morgan's "Programming from Specifications", Second edition, Exercise 15.17

// Consider the binary tree type:
datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)
// The frontier of such a tree is the sequence of tip-values in left-to-right order.
// Your assignment is to develop iterative code that "prints" the frontier of a given tree
// using the "Output" method of the following "IO" class
class IO<T> {
	var alpha: seq<T>, omega: seq<T>;

	method Input() returns (x: T)
		requires !EOF() //alpha != []
		modifies this
		ensures omega == old(omega)
		ensures old(alpha) == [x] + alpha
	{
		x, alpha := alpha[0], alpha[1..];
	}

	method Output(x: T)
		modifies this
		ensures alpha == old(alpha)
		ensures omega == old(omega) + [x]
	{
		omega := omega + [x];
	}

	method Rewrite()
		modifies this
		ensures omega == []
		ensures alpha == old(alpha)
	{
		omega := [];
	}

	predicate method EOF() reads this { alpha == [] }

}

method Main()
{
	var tree: BT<int>;
	tree := Tip(1);
	var io: IO<int>;
	io := new IO<int>;
	io.Rewrite();
	assert |io.omega| == 0;
	FrontierIter(tree, io);
	print io.omega;

	io.Rewrite();
	tree := Node(tree, Tip(2));
	FrontierIter(tree, io);
	print io.omega;
}

function Frontier(tree: BT<T>): seq<T>
{
	match tree {
		case Tip(n) => [n]
		case Node(left, right) => Frontier(left) + Frontier(right)
	}
}

function SumSequenceOfTrees(ntl: seq<BT<T>>): seq<T>
{
	if (ntl == []) then [] else Frontier(ntl[0]) + SumSequenceOfTrees(ntl[1..])
}


method FrontierIter(tree: BT<T>, io: IO<T>)
	requires io != null
	requires |io.omega| == 0
	modifies io
	ensures io.omega == old(io.omega) + Frontier(tree)
{
	var stack: seq<BT<T>>;
	stack := [tree];
	

	//itroduce local var 6.1 + strengthn post cond 1.1
	var temp:seq<T>:=[];
	
	//iteration 5.5
	while(stack != [] )
		invariant temp + SumSequenceOfTrees(stack) == SumSequenceOfTrees([tree])
		decreases SizeOfTreeSequence(stack);
	{	
		ghost var stack2:= stack;
		ghost var temp2:= temp;
		assert stack2 == stack && temp == temp2 && temp + SumSequenceOfTrees(stack) == SumSequenceOfTrees([tree]) && stack != [];
		//alternation 4.1 + contract frame 5.2
		match stack[0]{
			case Tip(n) =>
			//assignment 1.3
				temp := temp + [n];
				assert temp == temp2 + [n];
				
				calc
				{
					temp == temp2 + [n];
				==>
					Tip(n) == stack[0];
				==>
					SumSequenceOfTrees([stack[0]]) == [n];
				==>
					temp2 + SumSequenceOfTrees(stack) == SumSequenceOfTrees([tree]);
				==>
					temp2 + SumSequenceOfTrees([stack[0]]) + SumSequenceOfTrees(stack[1..]) == SumSequenceOfTrees([tree]);
				==>
					temp2 + [n] + SumSequenceOfTrees(stack[1..]) == SumSequenceOfTrees([tree]); 
				==> 
					temp + SumSequenceOfTrees(stack[1..]) == SumSequenceOfTrees([tree]);
				}
				//following assignment 3.5
				stack := stack[1..];
				assert temp + SumSequenceOfTrees(stack) == SumSequenceOfTrees([tree]);

			case Node(t1,t2) =>
				assert temp == temp2;
				ghost var seq2 := [t1,t2];
				assert seq2 == [t1,t2];
				//prove that SumSequenceOfTrees(stack) == SumSequenceOfTrees([t1,t2] + stack[1..])
				calc
				{
					SumSequenceOfTrees([t2] + stack[1..]) == Frontier(t2) + SumSequenceOfTrees(stack[1..]);
				==>
					Frontier(t1) + SumSequenceOfTrees([t2] + stack[1..]) == Frontier(t1) +  Frontier(t2) + SumSequenceOfTrees(stack[1..]);
				==>
					SumSequenceOfTrees([t1,t2] + stack[1..]) == Frontier(t1) + SumSequenceOfTrees([t2] + stack[1..]) ;
				==>
					SumSequenceOfTrees([t1,t2] + stack[1..]) == Frontier(t1) +  Frontier(t2) + SumSequenceOfTrees(stack[1..]);
				==>
					SumSequenceOfTrees(stack) == Frontier(stack[0]) + SumSequenceOfTrees(stack[1..]);
				==>
					stack[0] == Node(t1,t2);
				==>
					SumSequenceOfTrees(stack) == Frontier(Node(t1,t2)) + SumSequenceOfTrees(stack[1..]);
				==>
					SumSequenceOfTrees(stack) == Frontier(t1) +  Frontier(t2) + SumSequenceOfTrees(stack[1..]);
				==>
					SumSequenceOfTrees(stack) == SumSequenceOfTrees([t1,t2] + stack[1..]);
				}

				assert SumSequenceOfTrees(stack) == SumSequenceOfTrees([t1,t2] + stack[1..]);
				assert temp + SumSequenceOfTrees([t1,t2] + stack[1..]) == SumSequenceOfTrees([tree]);
				//following assignment 3.5
				stack := [t1,t2] + stack[1..];
				assert temp + SumSequenceOfTrees(stack) == SumSequenceOfTrees([tree]);
		}
		assert temp + SumSequenceOfTrees(stack) == SumSequenceOfTrees([tree]);
		assert SizeOfTreeSequence(stack) < SizeOfTreeSequence(stack2);
	}
	assert temp + SumSequenceOfTrees(stack) == SumSequenceOfTrees([tree]) && stack == [];
	
	calc{
		stack == []
	==>
		SumSequenceOfTrees(stack) == []
	==>
		temp == SumSequenceOfTrees([tree])
	==
		SumSequenceOfTrees([tree]) == Frontier(tree)
	==>
		temp == Frontier(tree);
	}
	
	io.omega := io.omega + temp;
	assert io.omega == old(io.omega) + Frontier(tree);
}



function SizeOfTreeSequence(ntl: seq<BT<T>>): nat
{
	if (ntl == []) then 0 else SizeOfTree(ntl[0]) + SizeOfTreeSequence(ntl[1..])
}

function SizeOfTree(nt: BT<T>): nat
{
	match nt {
		case Tip(n) => 1
		case Node(nt1,nt2) => 1 + SizeOfTree(nt1)+SizeOfTree(nt2)
	}
}
