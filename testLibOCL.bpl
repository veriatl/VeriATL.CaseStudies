
// a simple example to demonstrate how to use OCL iterators defined in 'LibOCL.bpl'

// Defined an anonymous predicate that check the pass in integer is greater than 1 or not.
const unique gtZero: [int, HeapType]bool;	
  axiom gtZero == (lambda x: int, h: HeapType :: x>0);
  
procedure testGeneral() returns ()
  modifies Heap;
{
	var c: Seq int;
	var inc: [int,HeapType]int;
	var dec: [int,HeapType]int;
	var r1,r2: Seq int;
	
	inc := (lambda x: int, h: HeapType :: x+1);
	dec := (lambda x: int, h: HeapType :: x-1);
	
	c := Seq#Build(Seq#Build(Seq#Empty(),1),2);	//{1,2,3}
	
	r1 := Iterator#Collect(c, Heap, inc); //{2,3,4}
	r2 := Iterator#Collect(c, Heap, dec); //{0,1,2}

	assert Seq#Index(r1,1)==3;
	assert Seq#Index(r2,0)==0;
	
	// whether the elements contained in 'c', yield a unique value when applied to 'gtZero' predicate defined above.
	assert !(Iterator#isUnique(c,Heap,gtZero));
}


// --------------------------------------------------------------------------------------------------------------
// --------------------------------------------------------------------------------------------------------------

// OCL Iterator Test for a small subset of Royal and loyal program
// In particular, we want to select the customer that has clubcard greater than 400 points.

// metamodel encodings
const unique t#Customer: TName;
const unique t#Card: TName;

const unique f#card: Field ref;
const unique f#point: Field int;



// getters of the Customer classifier
function Customer#getCard(o: ref, h:HeapType): ref;
  axiom (forall o: ref, h: HeapType :: typeof(o) == t#Customer ==> Customer#getCard(o, h) == h[o, f#card]);

function Card#getPoint(o: ref, h: HeapType): int;  
  axiom (forall o: ref, h: HeapType :: typeof(o) == t#Card ==> Card#getPoint(o, h) == h[o, f#point]);

// the defined anonymous predicate check whehter the passed-in customer that has clubcard greater than 400 points.
const unique filter: [ref,HeapType]bool;
	axiom filter == (lambda o:ref, h:HeapType :: Card#getPoint(Customer#getCard(o,h),h)>400);

procedure test#Iter#Select(cList: Seq ref) returns(loyalC : Seq ref)
  requires Seq#Length(cList) >= 0;
  requires (forall i: int :: 0<=i && i<Seq#Length(cList) ==> typeof(Seq#Index(cList,i)) == t#Customer && typeof(Customer#getCard(Seq#Index(cList,i),Heap)) == t#Card);
  ensures loyalC == Iterator#Select(0,Seq#Length(cList),cList,Heap,filter);
{

	var i: int;

	i:=0;
	loyalC := Seq#Empty();
	
	while(i<Seq#Length(cList))
	  invariant i<=Seq#Length(cList);
	  invariant cList == old(cList);
	  invariant loyalC == Iterator#Select(0,i,cList,Heap,filter);
	{
		
		if(Card#getPoint(Customer#getCard(Seq#Index(cList,i),Heap),Heap)>400)
		{
			//assert (forall<T> s: Seq T, e: T :: Seq#Equal(Seq#Build(s, e), Seq#Append(s, Seq#Singleton(e))));
			//loyalC := Seq#Build(loyalC, Seq#Index(cList,i));
			loyalC := Seq#Append(loyalC,Seq#Singleton(Seq#Index(cList,i)));
			
		}
		i := i+1;
	}

}	







