class CircularMemory{
    
    var cells : array<int>
    var read_position : int
    var write_position : int
    var isFlipped : bool


    constructor Init(cap : int)
        requires cap > 0
        ensures Valid()
        ensures fresh(cells)
        ensures read_position == 0 && write_position == 0
        ensures cap == cells.Length
    {
        cells := new int[cap];
        read_position, write_position := 0, 0;
        isFlipped := false;
    }

    predicate Valid() 
        reads this
    {
        (read_position >= 0 && read_position < cells.Length) &&
        (write_position >= 0 && write_position < cells.Length) &&
        (cells.Length > 0)
    }

    // A predicate indicating no more Read available
    predicate isEmpty()
        reads this
        requires Valid()
        ensures Valid()
    {
        (read_position == write_position) && !isFlipped
    }

    //A predicate indicating no more Write should be allowed
    predicate isFull()
        reads this
        requires Valid()
        ensures Valid()
    {
        (read_position == write_position) && isFlipped
    }

    method Read() returns (isSuccess : bool, content : int)
        modifies this
        requires Valid()
        ensures  Valid()
        ensures isSuccess  ==> 0 <= old(read_position) < cells.Length
        ensures isSuccess  ==> content       == cells[old(read_position)]
        ensures !isSuccess ==> read_position == old(read_position)
        ensures !isSuccess ==> content       == -100
    {
        isSuccess := false;
        content := -100;

        if(!isEmpty()){
            // if condition holds the read-pointer will end up on same index as the write-pointer and isFlipped get set to false
            // which indicates the buffer is empty.
            if(read_position == cells.Length - 1 && write_position == 0){
                isFlipped := false;
            }
            isSuccess     := true;
            content       := cells[read_position];
            read_position := (read_position + 1) % cells.Length;
            return isSuccess, content;          
        }else { 
            return isSuccess, content;
        }
    }

    
    method Write(input : int) returns (isSuccess : bool)
        modifies this, this.cells
        requires Valid()
        ensures  Valid()
        ensures 0           <= old(write_position) < cells.Length
        ensures isSuccess   ==> cells[old(write_position)] == input
        ensures !isSuccess  ==> write_position == old(write_position)
    {
        isSuccess := false;
    
        if(!isFull()){
            // if condition holds the write-pointer will end up on same index as the read-pointer and isFlipped get set to true
            // which indicates the buffer is full.
            if(write_position == cells.Length - 1 && read_position == 0){
                isFlipped := true;
            }
            isSuccess := true;
            cells[write_position] := input;
            write_position := (write_position + 1) % cells.Length;
            return isSuccess;
        } else {
            return isSuccess;
        } 
    }

    // Question 3 for Lab 3
    method DoubleCapacity()
        modifies this`cells
        requires Valid()
        ensures Valid()
        ensures cells.Length == 2 * old(cells.Length)
        ensures read_position == old(read_position)
        ensures write_position == old(write_position)
        ensures forall j : int :: 0 <= j < old(cells.Length) ==> cells[j] == old(cells[j])
        ensures forall j : int :: old(cells.Length) <= j < cells.Length ==> cells[j] == 0
    {

        var oldCells        := cells;
        var newCapacity     := 2 * cells.Length;
        var newCells        := new int[newCapacity];
        var i               := 0; 
        while(i < newCapacity)
            invariant 0 <= i <= newCapacity
            invariant forall j : int :: 0 <= j < oldCells.Length && j < i ==> newCells[j] == oldCells[j] 
            invariant forall j : int :: old(cells.Length) <= j < i ==> newCells[j] == 0 
            decreases newCapacity - i // Unsure if needed or if Dafny automatically verifies.
        
        {   
            if(i < oldCells.Length){
                newCells[i] := oldCells[i];

            }else{
                newCells[i] := 0;

            }
            i := i + 1;

        }
        cells := newCells;
    }

}