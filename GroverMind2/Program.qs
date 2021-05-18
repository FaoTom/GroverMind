namespace GroverMind {

    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Random;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Logical;
    
// Functions____________________________________________________________________________________________

    function BoolToIntArray(inputs : Bool[]) : Int[] {
        //Converts from array of couples of bits to array of integers.
        mutable converted = new Int[5];
        let chunks = Chunks(2,inputs);
        for i in 0 .. Length(inputs)/2-1 {
            set converted w/= i <- BoolArrayAsInt(chunks[i]);
        }
        return converted;
    }

    function IsNumberPresentInArray(n : Int, array : Int[]) : Bool {
    return Any(EqualI(_, n), array);
    }

    function IntToBoolArray(inputs : Int[][]) : Bool[][] {
        mutable ConvertedValid = new Bool[][Length(inputs)];
        for (i, sequence) in Enumerated(inputs){
            set ConvertedValid w/= i <- Flattened(Mapped(IntAsBoolArray(_,2), sequence));
        }
        return ConvertedValid;
    }

    function Compare(master : Int[], player : Int[]) : Int[] {
        //Compares the two sequences of colors.
        //For each position in the grid, returns a tuple containing a boolean (true if the colors are matching,
        //false otherwise) and the color of the player sequence.
        mutable tank = new Int[Length(player)];
        mutable nBlack = 0;
        mutable nWhite = 0;
        mutable mask_black = [false, false, false, false, false];
        mutable mask_used = [false, false, false, false, false];

        for i in 0..Length(player)-1{
            if (player[i] == master[i]){
                set mask_black w/=i <- true;
                set nBlack = nBlack + 1;
            }
        }
        for i in 0..Length(player)-1{
            if (not mask_black[i]){
                for j in 0..Length(player)-1{
                    if(player[i]==master[j] and not mask_used[j]){
                        set nWhite = nWhite + 1;
                        set mask_used w/=i <- true;
                        break;
                    }
                }
            }
        }
        
        return [nBlack, nWhite];
    }

    function Colorify(input: Int[]) : String[] {
        //Returns the array of colours given an array of integers
        mutable converted = new String[Length(input)];
        let colours = ["Red","Green","Blue","Yellow"];
        for i in 0 .. Length(input)-1{
            set converted w/=i <- colours[input[i]];
        }
        return converted;
    }

    function generateSequences(nColors : Int, nPositions : Int) : Int[][] {
        let nCombinations = nColors^nPositions;
        mutable AllSequences = new Int[][nCombinations];
        for i in 0..nColors-1{
            for j in 0..nColors-1{
                for k in 0..nColors-1{
                    for l in 0..nColors-1{
                        for m in 0..nColors-1{
                            set AllSequences w/=(4^4*i+4^3*j+4^2*k+4*l+m)  <- [i,j,k,l,m];
                        }
                        
                    }
                }
            }
        }
        return AllSequences;

    }

    function IsTrue(a : Bool): Bool{
        return a;
    }

    function constrainChoice(AllSequences : Int[][], player: Int[], nBlack : Int, nWhite : Int): Int[][]{
        //return (Mapped(Compare, Zipped(player, AllSequences)) == [nBlack, nWhite]);
        mutable BoolOutput = new Bool[Length(AllSequences)];
        for (i, sequence) in Enumerated(AllSequences){
            set BoolOutput w/=i <- EqualA(EqualI, Compare(sequence, player), [nBlack, nWhite]);
    }
    return Subarray(Where(IsTrue, BoolOutput), AllSequences);
    }

// Operations____________________________________________________________________________________________

    operation InitialSequence(nPositions: Int, nColors: Int) : Int[] {
        //Generates a sequence of colours
        mutable arr1 = new Int[nPositions];
        for i in 0 .. nPositions-1{
            set arr1 w/= i <- DrawRandomInt(0,nColors-1);
        }
        return arr1;
    }
    
    operation MarkMatchingColors(input : Qubit[], ValidSequences: Int[][], target : Qubit) : Unit is Adj {
        //GroverMind oracle
        mutable ConvertedValid = IntToBoolArray(ValidSequences);
        for converted in ConvertedValid{
            ControlledOnBitString(converted,X)(input, target);
        }
    }

    operation ApplyMarkingOracleAsPhaseOracle( MarkingOracle : ((Qubit[], Qubit) => Unit is Adj), register : Qubit[]) : Unit is Adj {
        //From Marking to Phase Oracle by means of a phase kickback
        use target = Qubit();
        within {
            X(target);
            H(target);
        } apply {
            MarkingOracle(register, target);
        }
    }

    operation RunGroversSearch(register : Qubit[], phaseOracle : ((Qubit[]) => Unit is Adj), iterations : Int) : Unit {
    //Function to run Grover's algorithm on the input register, using the input phase oracle 
    //Defined equal as in the Quantum Katas.

        //Preparing the superposition
        ApplyToEach(H, register);

        //Repeating the process for the given number of iterations
        for i in 1 .. iterations {

            //Applying the phase oracle to the register
            phaseOracle(register);

            //Reflection around the mean    
            within {
                ApplyToEachA(H, register);
                ApplyToEachA(X, register);
            } apply {
                Controlled Z(Most(register), Tail(register));
            }
        }
        
    }


    //Main operation of the code
    @EntryPoint()
    operation GroverMind() : Unit {
        
        //Initializing number of qubits = 2 * number of point
        let nQubits = 10;
        let nColors = 4;
        let nPositions = 5;
        let N = IntAsDouble(nColors^nPositions);

        //Generating the sequence of colours for the master
        let master_sequence = InitialSequence(nPositions, nColors);                              

        //Initializing number of guessed points
        mutable compatible = 0;

        //Initializing number of iterations for Grover's algorithm
        mutable nIterations = 0;

        //Initializing boolean array for guessed points
        mutable answer = new Bool[nQubits];

        //Initializing number of rounds
        mutable iter = 0;

        //Allocating 10 qubits for the points and control qubit
        use (register, output) = (Qubit[nQubits], Qubit());

        let allSequences = generateSequences(nColors, nPositions);
    
        mutable pegs = [0,0];
        mutable constrained = allSequences;

        //Cycle until the points are all guessed
        repeat{
    
            //Updating value of correctly compatible points
            set compatible = Length(constrained);

            //Calculating number of expected calls of the oracle for Grover's algorithm
            set nIterations = Round(PI()/4.*1./ArcSin(Sqrt(IntAsDouble(compatible)/N))-0.5);
            
            //Updating counter
            set iter+=1;
            
            //Updating conditions in the marking oracle
            let MarkingOracle = MarkMatchingColors(_,constrained,_);
            
            //Updating phase oracle
            let PhaseOracle = ApplyMarkingOracleAsPhaseOracle(MarkingOracle,_);
            
            //Running Grover's search algorithm for the expected number of times
            RunGroversSearch(register, PhaseOracle, nIterations);
            
            //Measuring the qubits
            let res = MultiM(register);

            //Saving guess and comparing it with the master sequence
            set answer = ResultArrayAsBoolArray(res);
            
            //Output to terminal
            Message($"\n=======================================================");
            Message($"GUESS {iter}:");
            Message($"Master sequence:  \t{master_sequence}");
            Message($"Player guess: \t \t{BoolToIntArray(answer)}");
            Message($"NERE: {pegs[0]}");
            Message($"BIANCHE: {pegs[1]}");
            Message($"Constrained: {constrained}");
            Message($"N iterations: {nIterations}");
            Message($"Guessed: {compatible}");
            
            set pegs = Compare(master_sequence, BoolToIntArray(answer));
            set constrained = constrainChoice(constrained, BoolToIntArray(answer), pegs[0], pegs[1]);

            //Resetting all qubits
            ResetAll(register);
        

        } until (pegs[0]==nPositions);

        //Final output
        Message($"\n\nFantastico :D GroverMind found the solution in {iter} guesses!");
    }
}