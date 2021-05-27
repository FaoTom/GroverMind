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

    function BoolToIntArray(inputs : Bool[]) : Int[] { //Converts from base 2 to Int
        return Mapped(BoolArrayAsInt, Chunks(2,inputs));
    }

    function IntToBoolArray(inputs : Int[][]) : Bool[][] {
        mutable ConvertedValid = new Bool[][Length(inputs)];
        for (i, sequence) in Enumerated(inputs){
            set ConvertedValid w/= i <- Flattened(Mapped(IntAsBoolArray(_,2), sequence));
        }
        return ConvertedValid;
    }

    function IsNumberPresentInArray(n : Int, array : Int[]) : Bool {
    return Any(EqualI(_, n), array);
    }

    function Compare(master : Int[], player : Int[]) : Int[] {
        //Compares the two color sequences and returns the number of black and white pegs
        mutable tank = new Int[Length(player)];
        mutable nBlack = 0;
        mutable nWhite = 0;
        mutable mask_black = [false, false, false, false, false];
        mutable mask_used = [false, false, false, false, false];
        mutable first = true;

        for i in 0..Length(player)-1{
            if (player[i] == master[i]){
                set mask_black w/=i <- true;
                set mask_used w/=i <- true;
                set nBlack += 1;
            }
        }
        for i in 0..Length(player)-1{
            if (not mask_black[i]){
                for j in 0..Length(player)-1{
                    set first = true;
                    if(player[i]==master[j] and not mask_used[j] and first){
                        set nWhite += 1;
                        set mask_used w/=i <- true;
                        set first = false;
                    }
                }
            }
        }
        return [nBlack, nWhite];
    }

    function colorItemMapper(item: Int, colors: String[]) : String {
        //Fact(item in Range(colors), "colorItem: Inconsistent  representation. Check Setup."); 
        return colors[item];
    }
    
    function Colorify(input: Int[], colors: String[]) : String[] {
        //Requires: Dom(input) == Range(colors)
        //Returns c such that (All i in IndexRange(input). c[i] = colors[input[i]])
        let auxColorItem = colorItemMapper(_, colors);
        return Mapped(auxColorItem, input);
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

    function IsTrue(t : Bool): Bool{
        return t;
    }

    function constrainChoice(AllSequences : Int[][], player: Int[], nBlack : Int, nWhite : Int): Int[][]{
        mutable BoolOutput = new Bool[Length(AllSequences)];
        for (i, sequence) in Enumerated(AllSequences){
            set BoolOutput w/=i <- EqualA(EqualI, Compare(sequence, player), [nBlack, nWhite]);
    }
    return Subarray(Where(IsTrue, BoolOutput), AllSequences);
    }

// Operations____________________________________________________________________________________________

operation InitialSequence(nPositions: Int, nColors: Int) : Int[] {
        //Generates a sequence of colours
        mutable arr = new Int[nPositions];
        for i in 0 .. nPositions-1{
            set arr w/= i <- DrawRandomInt(0,nColors-1);
        }
        return arr;
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
        
        //Initializing number of qubits = 2 * number of positions
        let nColors = 4;
        let nPositions = 5;
        let nQubits = 2*nPositions;
        let colors = ["Red","Green","Blue","Yellow"]; 
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
            set iter += 1;
            
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
            Message($"GUESS #{iter}:");
            // Message($"Master sequence:  \t{Colorify(master_sequence,colors)}"); // uncomment to color output
            // Message($"Player guess: \t \t{Colorify(BoolToIntArray(answer),colors)}");
            Message($"Master sequence:  \t{master_sequence}");
            Message($"Player guess: \t \t{BoolToIntArray(answer)}");
            Message($"Black pegs: \t{pegs[0]}");
            Message($"White pegs: \t{pegs[1]}");
            // Message($"Constrained: {constrained}");
            Message($"N iterations: \t{nIterations}");
            Message($"Guessed: \t{compatible}");
            
            set pegs = Compare(master_sequence, BoolToIntArray(answer));
            set constrained = constrainChoice(constrained, BoolToIntArray(answer), pegs[0], pegs[1]);

            //Resetting all qubits
            ResetAll(register);
        

        } until (pegs[0]==nPositions);

        //Final output
        Message($"\n\nFantastico :D GroverMind found the solution in {iter} guesses!");
    }
}