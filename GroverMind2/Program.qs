namespace Qrng {

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

    function Convert(inputs : Bool[]) : Int[] {
        //Converts from array of couples of bits to array of integers.
        mutable converted = new Int[5];
        let chunks = Chunks(2,inputs);
        for i in 0 .. Length(inputs)/2-1 {
            set converted w/= i <- BoolArrayAsInt(chunks[i]);
        }
        return converted;
    }

    function Compare(master : Int[], player : Int[]) : Int[] {
        //Compares the two sequences of colors.
        //For each position in the grid, returns a tuple containing a boolean (true if the colors are matching,
        //false otherwise) and the color of the player sequence.
        
        mutable nBlack = 0;
        mutable nWhite = 0;
    
        for (m, p) in Zipped(master, player){
                if (m==p){
                    set nBlack = nBlack + 1;
                }
                else{
                    for k in master{ //se è possibile vettorizzare questa top. Intanto così
                        if (p==k){
                            set nWhite = nWhite + 1;
                        }
                    }
                    
                }
            }
        
        return [nBlack, nWhite];
    }

    function AllAreTrue(arr : (Bool,Int)[]) : Bool { 
        //Returns a true if the array of tuples in input contains all trues in the first entry
        mutable count = 0; 

        for i in 0..Length(arr)-1{ 
            let (guess, col) = arr[i];
            if guess{ 
                set count = count +1; 
            } 
        } 
        let check = count == Length(arr); 
        return check; 
    }

    function CountHowManyTrue(arr : (Bool,Int)[]) : Int { 
        //Returns a the number of trues in the array of tuples
        mutable count = 0; 

        for i in 0..Length(arr)-1{ 
            let (guess, col) = arr[i];
            if guess{ 
                set count = count +1; 
            } 
        } 
        return count;
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
        for i in 0..3{
            for j in 0..3{
                for k in 0..3{
                    for l in 0..3{
                        for m in 0..3{
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
        for (idx, sequence) in Enumerated(AllSequences){
            set BoolOutput w/=idx <- EqualA(EqualI, Compare(sequence, player), [nBlack, nWhite]);
    }
    return Subarray(Where(IsTrue, BoolOutput), AllSequences);
    }

// Operations____________________________________________________________________________________________

    operation InitialSequence() : Int[] {
        //Generates a sequence of colours
        let cycles = 5;
        let nColors = 4;
        mutable arr1 = new Int[cycles];
        for i in 0 .. cycles-1{
            set arr1 w/= i <- DrawRandomInt(0,nColors-1);
        }
        return arr1;
    }
    
    operation MarkMatchingColors(input : Qubit[], ValidSequences: Int[][], target : Qubit) : Unit is Adj {
        //GroverMind oracle
        let register_chunk = Chunks(2,input);
        use controlQubit = Qubit[Length(input)/2];
        within {
            for ((guess, col), (Q, control)) in Zipped(check, Zipped(register_chunk, controlQubit)){
                if guess{
                    ControlledOnInt(col,X)(Q,control);
                }
                else {
                    X(control); 
                }
            }
        } apply {
            Controlled X(controlQubit, target);
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

        //Generating the sequence of colours for the master
        let master_sequence = InitialSequence();           

        //Generating the initial guess for the player                      
        let player_sequence = InitialSequence();                                 

        //Initializing number of guessed points
        mutable guessed = 0;

        //Initializing number of iterations for Grover's algorithm
        mutable nIterations = 0;

        //Initializing boolean array for guessed points
        mutable answer = new Bool[nQubits];

        //Initializing number of rounds
        mutable iter = 0;

        //Allocating 10 qubits for the points and control qubit
        use (register, output) = (Qubit[nQubits], Qubit());

        //Initializing check list comparing the first guess with the master
        mutable well_done = Compare(master_sequence, player_sequence);

        //Cycle until the points are all guessed
        repeat{
            
            //Updating value of correctly guessed points
            set guessed = CountHowManyTrue(well_done);

            //Calculating number of expected calls of the oracle for Grover's algorithm
            set nIterations = Round(PI()  * PowD(2.,  IntAsDouble(guessed) - 2. ));

            //Updating counter
            set iter+=1;
            
            //Updating conditions in the marking oracle
            let MarkingOracle = MarkMatchingColors(_,well_done,_);
            
            //Updating phase oracle
            let PhaseOracle = ApplyMarkingOracleAsPhaseOracle(MarkingOracle,_);
            
            //Running Grover's search algorithm for the expected number of times
            RunGroversSearch(register, PhaseOracle, nIterations);
            
            //Measuring the qubits
            let res = MultiM(register);

            //Saving guess and comparing it with the master sequence
            set answer = ResultArrayAsBoolArray(res);
            set well_done = Compare(master_sequence, Convert(answer));

            //Output to terminal
            Message($"\n=======================================================");
            Message($"GUESS {iter}:");
            Message($"Master sequence:  \t{Colorify(master_sequence)}");
            Message($"Player guess: \t \t{Colorify(Convert(answer))}");
        
            //Resetting all qubits
            ResetAll(register);
        

        } until AllAreTrue(well_done);

        //Final output
        Message($"\n\nFantastico :D GroverMind found the solution in {iter} guesses!");
    }
}