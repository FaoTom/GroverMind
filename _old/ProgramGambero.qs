// qchack-microsoft-challenge
// forked from quantumcoalition/qchack-microsoft-challenge

namespace Qrng {
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Random;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Diagnostics;
    
// Functions____________________________________________________________________________________________

    function Convert(inputs : Bool[]) : Int[] {
        //Converts from array of couples of bits to array of integers.
        let chunks = Chunks(2,inputs);
        mutable converted = new Int[Length(chunks)];
        
        for i in IndexRange(chunks) {
            set converted w/= i <- BoolArrayAsInt(chunks[i]);
        }
        return converted;
    }

    function Compare(master : Int[], player : Int[]) : (Bool,Int)[] {
        //Compares the two sequences of colors.
        //For each position in the grid, returns a tuple containing a boolean (true iff the colors are matching),
        //and the color of the player sequence.
        mutable check = new (Bool,Int)[Length(master)];

        for i in IndexRange(master) {  
            set check w/= i <- (master[i] == player[i], player[i]);
            }   
        return check;
    }

    function CountHowManyTrue(arr : (Bool,Int)[]) : Int { 
        //Returns the number of the tuples in arr that have true as first element
        mutable count = 0; 

        for p in arr{ 
            let (guess, col) = p;
            if guess{ 
                set count += 1;
            } 
        } 
        return count;
    }

    function AllAreTrue(arr : (Bool,Int)[]) : Bool { 
        //Returns true iff all the tuples in arr have true as first element
        
        return CountHowManyTrue(arr) == Length(arr); 
    }
    
    function Colorify(input: Int[]) : String[] {
        //Returns the array of colours given an array of integers
        mutable converted = new String[Length(input)];
        let colours = ["Red","Green","Blue","Yellow"];  //portarlo fuori? dove? come tipo utente? Inconsistente con nColours
        for i in IndexRange(input){
            set converted w/=i <- colours[input[i]];
        }
        return converted;
    }

// Operations____________________________________________________________________________________________

    operation InitialSequence(cycles : Int, nColors : Int) : Int[] {
        //Generates a sequence of colours
       
        mutable arr = new Int[cycles];
        let ub = nColors-1;
        for i in IndexRange(arr){
            set arr w/= i <- DrawRandomInt(0,ub);
        }
        return arr;
    }

    operation MarkMatchingColors(input : Qubit[], check : (Bool,Int)[], target : Qubit) : Unit is Adj {
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

    operation ApplyMarkingOracleAsPhaseOracle(
        //From Marking to Phase Oracle by means of a phase kickback
        MarkingOracle : ((Qubit[], Qubit) => Unit is Adj), 
        register : Qubit[]
    ) : Unit is Adj {
        use target = Qubit();
        within {
            X(target);
            H(target);
        } apply {
            MarkingOracle(register, target);
        }
    }

    operation RunGroversSearch(register : Qubit[], phaseOracle : ((Qubit[]) => Unit is Adj), iterations : Int) : Unit {
        //Grover's algorithm iteration for the optimal number of times
        ApplyToEach(H, register);
        for i in 1 .. iterations {
            phaseOracle(register);
            within {
                ApplyToEachA(H, register);
                ApplyToEachA(X, register);
            } apply {
                Controlled Z(Most(register), Tail(register));
            }
        }
        
    }

    @EntryPoint()
    operation QasterMind() : Unit {
        //GroverMind's main core 
        let nQubits = 10;

        let cycles = 5;
        let nColors = 4;    // Better to define a 'Color' type?
        for nTrial in 1..2 {
            let master_sequence = InitialSequence(cycles, nColors);   
            let colored_master_sequence = Colorify(master_sequence);

            let player_sequence = InitialSequence(cycles, nColors);                                 

            mutable well_done = Compare(master_sequence, player_sequence);           
            mutable guessed = CountHowManyTrue(well_done);
            mutable nIterations = Round(PI()  * PowD(2.,  IntAsDouble(guessed) - 2. ));   
            mutable answer = new Int[nQubits];
            
            mutable nGuessedPrev = 0;
            mutable iter = 0;

            use (register, output) = (Qubit[nQubits], Qubit());

            repeat{
                set iter += 1;

                let MarkingOracle = MarkMatchingColors(_,well_done,_);  // why not mutable?
                let PhaseOracle = ApplyMarkingOracleAsPhaseOracle(MarkingOracle,_);
                RunGroversSearch(register, PhaseOracle, nIterations);
                
                let res = MultiM(register);

                set answer = Convert(ResultArrayAsBoolArray(res));
                set well_done = Compare(master_sequence, answer);

                Message($"\n=======================================================");
                Message($"ITERATION {iter}:");
                Message($"Master sequence: {colored_master_sequence}");
                Message($"Player guess: {Colorify(answer)}");

                set guessed = CountHowManyTrue(well_done);
                if guessed < nGuessedPrev {
                            Message($"**************** nGuessed decreased from {nGuessedPrev} to {guessed}");
                        }
                        set nGuessedPrev = guessed;

                ResetAll(register);  // why not in fixup?

            } until AllAreTrue(well_done)
            fixup{
                
                set nIterations = Round(PI()  * PowD(2.,  IntAsDouble(guessed) - 2. ));
            }

            Message($"\n\nFantastico :D GroverMind found the solution in {iter} iterations!");
        }
    }
}