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
    
// Auxiliary functions____________________________________________________________________________________________

     function Setup() : (Int, String[], (Int, Int)) { // define nPegs, colors, colorRange
        let colors = ["Red   ","Green ","Blue  ","Yellow"]; 
        return (5, colors,(0, Length(colors)-1));
    }
    
    function Convert(inputs : Bool[]) : Int[] { //Converts from base 2 to Int.
            return Mapped(BoolArrayAsInt, Chunks(2,inputs)); 
    }

    function check2pegsMapper (masterPeg : Int, playerPeg : Int) : (Bool, Int) { // saves the player's color too.
        return (masterPeg == playerPeg, playerPeg);
    }

    function CheckAnswer(master : Int[], player : Int[]) : (Bool,Int)[] { //  Assess the player's answer
        //  For each position in the grid, returns a pair containing 
        //  true iff there is a match,
        //  the color in the player sequence.
        return Mapped(check2pegsMapper, Zipped(master, player));
    }

    function guessedFolder (state: Int, singleCheck : (Bool, Int)) : Int { // add an outcome 
        let (match, _) = singleCheck;
        return state + (match ? 1 | 0);
    }
    
    function CountGuessed(check: (Bool, Int)[]) : Int {
        return Fold(guessedFolder, 0, check);
    }

// Presentation functions

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

    function  ConsoleOutput(iter: Int, nGuessed: Int, colored_master_sequence: String[], colored_answer_sequence: String[]) : Unit {
        Message("Iteration: "+$"{iter}"+"  Guessed: "+$"{nGuessed}");
        Message($"Master sequence: {colored_master_sequence}");
        Message($"Player guess:    {colored_answer_sequence}");
    }

// Random color generation____________________________________________________________________________________________
         
    operation RandomSequence(length : Int, range : (Int, Int)) : Int[] {
        mutable arr = new Int[length];
        for i in IndexRange(arr){
            set arr w/= i <- DrawRandomInt(range); 
        }
        return arr;
    }

// Grover search auxiliary functions and operations_____________________________________________________________

    function nGroverIterations(nGuessed : Int) : Int {
        return Round(PI()  * PowD(2.,  IntAsDouble(nGuessed) - 2. ));
    }
    
    operation MarkMatchingColors(input : Qubit[], check : (Bool,Int)[], target : Qubit) : Unit is Adj {
        //GroverMind oracle
        let register_chunk = Chunks(2,input);
        use controlQubit = Qubit[Length(register_chunk)];
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


// GroverMind's main core 

    //@EntryPoint()
    operation QasterMind() : Unit {
        
        let (nPegs, colors, colorRange) = Setup();
           
        let master_sequence = RandomSequence(nPegs, colorRange);   
        let colored_master_sequence = Colorify(master_sequence, colors);

        mutable answer = RandomSequence(nPegs, colorRange);
        
        mutable guessed = CheckAnswer(master_sequence, answer);
        mutable nGuessed = CountGuessed(guessed);
        mutable iter = 0;
        
        ConsoleOutput(iter, nGuessed, colored_master_sequence, Colorify(answer, colors));
        
        if nGuessed < nPegs { // nGuessed == nPegs is a rare possible event at this point.
            let nQubits = nPegs*2;
            //use (register, output) = (Qubit[nQubits], Qubit()); output seems useless.
            use register = Qubit[nQubits];

            repeat{
                
                let MarkingOracle = MarkMatchingColors(_,guessed,_);  // why not mutable? Because it constructs a new callable?.
                let PhaseOracle = ApplyMarkingOracleAsPhaseOracle(MarkingOracle,_);

                RunGroversSearch(register, PhaseOracle, nGroverIterations(nGuessed));
                let res = MultiM(register);

                set answer = Convert(ResultArrayAsBoolArray(res));
                set guessed = CheckAnswer(master_sequence, answer);
                set nGuessed = CountGuessed(guessed);
                set iter += 1;

                ConsoleOutput(iter, nGuessed, colored_master_sequence, Colorify(answer, colors));
            
            } until nGuessed == nPegs
            fixup {
                ResetAll(register);
            }
        } 

        Message($"\n\nFantastic :D GroverMind found the solution in {iter} iterations!");
    }
}