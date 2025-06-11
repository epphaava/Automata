#load "DFA.fsx"
#load "../derivative_of_regex/derivative.fsx"

type NFA<'State, 'Input when 'State : comparison and 'Input : comparison> = {
    States: Set<'State>
    Alphabet: Set<'Input>
    TransitionFunction: Map<'State * 'Input option, Set<'State>>
    StartStates: Set<'State>
    AcceptStates: Set<'State>
}

let isAccepted (acceptStates: Set<'State>) (finalStates: Set<'State>) =
    not (Set.isEmpty (Set.intersect finalStates acceptStates))

let ECLOSE (nfa: NFA<'State, 'Input>) (states: Set<'State>) : Set<'State> =
    let rec find currentStates previousStates =
        let nextStates =
            currentStates
            |> Set.map (fun state ->
                match nfa.TransitionFunction.TryFind (state, None) with
                | Some nextStates -> Set.difference nextStates previousStates
                | None -> Set.empty)
            |> Set.unionMany
        if Set.isEmpty nextStates then previousStates
        else find nextStates (Set.union previousStates nextStates)
    find states states

            
let runNFA (nfa: NFA<'State, 'Input>) input =
    let rec run currentStates remainingInput =
        let currentStatesWithEpsilon = ECLOSE nfa currentStates
        match remainingInput with
        | [] -> 
            if (isAccepted nfa.AcceptStates currentStatesWithEpsilon) then 
                printfn "Resulting states: %A" currentStates
                true
            else false
        | nextInput :: rest ->
            let nextStates =
                currentStatesWithEpsilon 
                |> Set.map (fun state ->
                    match nfa.TransitionFunction.TryFind (state, Some nextInput) with
                    | Some next -> next
                    | None -> Set.empty
                )
                |> Set.unionMany
            run nextStates rest
    run nfa.StartStates (Seq.toList input)

