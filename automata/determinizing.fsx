#load "DFA.fsx"
#load "NFA.fsx"

// Eliminate e-transitions
let removeEpsilonTransitions (nfa: NFA.NFA<'State, 'Input>) : NFA.NFA<'State, 'Input> =

    let stateEpsilonClosures =
        nfa.States
        |> Set.map (fun state -> state, NFA.ECLOSE nfa (set [state]))
        |> Map.ofSeq

    let new_transitions =
        nfa.TransitionFunction
        |> Map.fold (fun acc (state, input) _ ->
            if input = None then 
                acc
            else
                // all reachable states with given input symbol
                let allReachableStates =
                    stateEpsilonClosures.[state]
                    |> Set.fold (fun acc epsilonState ->
                
                        match Map.tryFind (epsilonState, input) nfa.TransitionFunction with
                        | Some next -> acc + next
                        | None -> acc
                    ) Set.empty

                // for each reachable state also add the epsilon reachable states from them
                let epsilonReachables =
                    allReachableStates 
                    |> Set.fold (fun acc reachableState -> acc + stateEpsilonClosures.[reachableState]) Set.empty

                if not (Set.isEmpty epsilonReachables) then 
                    acc |> Map.add (state, input) epsilonReachables
                else
                    acc
        ) Map.empty

    let new_start =
        nfa.StartStates
        |> Set.fold (fun acc state -> acc + stateEpsilonClosures.[state]) Set.empty

    let new_accept =
        nfa.States
        |> Set.fold (fun acc state ->
            if Set.exists (fun epsilon -> Set.contains epsilon nfa.AcceptStates) stateEpsilonClosures.[state] then
                acc |> Set.add state
            else
                acc
        ) Set.empty

    { States = nfa.States; Alphabet = nfa.Alphabet; TransitionFunction = new_transitions; StartStates = new_start; AcceptStates = new_accept }


let determinize (inputNFA: NFA.NFA<'State, 'Input>) : DFA.DFA<Set<'State>, 'Input> =
    let nfa = removeEpsilonTransitions inputNFA

    let getNextStates states input =
        states
        |> Set.fold (fun acc state ->
            match Map.tryFind (state, Some input) nfa.TransitionFunction with
            | Some next_states -> Set.union acc next_states
            | None -> acc
        ) Set.empty

    let rec processStates not_visited visited new_states new_transitions =
        match not_visited with
        | [] -> new_states, new_transitions
        | current :: rest ->
            if Set.contains current visited then
                processStates rest visited new_states new_transitions
            else
                let new_visited = Set.add current visited
                let new_states = Set.add current new_states

                let new_transitions' = 
                    nfa.Alphabet
                    |> Set.fold (fun acc input ->
                        let next_states = getNextStates current input
                        if not (Set.isEmpty next_states) then
                            Map.add (current, input) next_states acc
                        else acc
                    ) new_transitions

                let next_visit = 
                    nfa.Alphabet
                    |> Set.fold (fun acc input ->
                        let next_states = getNextStates current input
                        if not (Set.isEmpty next_states) && not (Set.contains next_states visited) then
                            next_states :: acc
                        else
                            acc
                    ) rest

                processStates next_visit new_visited new_states new_transitions'

    let start_states = NFA.ECLOSE nfa nfa.StartStates
    let new_states, new_transitions = processStates [start_states] Set.empty Set.empty Map.empty

    let new_accept =
        new_states
        |> Set.filter (fun states ->
            states 
            |> Set.exists (fun state -> 
                Set.contains state nfa.AcceptStates)
        )

    { States = new_states; Alphabet = nfa.Alphabet; TransitionFunction = new_transitions; StartState = start_states; AcceptStates = new_accept }

let make_nicer (dfa : DFA.DFA<Set<'State>, 'Input>) : DFA.DFA<'State, 'Input> =

    let new_states =
        dfa.States
        |> Set.fold (fun (acc, index) state ->
            let updatedMap = Map.add state index acc
            (updatedMap, index + 1)
        ) (Map.empty, 0)
        |> fst 

    let new_transitions =
        dfa.TransitionFunction
        |> Map.fold (fun acc (aState, input) bState ->
            let newAState = Map.find aState new_states
            let newBState = Map.find bState new_states
            let newTransition = (newAState, input)
            Map.add newTransition newBState acc
        ) Map.empty

    let newStartState = Map.find dfa.StartState new_states

    let new_accept =
        dfa.AcceptStates
        |> Set.fold (fun acc state ->
            Set.add (Map.find state new_states) acc
        ) Set.empty

    
    { States = new_states |> Map.toSeq |> Seq.map snd |> Set.ofSeq
; Alphabet = dfa.Alphabet; TransitionFunction = new_transitions; StartState = newStartState; AcceptStates = new_accept }

let printDFA (dfa: DFA.DFA<'State, 'input>) =
    printfn "DFA:"
    printfn "States: {%A}" dfa.States
    printfn "Start State: %A" dfa.StartState
    printfn "Accept States: {%A}" dfa.AcceptStates
    printfn "Transitions:\n%A" dfa.TransitionFunction

let printNFA (dfa: NFA.NFA<'State, 'input>) =
    printfn "DFA:"
    printfn "States: {%A}" dfa.States
    printfn "Start State: {%A}" dfa.StartStates
    printfn "Accept States: {%A}" dfa.AcceptStates
    printfn "Transitions:\n%A" dfa.TransitionFunction

let nfa_fig142 : NFA.NFA<'State, 'Input>= {
    States = set [1; 2; 3]
    Alphabet = set ['a'; 'b']
    TransitionFunction = 
        Map.ofList [
            ((1, None), set [3])
            ((1, Some 'b'), set [2])
            ((2, Some 'a'), set [2; 3])
            ((2, Some 'b'), set [3])
            ((3, Some 'a'), set [1])
        ]
    StartStates = set [1]
    AcceptStates = set [1]
}

let y : NFA.NFA<'State, 'Input>= {
    States = set [1; 2; 3; 4]
    Alphabet = set ['a'; 'b'; 'c']
    TransitionFunction = 
        Map.ofList [
            ((1, Some 'a'), set [2])
            ((2, Some 'c'), set [3])
            ((2, None), set [3])
            ((3, Some 'b'), set [4])
        ]
    StartStates = set [1]
    AcceptStates = set [4]
}

let x = determinize (removeEpsilonTransitions nfa_fig142)

printfn "States: %A" x.States
printfn "Transition Function: %A" x.TransitionFunction
printfn "Start States: %A" x.StartState
printfn "Accept States: %A\n" x.AcceptStates

