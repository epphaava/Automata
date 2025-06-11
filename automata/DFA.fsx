type DFA<'State, 'Input when 'State : comparison and 'Input : comparison> = {
    States : Set<'State>
    Alphabet : Set<'Input>
    TransitionFunction : Map<'State * 'Input, 'State>
    StartState : 'State
    AcceptStates : Set<'State>
}


let rec runDFA (dfa: DFA<'State, 'Input>) currentState input =
    match input with
    | [] -> dfa.AcceptStates.Contains(currentState)
    | head :: tail -> 
        match dfa.TransitionFunction.TryFind (currentState, head) with
        | Some nextState -> runDFA dfa nextState tail
        | None -> false


