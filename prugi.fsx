
(*type NFA<'State, 'Input, 'Transition when 'State : comparison and 'Input : comparison and 'Transition : comparison> = {
    States: Set<'State>
    Alphabet: Set<'Input>
    TransitionFunction: Map<'State * 'Transition, Set<'State>>
    StartStates: Set<'State>
    AcceptStates: Set<'State>
}



let checkIfAllowsEpsilon (nfa: NFA<'State, 'Input, 'Transition>) : bool =
    nfa.TransitionFunction
    |> Map.exists (fun (_, t) _ -> 
        match box t with
        | :? Option<'Input> -> true
        | _ -> false
    )


let runNFAwithOption (nfa: NFA<'State, 'Input, 'Input option>) input =
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

let runNFAwithoutOption (nfa: NFA<'State, 'Input, 'Input>) input=
    let rec run currentStates remainingInput =
        match remainingInput with
        | [] -> true
        | nextInput :: rest ->
            let nextStates =
                currentStates 
                |> Set.map (fun state ->
                    match nfa.TransitionFunction.TryFind (state, nextInput) with
                    | Some next -> next
                    | None -> Set.empty
                )
                |> Set.unionMany
            run nextStates rest
    run nfa.StartStates (Seq.toList input)

let runNFA (nfa: NFA<'State, 'Input, 'Transition>) (input: seq<'Input>) =
    if checkIfAllowsEpsilon nfa then
        runNFAwithOption (unbox nfa) (Seq.toList input)
    else
        runNFAwithoutOption (unbox nfa) (Seq.toList input)

    

#load "DFA.fsx"
#load "NFA.fsx"
#load "determiniseerime.fsx"

// Eliminate e-transitions
let eliminateEpsilon (nfa: NFA.NFA<'State, 'Input>) : NFA.NFA<'State, 'Input> =
    let mutable acceptStates = nfa.AcceptStates
    let (transitionFunction : Map<'State * 'Input option, Set<'State>>) = 
        nfa.States
        |> Set.fold (fun (acc: Map<'State * 'Input option, Set<'State>>) state ->
            let regularTransitions = 
                nfa.TransitionFunction
                |> Map.filter (fun (s, input) _ -> s = state && input.IsSome)

            let epsilonNextStates = NFA.ECLOSE nfa (set [state])


            let newTransitions =
                nfa.TransitionFunction 
                |> Map.fold (fun (acc: Map<'State * 'Input option, Set<'State>>) (startState, input) destinationStates ->
                    if Set.contains state destinationStates then

                        let combinedDestStates = Set.union destinationStates epsilonNextStates
                        acc 
                        |> Map.change (startState, input) (fun existingDestStates ->

                            match existingDestStates with
                            | Some existing -> Some (Set.union existing combinedDestStates)
                            | None -> Some combinedDestStates
                        
                        )                      
                    else
                        acc
                ) acc

            if not (Set.isEmpty (Set.intersect epsilonNextStates nfa.AcceptStates)) then 
                acceptStates <- Set.add state acceptStates

            Map.fold (fun (acc: Map<'State * 'Input option, Set<'State>>) (startState, (input : 'Input option)) destinationState ->
                if state = startState && input.IsSome then
                    Map.add (startState, input) destinationState acc
                else
                    acc
            ) regularTransitions newTransitions

        ) Map.empty

    { States = nfa.States; Alphabet = nfa.Alphabet; TransitionFunction = transitionFunction; StartStates = nfa.StartStates; AcceptStates = acceptStates }



let nfa1 : NFA.NFA<'State, 'Input>= {
    States = set ["q0"; "q1"; "q2"]
    Alphabet = set ['a']
    TransitionFunction = 
        Map.ofList [
            (("q0", None), set ["q1"])
            (("q1", None), set ["q2"])
            (("q2", Some 'a'), set ["q0"])
        ]
    StartStates = set ["q0"]
    AcceptStates = set ["q2"]
}

let nfa1NoEpsilon = eliminateEpsilon nfa1

printfn "States: %A" nfa1NoEpsilon.States
printfn "Transition Function: %A" nfa1NoEpsilon.TransitionFunction
printfn "Start States: %A" nfa1NoEpsilon.StartStates
printfn "Accept States: %A" nfa1NoEpsilon.AcceptStates



let rec compare_regex (R1': RegEx) (R2': RegEx) : bool =
    let R1 = reduce R1'
    let R2 = reduce R2'
    if R1 = R2 then true else
    match R1 with
    | Symbol a -> R2 = Symbol a
    | Lam -> R2 = Lam
    | Empty -> R2 = Empty

    | Concat (a, b) -> 
        match a with 
            | Concat (x, y) -> compare_regex R2 (Concat (x, Concat (y, b)))
            | Union (x, y) -> compare_regex R2 (Union (Concat (x, b), Concat (y, b)))
            | _ -> false
        ||
        match b with 
            | Concat (x, y) -> compare_regex R2 (Concat (Concat (a, x), y))
            | Union (x, y) -> compare_regex R2 (Union (Concat (a, x), Concat (a, y)))
            | _ -> false

    | Union (a, b) -> 
        compare_regex R2 (Union (b, a)) ||
        (match a with 
            | Union (x, y) -> compare_regex R2 (Union (x, Union (y, b)))
            | _ -> false
        ) ||
        (match b with 
            | Union (x, y) -> compare_regex R2 (Union (Union (a, x), y))
            | _ -> false
        )
    | Star a -> 
        match R2 with
        | Star b -> compare_regex a b
        | _ -> false
    | Complement a -> 
        match R2 with
        | Complement b -> compare_regex a b
    | Intersection (a, b) ->
        match R2 with
        | Intersection (x, y) -> compare_regex a x && compare_regex b y || compare_regex a y && compare_regex b x


// so i can read :)
let rec reduce (R: RegEx) : RegEx =
    match R with
    | Symbol _ -> R
    | Lam -> Lam
    | Empty -> Empty

    | Concat (Lam, a) | Concat (a, Lam) -> reduce a
    | Concat (Empty, _) | Concat (_, Empty) -> Empty
    | Concat (a, b) -> 
        let a' = reduce a
        let b' = reduce b
        match a', b' with
        | Empty, _ | _, Empty -> Empty
        | Lam, x | x, Lam -> x
        | _ -> Concat (a', b')

    | Union (a, Empty) | Union (Empty, a) -> reduce a
    | Union (a, Lam) | Union (Lam, a) when check_lam a -> reduce a
    | Union (a, b) ->
        let a' = reduce a
        let b' = reduce b
        if a' = b' then a' else
        match a', b' with
        | Empty, x | x, Empty -> reduce x
        | Union (x, y), z | Union (y, x), z | z, Union (x, y) | z, Union (y, x) when x = z -> Union (x, y)
        | _ -> Union (a', b')

    | Star Empty -> Lam
    | Star Lam -> Lam
    | Star (Star a) -> Star (reduce a) // ?
    | Star a -> Star (reduce a)

    | Complement R1 -> Complement (reduce R1)
    | Intersection (R1, R2) -> Intersection (reduce R1, reduce R2)
*)