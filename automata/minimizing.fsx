#load "NFA.fsx"
#load "DFA.fsx"
#load "determinizing.fsx"
#load "../derivative_of_regex/derivative.fsx"

let reverse (dfa: DFA.DFA<'State, 'Input>) : NFA.NFA<'State, 'Input> =

    let newStartStates = dfa.AcceptStates
    let newAcceptStates = set [dfa.StartState]

    let newTransitions =
        dfa.TransitionFunction
        |> Map.fold (fun (acc: Map<'State * 'Input option, Set<'State>>) (aState, input) bState ->
            let newTransition =
                match Map.tryFind (bState, Some input) acc with
                | Some x -> Set.add aState x
                | None -> set [aState]
            Map.add (bState, Some input) newTransition acc
        ) Map.empty

    { States = dfa.States; Alphabet = dfa.Alphabet; TransitionFunction = newTransitions; StartStates = newStartStates; AcceptStates = newAcceptStates }


let minimize_brz (dfa: DFA.DFA<'State, 'Input>) =
    Determinizing.make_nicer (Determinizing.determinize (reverse (Determinizing.make_nicer (Determinizing.determinize (reverse dfa)))))


let order a b =
    if a < b then a,b
    else b, a

let table_filling (dfa: DFA.DFA<'state, 'input>) =

    let not_eq = 
        dfa.States
        |> Set.fold (fun acc s1 ->
            dfa.States
            |> Set.fold (fun acc' s2 ->
                let x, y = order s1 s2
                if List.contains (x, y) acc' then acc'
                else if s1 <> s2 && Set.contains s1 dfa.AcceptStates <> Set.contains s2 dfa.AcceptStates then
                    (x, y) :: acc'
                else
                    acc'
            ) acc
        ) []

    let rec help checked not_checked =
        match not_checked with
        | [] -> checked
        | (x, y) :: rest ->
            let new_pairs =
                dfa.Alphabet
                |> Set.fold (fun acc input ->
                    let matching_x =
                        dfa.TransitionFunction
                        |> Map.toList
                        |> List.choose (fun ((a, b), v) ->
                            if b = input && v = x then Some a else None
                        )

                    let matching_y =
                        dfa.TransitionFunction
                        |> Map.toList
                        |> List.choose (fun ((a, b), v) ->
                            if b = input && v = y then Some a else None
                        )

                    let pairs =
                        matching_x
                        |> List.collect (fun a ->
                            matching_y
                            |> List.choose (fun b ->
                                if a <> b then Some (order a b) else None
                            )
                        )
                        |> Set.ofList
                        |> Set.toList
                    let new_not_checked =
                        pairs |> List.filter (fun p -> not (Set.contains p checked))

                    acc @ new_not_checked
                ) []
            help (Set.add (x, y) checked) (rest @ new_pairs)
    
    let not_equal_pairs = help Set.empty not_eq

    dfa.States
    |> Set.fold (fun acc item1 ->
        dfa.States
        |> Set.filter (fun item2 -> item1 < item2)
        |> Set.fold (fun acc' item2 -> Set.add (item1, item2) acc') acc
    ) Set.empty
    |> Set.toList
    |> List.filter (fun pair -> not (Set.contains pair not_equal_pairs))

let minimize_table (dfa: DFA.DFA<'state, 'input>) : DFA.DFA<Set<'state>, 'input> =

    let equal_pairs = table_filling dfa

    let rec make_blocks pairs queue block = 
        match pairs with
        | [] -> 
            if Set.isEmpty queue then
                [block]
            else
                let new_pairs = queue |> Set.toList
                [block] @ make_blocks new_pairs Set.empty Set.empty
        | (x, y) :: rest ->
            if Set.isEmpty block then 
                make_blocks rest queue (set [x; y])
            else if Set.contains x block || Set.contains y block then
                let new_block =
                    block 
                    |> Set.add x
                    |> Set.add y
                make_blocks rest queue new_block
            else
                make_blocks rest (Set.add (x, y) queue) block
    
    let rec get_new_states acc states = 
        match states with
        | [] -> acc
        | s :: rest ->
            if List.exists (fun block -> Set.contains s block ) acc then
                get_new_states acc rest 
            else 
                get_new_states (set [s] :: acc) rest
            
    let rec get_new_transition (acc: Map<Set<'state> * 'input, Set<'state>>) (not_checked: Set<'state> list) states=
        match not_checked with
        | [] -> acc
        | state_set :: rest ->
            let new_acc =
                dfa.Alphabet
                |> Set.fold (fun acc' input ->
                    let state = Set.toSeq state_set |> Seq.head
                    match Map.tryFind (state, input) dfa.TransitionFunction with
                    | Some value ->
                        let dest = List.find (fun x -> Set.contains value x) states
                        Map.add (state_set, input) dest acc'
                    | None -> acc'
                ) acc
            get_new_transition new_acc rest states


    let new_states = get_new_states (make_blocks equal_pairs Set.empty Set.empty) (Set.toList dfa.States) 

    let new_transition = get_new_transition Map.empty new_states new_states

    let new_start = List.find (fun x -> Set.contains dfa.StartState x) new_states
    let new_accept =
        new_states
        |> List.filter (fun state ->
            Set.exists (fun x -> Set.contains x state) dfa.AcceptStates
        )

    { States = new_states |> Set.ofList; Alphabet = dfa.Alphabet; TransitionFunction = new_transition; StartState = new_start; AcceptStates = new_accept |> Set.ofList }


let compare_dfa (dfa1: DFA.DFA<'state, 'input>) (dfa2: DFA.DFA<'state, 'input>) =

    let rec help (s1, s2) not_checked checked =

        printfn "current s1: %A s2: %A acc: %A" s1 s2 not_checked
        if Set.contains s1 dfa1.AcceptStates <> Set.contains s2 dfa2.AcceptStates then
            false
        else
            let dests1 =
                dfa1.TransitionFunction 
                |> Map.toList
                |> List.choose (fun ((s, input), dest) ->
                    if s = s1 then Some (input, dest) else None
                )
            let dests2 =
                dfa2.TransitionFunction 
                |> Map.toList
                |> List.choose (fun ((s, input), dest) ->
                    if s = s2 then Some (input, dest) else None
                )
            
            let inputs1 = dests1 |> List.map fst |> Set.ofList
            let inputs2 = dests2 |> List.map fst |> Set.ofList

            if inputs1 <> inputs2 then 
                false
            else
                let next_states =
                    dests1
                    |> List.choose (fun (input1, dest1) ->
                        dests2
                        |> List.tryFind (fun (input2, _) -> input1 = input2)
                        |> Option.map (fun (_, dest2) ->
                            order dest1 dest2
                        )
                    )
                    |> List.filter (fun pair -> not (Set.contains pair checked) && not (pair = (s1, s2)))
                    |> Set.ofList

                let waiting_list = Set.union next_states not_checked

                if Set.isEmpty waiting_list then true
                else 
                    let head = Set.minElement waiting_list
                    help head (Set.remove head waiting_list) (Set.add (order s1 s2) checked)


    help (dfa1.StartState, dfa2.StartState) (set []) (set [])



let printDFA (dfa: DFA.DFA<'state, 'input>) =
    printfn "DFA:"
    printfn "States: {%A}" dfa.States
    printfn "Start State: %A" dfa.StartState
    printfn "Accept States: {%A}" dfa.AcceptStates
    printfn "Transitions:\n%A" dfa.TransitionFunction

let get_comparison x y =

    let a = Derivative.regex_to_DFA (Derivative.string_to_regex x)
    let b = Derivative.regex_to_DFA (Derivative.string_to_regex y)
    printfn "%A" (compare_dfa a b)

let y : DFA.DFA<'State, 'Input> = {
    States = set [0; 1; 2; 3; 4; 5]
    Alphabet = set [1; 0]
    TransitionFunction = 
        Map.ofList [
            ((0, 0), 3)
            ((0, 1), 1)
            ((1, 0), 2)
            ((1, 1), 5)
            ((2, 0), 2)
            ((2, 1), 5)
            ((3, 0), 0)
            ((3, 1), 4)
            ((4, 0), 2)
            ((4, 1), 5)
            ((5, 0), 5)
            ((5, 1), 5)

        ]
    StartState = 0
    AcceptStates = set [1; 2; 4]
}

//let min_y = minimize_brz y


//Determ.printDFA x

//let pairs = table_filling y
//printfn "%A" pairs


let x : DFA.DFA<'State, 'Input> = {
    States = set ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H']
    Alphabet = set [1; 0]
    TransitionFunction = 
        Map.ofList [
            ('A', 0), 'B'
            ('A', 1), 'F'
            ('B', 0), 'G'
            ('B', 1), 'C'
            ('C', 0), 'A'
            ('C', 1), 'C'
            ('D', 0), 'C'
            ('D', 1), 'G'
            ('E', 0), 'H'
            ('E', 1), 'F'
            ('F', 0), 'C'
            ('F', 1), 'G'
            ('G', 0), 'G'
            ('G', 1), 'E'
            ('H', 0), 'G'
            ('H', 1), 'C'
        ]
    StartState = 'A'
    AcceptStates = set ['C']
}

//let min_x = minimize_table x

//printDFA min_x

//let min_y = minimize_table y

//printDFA min_y

//printfn "%A" (compare_dfa x x)

get_comparison "bb*" "b(b)*"