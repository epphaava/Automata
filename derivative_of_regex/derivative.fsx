#load "../automata/DFA.fsx"
#load "../automata/NFA.fsx"
#load "../automata/determinizing.fsx"

type RegEx =
    | Symbol of char
    | Lam
    | Empty
    | Concat of RegEx * RegEx
    | Union of RegEx * RegEx
    | Star of RegEx
    | Complement of RegEx
    | Intersection of RegEx * RegEx

let rec d (R: RegEx) : RegEx =
    match R with
    | Symbol _  | Empty -> Empty
    | Lam | Star _ -> Lam
    | Concat (R1, R2) | Intersection (R1, R2) -> if d R1 = Lam && d R2 = Lam then Lam else Empty
    | Union (R1, R2) -> if d R1 = Lam || d R2 = Lam then Lam else Empty
    | Complement R1 -> if d R1 = Lam then Empty else Lam

let rec derivative (R: RegEx) (a: 'input) : RegEx =
    match R with
    | Symbol x -> if x = a then Lam else Empty
    | Lam | Empty -> Empty
    | Concat (R1, R2) -> 
        let d1 = derivative R1 a
        Union (Concat (d1, R2), Concat (d R1, derivative R2 a))
    | Union (R1, R2) -> Union (derivative R1 a, derivative R2 a)
    | Star R1 -> 
        let d = derivative R1 a
        if d = Lam then Star R1
        else Concat (d, Star R1)
    | Complement R1 -> Complement (derivative R1 a)
    | Intersection (R1, R2) -> Intersection (derivative R1 a, derivative R2 a)

let rec merge R1 R2 : RegEx =
    match R1, R2 with
    | Union (a, b), Union (x, y) -> 
        if a = Empty then merge b (Union (x, y))
        else if x = Empty then merge y (Union (a, b))
        else 
            match compare a x with
            | z when z < 0 -> Union (a, merge b (Union (x, y)))
            | z when z = 0 -> Union (a, merge b y)
            | _ -> Union (x, merge y (Union (a, b)))
    | Union (a, b), x | x, Union (a, b) ->
        if a = Empty then merge b x
        else if x = Empty then merge a b
        else 
            match compare a x with
            | z when z < 0 -> Union (a, merge b x)
            | z when z = 0 -> merge a b
            | _ -> Union (x, merge a b)
    | x, y -> 
        if x = Empty then y
        else if y = Empty then x
        else 
            match compare x y with
            | a when a < 0 -> Union (x, y)
            | a when a = 0 -> x
            | _ -> Union (y, x)

let rec reduce R : RegEx =
    match R with
    | Union (a, b) ->
        let a' = reduce a
        let b' = reduce b
        merge a' b'
    | Concat (Lam, a) | Concat (a, Lam) -> a
    | _ -> R

let get_alphabet R : Set<'input> =
    let rec help (acc: Set<'input>) R : Set<'input> =
        match R with
        | Symbol a -> Set.add a acc
        | Lam | Empty -> acc
        | Concat (R1, R2) | Union (R1, R2) | Intersection (R1, R2) ->
            help (help acc R1) R2
        | Star a | Complement a -> help acc a
    help Set.empty R


let rec regex_to_DFA (R: RegEx) : DFA.DFA<'state, 'input> =

    let alph = get_alphabet R

    let rec help (waiting : RegEx List) (states : Set<RegEx>) (alphabet: Set<'input>) (transition : Map<RegEx * 'input, RegEx>) (start : 'state) (accept : Set<RegEx>) : DFA.DFA<RegEx, 'input> =
        match waiting with
        | [] ->
            { DFA.States = states; DFA.Alphabet = alphabet; DFA.TransitionFunction = transition; DFA.StartState = start; DFA.AcceptStates = accept }
        | s :: rest ->
            let  newTransition, newStates, newWaiting, updatedAccept =
                alphabet 
                |> Set.fold (fun (trans, st, wait, accept) a ->
                    let deriv = reduce (derivative s a)
                    let updatedTrans = 
                        Map.add (s, a) deriv trans
                    let updatedStates = Set.add deriv st
                    let updatedWaiting = if Set.contains deriv st then wait else deriv :: wait
                    let updatedAccept = if d deriv = Lam then Set.add deriv accept else accept

                    updatedTrans, updatedStates, updatedWaiting, updatedAccept
                ) (transition, states, rest, accept)

            help newWaiting newStates alphabet newTransition start updatedAccept

    help [R] (set [R]) alph Map.empty R (if d R = Lam then set [R] else Set.empty)
       
let regex_to_NFA (R: RegEx) : NFA.NFA<'state, 'input> =
    let alph = get_alphabet R

    let rec help (waiting : RegEx List) (states : Set<RegEx>) (alphabet: Set<'input>) (transition : Map<RegEx * 'input, RegEx>) (starts : Set<RegEx>) (accept : Set<RegEx>) : NFA.NFA<RegEx, 'input> =
        match waiting with
        | [] ->
            { NFA.States = states; NFA.Alphabet = alphabet; NFA.TransitionFunction = transition; NFA.StartStates = starts; NFA.AcceptStates = accept }
        | s :: rest ->
            let  newTransition, newStates, newWaiting, updatedAccept =
                alphabet 
                |> Set.fold (fun (trans, st, wait, accept) a ->
                    let deriv = reduce (derivative s a)
                    let updatedTrans = 
                        Map.add (s, a) deriv trans
                    let updatedStates = Set.add deriv st
                    let updatedWaiting = if Set.contains deriv st then wait else deriv :: wait
                    let updatedAccept = if d deriv = Lam then Set.add deriv accept else accept

                    updatedTrans, updatedStates, updatedWaiting, updatedAccept
                ) (transition, states, rest, accept)

            help newWaiting newStates alphabet newTransition start updatedAccept

    help [R] (set [R]) alph Map.empty R (if d R = Lam then set [R] else Set.empty)



// from chatgpt for convenience
let rec parseRegEx (tokens: char list) : RegEx * char list =
    let rec parsePrimary tokens =
        match tokens with
        | [] -> failwith "Unexpected end of input"
        | '(' :: rest -> 
            let innerExp, remaining = parseRegEx rest
            match remaining with
            | ')' :: more -> innerExp, more
            | _ -> failwith "Mismatched parentheses"
        | x :: rest -> Symbol x, rest
    
    and parseStar tokens =
        let expr, remaining = parsePrimary tokens
        match remaining with
        | '*' :: rest -> Star expr, rest  // Apply Kleene star to the previous expression
        | _ -> expr, remaining

    and parseComplement tokens =
        let expr, remaining = parseStar tokens
        match remaining with
        | '\'' :: rest -> Complement expr, rest  // Apply complement to the previous expression
        | _ -> expr, remaining

    and parseConcat tokens =
        let rec loop left tokens =
            match tokens with
            | [] | ')' :: _ | '+' :: _  :: _ -> left, tokens
            | _ -> 
                let right, remaining = parseComplement tokens  // Complement has higher precedence
                loop (Concat (left, right)) remaining
        let first, rest = parseComplement tokens
        loop first rest

    and parseIntersection tokens =
        let rec loop left tokens =
            match tokens with
            | [] | ')' :: _ | '&' :: _  :: _ -> left, tokens
            | _ -> 
                let right, remaining = parseIntersection tokens  // Complement has higher precedence
                loop (Intersection (left, right)) remaining
        let first, rest = parseIntersection tokens
        loop first rest

    and parseUnion tokens =
        let left, remaining = parseConcat tokens
        match remaining with
        | '+' :: rest -> 
            let right, more = parseUnion rest
            Union (left, right), more
        | _ -> left, remaining

    parseUnion tokens

let string_to_regex (s: string) : RegEx =
    let tokens = Seq.toList s
    let result, remaining = parseRegEx tokens
    if remaining <> [] then failwith "Invalid regex format"
    else result

let rec regex_to_string (R: RegEx) : string =
    match R with
    | Symbol c -> string c
    | Lam -> "ε"
    | Empty -> "∅"
    | Concat (R1, R2) -> "(" + regex_to_string R1 + regex_to_string R2 + ")"
    | Union (R1, R2) -> "(" + regex_to_string R1 + "+" + regex_to_string R2 + ")"
    | Star R1 -> "(" + regex_to_string R1 + ")*"
    | Complement R1 -> "¬(" + regex_to_string R1 + ")"
    | Intersection (R1, R2) -> "(" + regex_to_string R1 + "&" + regex_to_string R2 + ")"

let rec regex_to_string_readable (R: RegEx) : string =
    match R with
    | Symbol c -> string c
    | Lam -> "ε"
    | Empty -> "∅"
    | Concat (R1, R2) ->
        let x = regex_to_string_readable R1
        let y = regex_to_string_readable R2
        match x with
        | "ε" -> y
        | "∅" -> "∅"
        | _ -> 
            match y with
            | "ε" -> x
            | "∅" -> "∅"
            | _ -> "(" + x + y + ")"
    | Union (R1, R2) -> 
        let x = regex_to_string_readable R1
        let y = regex_to_string_readable R2
        match x with
        | "∅" -> y
        | _ -> 
            match y with
            | "∅" -> x
            | _ -> "(" + x + "+" + y + ")"
    | Star R1 -> "(" + regex_to_string_readable R1 + ")*"
    | Complement R1 -> "¬(" + regex_to_string_readable R1 + ")"
    | Intersection (R1, R2) -> 
        let x = regex_to_string_readable R1
        let y = regex_to_string_readable R2
        if x = y then x else
        match x with
        | "∅" -> "∅"
        | _ -> 
            match y with
            | "ε" -> "ε"
            | "∅" -> "∅"
            | _ -> "(" + x + "&" + y + ")"

let printDFA (dfa: DFA.DFA<RegEx, 'input>) =

    let stateStrings = dfa.States |> Set.map regex_to_string |> String.concat ", "
    let startStateString = regex_to_string dfa.StartState
    let acceptStateStrings = dfa.AcceptStates |> Set.map regex_to_string |> String.concat ", "

    let transitionStrings =
        dfa.TransitionFunction 
        |> Map.toList
        |> List.map (fun ((state, input), nextState) ->
            sprintf "(%s, '%c') → %s" (regex_to_string state) input (regex_to_string nextState))
        |> String.concat "\n"

    printfn "DFA:"
    printfn "States: {%s}" stateStrings
    printfn "Start State: %s" startStateString
    printfn "Accept States: {%s}" acceptStateStrings
    printfn "Transitions:\n%s" transitionStrings


let make_nicer (initialDFA : DFA.DFA<RegEx, 'input>) = 
    let stateMap, _ =
        initialDFA.States
        |> Set.fold (fun (acc, index) state ->
            let updatedMap = Map.add state index acc
            updatedMap, index + 1
        ) (Map.empty, 0)
    let newTransition =
        initialDFA.TransitionFunction
        |> Map.fold (fun acc (aState, input) bState ->
            let newAState = Map.find aState stateMap
            let newBState = Map.find bState stateMap
            Map.add (newAState, input) newBState acc
        ) Map.empty
    let newStartState = Map.find initialDFA.StartState stateMap
    let newAcceptStates =
        initialDFA.AcceptStates
        |> Set.fold (fun acc state -> Set.add (Map.find state stateMap) acc) Set.empty

    { DFA.States = stateMap |> Map.toSeq |> Seq.map snd |> Set.ofSeq
    ; DFA.Alphabet = initialDFA.Alphabet
    ; DFA.TransitionFunction = newTransition
    ; DFA.StartState = newStartState
    ; DFA.AcceptStates = newAcceptStates }

let print_derivative r der =
    let regex = string_to_regex r
    printfn "from %A to %A \n" (regex_to_string regex) (regex_to_string_readable ( reduce (derivative regex der)))

print_derivative "1+0+1" 'ε'

print_derivative "bb*" 'b'

let regex_DFA2 = "bb*"
let DFA2 =  regex_to_DFA (string_to_regex regex_DFA2)
printDFA DFA2