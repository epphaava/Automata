type NFA<'State, 'Input when 'State : comparison and 'Input : comparison> = {
    States: Set<'State>
    Alphabet: Set<'Input>
    TransitionFunction: Map<'State * 'Input option, Set<'State>>
    StartStates: Set<'State>
    AcceptStates: Set<'State>
}

type regex' =
    | Symbol of char
    | Lam
    | Empty
    | Concat of regex' * regex'
    | Union of regex' * regex'
    | Star of regex'

let rec parseregex' (tokens: char list) : regex' * char list =    
    // Parse primary expressions: single character or parenthesized expression
    let rec parsePrimary tokens =
        match tokens with
        | [] -> failwith "Unexpected end of input"
        | '(' :: rest ->
            let innerExp, remaining = parseregex' rest
            match remaining with
            | ')' :: more -> innerExp, more
            | _ -> failwith "Expected closing parenthesis"
        | 'ε' :: rest -> Lam, rest
        | '∅' :: rest -> Empty, rest
        | c :: rest -> Symbol c, rest

    // Handle Kleene star
    and parseStar tokens =
        let expr, remaining = parsePrimary tokens
        match remaining with
        | '*' :: rest -> Star expr, rest
        | _ -> expr, remaining

    // Concatenation
    and parseConcat tokens =
        let rec loop left tokens =
            match tokens with
            | [] | ')' :: _ | '+' :: _ -> left, tokens
            | _ ->
                let right, rest = parseStar tokens
                loop (Concat (left, right)) rest
        let first, rest = parseStar tokens
        loop first rest

    // Union (+)
    and parseUnion tokens =
        let left, remaining = parseConcat tokens
        match remaining with
        | '+' :: rest ->
            let right, more = parseUnion rest
            Union (left, right), more
        | _ -> left, remaining

    parseUnion tokens

let string_to_regex' (input: string) : regex' =
    let tokens = input |> Seq.toList
    let parsed, remaining = parseregex' tokens
    if remaining <> [] then
        failwithf "Unexpected leftover tokens: %A" remaining
    parsed

let rec regex_to_string' (R: regex') : string =
    match R with
    | Symbol c -> string c
    | Lam -> "ε"
    | Empty -> "∅"
    | Concat (R1, R2) -> "(" + regex_to_string' R1 + regex_to_string' R2 + ")"
    | Union (R1, R2) -> "(" + regex_to_string' R1 + "+" + regex_to_string' R2 + ")"
    | Star R1 -> "(" + regex_to_string' R1 + ")*"

let rec d' (R: regex') : regex' =
    match R with
    | Symbol _  | Empty -> Empty
    | Lam | Star _ -> Lam
    | Concat (R1, R2) -> if d' R1 = Lam && d' R2 = Lam then Lam else Empty
    | Union (R1, R2) -> if d' R1 = Lam || d' R2 = Lam then Lam else Empty


let concat_ext (s: Set<char * regex'>) (t: regex') : Set<char * regex'>=
    match t with
    | Empty -> Set.empty
    | Lam -> s
    | _ ->
        s
        |> Set.fold (fun acc (input, r) ->
            match r with
            | Empty -> Set.add (input, r) acc
            | Lam -> Set.add (input, t) acc
            | _ -> Set.add (input, Concat (r, t)) acc
        ) Set.empty

// linear form of r
let rec lf (r: regex') : Set<char * regex'> =

    //printfn "reg: %A, \n tail: %A \n" r tail
    match r with
    // lk 12
    | Empty -> Set.empty
    | Lam -> Set.empty
    | Symbol x -> set [(x, Lam)]
    | Union (x, y) -> Set.union (lf x) (lf y)
    | Star x -> concat_ext (lf x) r
    | Concat (x, y) ->
        if d' x = Lam then
            Set.union (concat_ext (lf x) y) (lf y)
        else 
            concat_ext (lf x) y


let get_alphabet' R : Set<'input> =
    let rec help (acc: Set<'input>) R : Set<'input> =
        match R with
        | Symbol a -> Set.add a acc
        | Lam | Empty -> acc
        | Concat (R1, R2) | Union (R1, R2) ->
            help (help acc R1) R2
        | Star a -> help acc a
    help Set.empty R


// small NFA with aat most ||t|| + 1 states
let regex_to_NFA (s: string) : NFA<regex', char> =
    let r = string_to_regex' s
    let alphabet = get_alphabet' r

    let rec help (states: Set<regex'>) (accept: Set<regex'>) (transition: Map<regex' * char option, Set<regex'>>) (not_checked: regex' list) alphabet : Set<regex'> * Set<regex'> * Map<regex' * char option , Set<regex'>> =

        match not_checked with
        | [] -> states, accept, transition
        | s :: rest ->
            let new_accept =
                if d' s = Lam then Set.add s accept
                else accept
            
            let linear = lf s

            let new_transition, new_not_checked, new_alphabet =
                linear
                |> Set.fold (fun (transition, not_checked, alphabet) (input, dest) ->
                    let new_alphabet = Set.add input alphabet
                    let new_not_checked = 
                        if not (Set.contains dest states) && not (List.contains dest not_checked) then
                            dest :: not_checked 
                        else 
                            not_checked
                    let new_transition =
                        match Map.tryFind (s, Some input) transition with
                        | Some prev_dest -> Map.add (s, Some input) (Set.add dest prev_dest) transition
                        | None -> Map.add (s, Some input) (set [dest]) transition

                    new_transition, new_not_checked, new_alphabet

                ) (transition, rest, alphabet)

            let new_states = Set.add s states
            help new_states new_accept new_transition new_not_checked new_alphabet

    let all_states, accepting, transition =
        help Set.empty Set.empty Map.empty [r] Set.empty

    { NFA.States = all_states
    ; NFA.Alphabet = alphabet
    ; NFA.TransitionFunction = transition
    ; NFA.StartStates = set [r]
    ; NFA.AcceptStates = accepting }



let printNFA' (nfa: NFA<'regex, 'input>) =

    let stateStrings = nfa.States |> Set.map regex_to_string' |> String.concat ", "
    let startStatesString = nfa.StartStates |> Set.map regex_to_string' |> String.concat ", "
    let acceptStateStrings = nfa.AcceptStates |> Set.map regex_to_string' |> String.concat ", "
    let transitionStrings =
        nfa.TransitionFunction 
        |> Map.toList
        |> List.map (fun ((state, input), nextStates) ->
            let nextStatesStr =
                nextStates
                |> Seq.map regex_to_string'
                |> String.concat ", "
            sprintf "(%s, '%A') → {%s}" (regex_to_string' state) input nextStatesStr)
        |> String.concat "\n"

    printfn "NFA:"
    printfn "States: {%s\n}" stateStrings
    printfn "\nStart States: %s\n" startStatesString
    printfn "\nAccept States: {%s}\n" acceptStateStrings
    printfn "\nTransitions:\n%s" transitionStrings

printNFA' (regex_to_NFA "(ab+b)*ba")