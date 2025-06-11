(* 
kaks varianti:
1. keel on kolm hulka
2. keelt kirjeldab kolm regulaarvaldist

esimene suht jube ärme seda tee
*)

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



let r_1 = string_to_regex "x"
let r_2 = string_to_regex "y"
let r_3 = string_to_regex "z"

let L = [r_1, r_2, r_3]

let w = "xxx"