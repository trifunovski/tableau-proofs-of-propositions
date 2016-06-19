open Format

exception ERROR1
exception ERROR2
exception ERROR3
exception ERROR4
exception CONTRADICTED
exception FAILED
exception WRONG

type prop =
  Neg of prop | Var of string | Conj of prop * prop | Disj of prop * prop
  | Imp of prop * prop | ER | Top | Bot

type chk = bool
type form = bool * prop * chk
type tableau = Empty | Unary of tableau * (form list) | Node of tableau * (form list) * tableau

let rec matchUp (tv, p, x) = function
  | [] -> false
  | (true, Top, _)::_ -> true
  | (false, Bot, _)::_ -> true
  | (tv',p',_)::_ when (tv<>tv' && p=p') -> true
  | f::fs -> matchUp (tv, p, x) fs

let rec findContradict list1 = function
  | [] -> false
  | f::fs -> if matchUp f list1 then true else findContradict list1 fs

let unchecked = function
  | (_,_,false) -> true
  | _ -> false

let isAtom = function
  | (_,Var _, _) -> true
  | _ -> false

let isAlpha : form -> bool = function
  | (_, Neg _, _) -> true
  | (true, Conj _, _) -> true
  | (false, Disj _, _) -> true
  | (false, Imp _, _) -> true
  | _ -> false

let isBeta : form -> bool = function
  | (false, Conj _, _) -> true
  | (true, Disj _, _) -> true
  | (true, Imp _, _) -> true
  | _ -> false

let rec alphasInList = function
  | [] -> false
  | f :: fs -> ((isAlpha f) && (unchecked f)) || (alphasInList fs)

let rec betasInList = function
  | [] -> false
  | f :: fs -> ((isBeta f) && (unchecked f)) || (betasInList fs)

let rec find (pred : (form -> bool)) (forms : form list) =
  match forms with
    | [] -> ([],[])
    | f::fs ->  let (al,als) = find pred fs in
                if pred f then (f::al,als) else (al,f::als)

let rec addAlpha (alph : form) (t : tableau) : tableau =
  match t with
    | Empty -> Unary (Empty, [alph])
    | Unary (t1 , l) -> Unary (addAlpha alph t1, l)
    | Node (tl, olds, tr) -> Node (addAlpha alph tl, olds, addAlpha alph tr)

let rec addAlphas (a1 : form) (a2 : form) (t : tableau) : tableau =
  match t with
    | Empty -> Unary (Empty, a1::[a2])
    | Unary (t1 , l) -> Unary (addAlphas a1 a2 t1, l)
    | Node (tl, olds, tr) -> Node (addAlphas a1 a2 tl, olds, addAlphas a1 a2 tr)

let rec addBetas (f1 : form) (f2 : form) (t : tableau) : tableau =
  match t with
    | Empty -> raise ERROR4
    | Unary (Empty, l) -> Node (Unary(Empty, [f1]), l, Unary(Empty, [f2]))
    | Unary (t1 , l) -> Unary (addBetas f1 f2 t1, l)
    | Node (tl, olds, tr) -> Node (addBetas f1 f2 tl, olds, addBetas f1 f2 tr)

let evalSingleAlphaForm = function
    | (tv, Neg x, false) -> ((not tv, x, false),(tv, ER, true))
    | (true, Conj (p1,p2), false) -> ((true,p1, false),(true,p2, false))
    | (false, Disj (p1,p2), false) -> ((false,p1, false),(false,p2, false))
    | (false, Imp (p1,p2), false) -> ((true,p1, false),(false,p2, false))
    | _ -> raise ERROR2

let evalSingleBetaForm = function
    | (false, Conj (p1,p2), false) -> ((false,p1,false),(false,p2, false))
    | (true, Disj (p1,p2), false) -> ((true,p1,false),(true,p2, false))
    | (true, Imp (p1,p2), false) -> ((false,p1,false),(true,p2, false))
    | _ -> raise ERROR1

let rec isClosed (t : tableau) (cons : form list) : bool =
  match t with
    | Empty -> false
    | Unary (t , forms) -> let total = cons@forms in
                           if findContradict forms total then true
                           else (isClosed t total)
    | Node (tl , forms, tr) -> let total = cons@forms in
                               if findContradict forms total then true
                               else (isClosed tl total) && (isClosed tr total)

let rec thereIsAlphas = function
  | Empty -> false
  | Unary (t, forms) -> (alphasInList forms) || (thereIsAlphas t)
  | Node (l, forms, r) -> (alphasInList forms) || (thereIsAlphas l) ||  (thereIsAlphas r)

let rec thereIsBetas = function
    | Empty -> false
    | Unary (t, forms) -> (betasInList forms) || (thereIsBetas t)
    | Node (l, forms, r) -> (betasInList forms) || (thereIsBetas l) ||  (thereIsBetas r)

let rec findAbeta = function
  | [] -> raise ERROR2
  | f :: fs -> if (isBeta f) && (unchecked f) then ([],f,fs) else
               let (before, be, after) = findAbeta fs
               in (f::before, be, after)
let rec findAnAlpha = function
  | [] -> raise ERROR1
  | f :: fs -> if (isAlpha f) && (unchecked f) then ([],f,fs) else
               let (before, al, after) = findAnAlpha fs
               in (f::before, al, after)

let check = function
  | (tv, p, _) -> (tv, p, true)

let rec eval_stepAlpha (t : tableau) : tableau =
  if isClosed t [] then raise CONTRADICTED else
  match t with
  | Empty -> t
  | Unary (t1, forms) -> if alphasInList forms then
                            let (before, al, after) = findAnAlpha forms in
                            let (f1, f2) = evalSingleAlphaForm al in
                            let chkal = check al in
                            let newTab = Unary (t1, before@(chkal::after)) in
                            let (a,b,c) = f2 in
                            if b<>ER
                            then addAlphas f1 f2 newTab
                            else addAlpha f1 newTab
                        else Unary (eval_stepAlpha t1, forms)
  | Node (tl, forms, tr) -> if alphasInList forms then
                              let (before, al, after) = findAnAlpha forms in
                              let (f1, f2) = evalSingleAlphaForm al in
                              let chkal = check al in
                              let newTab = Node (tl, before@(chkal::after), tr) in
                              let (a,b,c) = f2 in
                              if b<>ER
                              then addAlphas f1 f2 newTab
                              else addAlpha f1 newTab
                            else if thereIsAlphas tl then
                                 Node (eval_stepAlpha tl, forms, tr)
                            else Node (tl, forms, eval_stepAlpha tr)

let rec eval_stepBeta (t : tableau) : tableau =
  if isClosed t [] then raise CONTRADICTED else
  match t with
  | Empty -> t
  | Unary (t1, forms) -> if betasInList forms then
                              let (before, be, after) = findAbeta forms in
                              let (f1, f2) = evalSingleBetaForm be in
                              let chkbe = check be in
                              let newTab = Unary (t1, before@(chkbe::after)) in
                                addBetas f1 f2 newTab
                         else Unary(eval_stepBeta t1, forms)
  | Node (tl, forms, tr) -> if betasInList forms then
                              let (before, be, after) = findAbeta forms in
                              let (f1, f2) = evalSingleBetaForm be in
                              let chkbe = check be in
                              let newTab = Node (tl, before@(chkbe::after), tr) in
                                addBetas f1 f2 newTab
                            else if thereIsBetas tl then
                                 Node (eval_stepBeta tl, forms, tr)
                            else Node (tl, forms, eval_stepBeta tr)

let rec eval t =
  try
      let t' = if thereIsAlphas t then eval_stepAlpha t
               else if thereIsBetas t then eval_stepBeta t
               else if isClosed t [] then raise CONTRADICTED
               else raise WRONG
      in eval t'
  with CONTRADICTED -> t;;

let tValue : bool -> string = function
    | true -> "T"
    | _ -> "F"

let rec showP = function
    | Top -> "$\\top$"
    | Bot -> "$\\bot$"
    | Neg p -> "($\\neg$" ^ (showP p) ^ ")"
    | Var p -> p
    | Conj (p1,p2) -> "(" ^ (showP p1) ^ " $\\wedge$ " ^ (showP p2) ^ ")"
    | Disj (p1,p2) -> "(" ^ (showP p1) ^ " $\\vee$ " ^ (showP p2) ^ ")"
    | Imp (p1,p2) -> "(" ^ (showP p1) ^ " $\\Rightarrow$ " ^ (showP p2) ^ ")"

let show ((v,p,c) : form) : string =
  match c with
   | false -> (tValue v) ^ (showP p)
   | _ -> (tValue v) ^ (showP p)

let max a b =
  if a >= b then a else b

let rec depth (t : tableau) : int =
  match t with
  | Empty -> 0
  | Unary (t1, _)-> 1 + depth t1
  | Node (tl, _, tr) -> 1 + max (depth tl) (depth tr)

let makeTableau (p : prop) : tableau = (Unary (Empty, [(false,p,false)]))

let rec printList = function
  | [] -> ""
  | [f] -> show f
  | f :: fs -> let restStr = printList fs
               in (show f) ^ "," ^ restStr


let tableauProof (p : prop) = eval (makeTableau p)


let rec printTab (t : tableau) (oc : out_channel) : unit =
  match t with
  | Empty -> ()
  | Unary (Empty, x) ->   let str1 = "\\AxiomC{$\\odot $}" in
                          let () = output oc str1 0 (String.length str1) in
                          let str = "\\UnaryInfC{" ^ (printList x) ^ "}" in
                                 output oc str 0 (String.length str)
  | Unary (t1, x) -> let () = printTab t1 oc in
                     let str = "\\UnaryInfC{" ^ (printList x) ^ "}" in
                        output oc str 0 (String.length str)
  | Node (l , x , r) -> let () = printTab l oc in
                        let () = printTab r oc in
                        let str = "\\BinaryInfC{" ^ (printList x) ^ "}" in
                            output oc str 0 (String.length str)

let tableauToLatex (t : tableau) (fileName : string) =
  let file = fileName ^ ".tex" in
  let oc = open_out file in
  let strStart = "\\documentclass[12pt]{article} \n
                  \\usepackage{bussproofs} \n
                  \\usepackage{amssymb} \n
                  \\usepackage{latexsym} \n
                  \\begin{document} \n
                  \\begin{prooftree} \n" in
  let strEnd = "\\end{prooftree} \\end{document}" in
  let comm = "pdflatex "^ file in
  let op = "open " ^ fileName ^".pdf" in
  output oc strStart 0 (String.length strStart);
  printTab t oc;
  output oc strEnd 0 (String.length strEnd);
  close_out oc;
  Sys.command comm;
  Sys.command op

let texProof (p : prop) (s : string) = tableauToLatex (tableauProof p) s

let f1 = Imp ((Conj((Var "A"),(Var "B"))),(Var "A"))
let f2 = Imp ( (Disj( (Conj((Var "C"),(Var "A"))) , (Conj((Var "C"),(Var "B"))) )),
              Conj ((Var "C") , (Disj ((Var "A"),(Var "B")))))
let demorgan1 = Imp((Neg (Conj((Var "P"),(Var "Q")))) , (Disj (Neg(Var "P") , (Neg(Var "Q")))))
let demorgan2 = Imp((Disj (Neg(Var "P") , (Neg(Var "Q")))) , (Neg (Conj((Var "P"),(Var "Q")))) )
let demorgan1and2 = Conj(demorgan1 , demorgan2)
let p1 = Imp ((Disj ((Conj ((Var "C") , (Var "A"))) , (Conj ((Var "C") , (Var "B"))))) ,
              (Conj ((Var "C") , (Disj ((Var "A"), (Var "B"))))))
let p2 = Imp ( ((Conj ( (Neg (Var "C")) , (Conj ((Neg (Var "A")), (Imp ((Neg( Disj((Var "A") , (Var "C")))) , (Var "B"))) )))) ) , (Var "B"))
