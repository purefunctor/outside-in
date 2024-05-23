open PPrint
open Syntax

let is_ty_application = function
  | Application _ -> true
  | _ -> false

let parens_if c d = if c then parens d else d

let rec pretty_ty =
  let rec aux (t : ty) =
    match t with
    | Application (f, a) ->
        let f = aux f |> parens_if (is_ty_application f) in
        let a = aux a |> parens_if (is_ty_application a) in
        f ^^ space ^^ a
    | Forall (variables, predicates, t) ->
        let variables =
          match variables with
          | [] -> failwith "invariant violated: empty variables"
          | _ ->
              let variables =
                flow_map space
                  (fun variable -> string "^" ^^ string variable)
                  variables
              in
              string "forall" ^^ space ^^ variables ^^ string "."
        in
        let predicates =
          let list =
            match predicates with
            | [] -> empty
            | [ predicate ] -> pretty_ty_predicate predicate
            | _ ->
                flow_map (comma ^^ space) pretty_ty_predicate predicates
                |> parens
          in
          list ^^ space ^^ string "=>"
        in
        let t = aux t in
        flow space [ variables; predicates; t ]
    | Function (a, r) ->
        let a = aux a in
        let r = aux r in
        a ^^ string " -> " ^^ r
    | Skolem s -> string "^" ^^ string s
    | Unification (n, u) -> pretty_ty_unification n u
    | Int -> string "Int"
    | Bool -> string "Bool"
    | List t -> string "List" ^^ space ^^ aux t
  in
  aux

and pretty_ty_predicate =
  let aux (p : ty_predicate) =
    match p with
    | Eq t -> string "Eq" ^^ space ^^ pretty_ty t
    | Unify (x_ty, y_ty) ->
        pretty_ty x_ty ^^ space ^^ string "~" ^^ space ^^ pretty_ty y_ty
  in
  aux

and pretty_ty_unification n u =
  let n = Option.map string n |> Option.value ~default:empty in
  let u = !u |> Unification.get_identifier |> string_of_int |> PPrint.string in
  string "?" ^^ n ^^ u

let pretty_tm =
  let rec aux (e : tm) =
    match e with
    | Apply (f, a) -> aux f ^^ space ^^ aux a
    | Lambda (x, e) -> string "\\" ^^ string x ^^ dot ^^ space ^^ aux e
    | Variable v -> string v
    | Int i -> string_of_int i |> string
    | Bool b -> string_of_bool b |> string
    | List es -> flow_map (comma ^^ space) aux es |> brackets
  in
  aux

let render_to_string document =
  let buffer = Buffer.create 0 in
  PPrint.ToBuffer.pretty 1.0 80 buffer document;
  buffer |> Buffer.contents

let render_ty t = t |> pretty_ty |> render_to_string
let render_ty_predicate p = p |> pretty_ty_predicate |> render_to_string
let render_ty_unification n u = pretty_ty_unification n u |> render_to_string
let render_tm e = e |> pretty_tm |> render_to_string
