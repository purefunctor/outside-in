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
    | Constructor c -> string c
    | Forall (variables, predicates, t) ->
        let variables =
          match variables with
          | [] -> string "forall / ."
          | _ ->
              let variables =
                flow_map space
                  (fun variable -> string "^" ^^ string variable)
                  variables
              in
              string "forall" ^^ space ^^ variables ^^ string "."
        in
        let predicates =
          let pre = space in
          let post = space ^^ string "=>" ^^ space in
          match predicates with
          | [] -> pre
          | [ predicate ] -> pretty_ty_predicate predicate |> enclose pre post
          | _ ->
              flow_map (comma ^^ space) pretty_ty_predicate predicates
              |> parens |> enclose pre post
        in
        let t = aux t in
        variables ^^ predicates ^^ t
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

and pretty_ty_constraint =
  let rec aux (c : ty_constraint) =
    match c with
    | Predicate p -> pretty_ty_predicate p
    | Implication (given, local) ->
        let plural_or_zero v = List.is_empty v || List.length v > 1 in
        let separated vs = flow_map (comma ^^ space) aux vs in
        let given = given |> separated |> parens_if (plural_or_zero given) in
        let local = local |> separated |> parens_if (plural_or_zero local) in
        flow space [ given; string "=>"; local ]
  in
  aux

let pretty_pt =
  let rec aux (p : pt) =
    match p with
    | PtApply (f, a) -> aux f ^^ space ^^ flow_map space aux a
    | PtConstructor c -> string c
    | PtVariable v -> string v
    | PtInt i -> string_of_int i |> string
    | PtBool b -> string_of_bool b |> string
    | PtList ps -> flow_map (comma ^^ space) aux ps |> brackets
  in
  aux

let pretty_tm =
  let rec aux (e : tm) =
    match e with
    | Apply (f, a) -> aux f ^^ space ^^ aux a
    | Constructor c -> string c
    | Lambda (x, e) -> string "\\" ^^ string x ^^ dot ^^ space ^^ aux e
    | Variable v -> string v
    | Int i -> string_of_int i |> string
    | Bool b -> string_of_bool b |> string
    | List es -> flow_map (comma ^^ space) aux es |> brackets
    | Case (e, p, b) ->
        flow space
          [ string "case"; aux e; string "of"; pretty_pt p; string "->"; aux b ]
  in
  aux

let render_to_string document =
  let buffer = Buffer.create 0 in
  PPrint.ToBuffer.pretty 1.0 80 buffer document;
  buffer |> Buffer.contents

let render_ty t = t |> pretty_ty |> render_to_string
let render_ty_predicate p = p |> pretty_ty_predicate |> render_to_string
let render_ty_unification n u = pretty_ty_unification n u |> render_to_string
let render_ty_constraint c = c |> pretty_ty_constraint |> render_to_string
let render_tm e = e |> pretty_tm |> render_to_string
