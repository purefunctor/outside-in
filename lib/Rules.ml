open Syntax
module StringMap = Map.Make (String)

module State = struct
  type t = {
    mutable index : int;
    mutable mono : mono_t StringMap.t;
    mutable poly : scheme_t StringMap.t;
  }

  let create () = { index = 0; mono = StringMap.empty; poly = StringMap.empty }

  let fresh_unification state =
    let index = state.index in
    state.index <- state.index + 1;
    `Unification (ref (`Unsolved index))

  let add_mono state k v = state.mono <- StringMap.add k v state.mono
  let get_mono state k = StringMap.find_opt k state.mono

  let with_mono state k v f =
    state.mono <- StringMap.add k v state.mono;
    let r = f () in
    state.mono <- StringMap.remove k state.mono;
    r

  let add_poly state k v = state.poly <- StringMap.add k v state.poly
  let get_poly state k = StringMap.find_opt k state.poly
end

let replace_type (substitution : mono_t StringMap.t) =
  let rec aux (t : mono_t) =
    match t with
    | `Bool -> t
    | `Int -> t
    | `Application (f, x) ->
        let f = aux f in
        let x = aux x in
        `Application (f, x)
    | `Function (a, r) ->
        let a = aux a in
        let r = aux r in
        `Function (a, r)
    | `Unification _ -> t
    | `Variable v ->
        StringMap.find_opt v substitution |> Option.value ~default:t
  in
  aux

let replace_predicate (substitution : mono_t StringMap.t)
    (predicate : predicate) =
  match predicate with
  | `Unify (x_t, y_t) ->
      let x_t = replace_type substitution x_t in
      let y_t = replace_type substitution y_t in
      `Unify (x_t, y_t)
  | `Eq t ->
      let t = replace_type substitution t in
      `Eq t

let replace_predicates (substitution : mono_t StringMap.t) :
    predicate list -> predicate list =
  List.map (replace_predicate substitution)

let instantiate (state : State.t) (t : scheme_t) : mono_t * q_constraint list =
  match t with
  | `Forall (variables, predicates, t) ->
      let substitution =
        let fresh_unification variable =
          (variable, state |> State.fresh_unification)
        in
        variables |> List.map fresh_unification |> StringMap.of_list
      in
      (replace_type substitution t, replace_predicates substitution predicates)

let rec solve (state : State.t) (u : unification_variable ref) (t : mono_t) =
  match !u with `Unsolved _ -> u := `Solved t | `Solved t' -> unify state t' t

and unify (state : State.t) (x_t : mono_t) (y_t : mono_t) =
  match (x_t, y_t) with
  | `Bool, `Bool -> ()
  | `Int, `Int -> ()
  | `Application (x_f, x_a), `Application (y_f, y_a) ->
      unify state x_f y_f;
      unify state x_a y_a
  | `Function (x_a, x_r), `Function (y_a, y_r) ->
      unify state x_a y_a;
      unify state x_r y_r
  | `Unification x_u, `Unification y_u ->
      if x_u = y_u then () else solve state x_u y_t
  | `Variable x, `Variable y ->
      if String.equal x y then () else failwith "cannot unify skolems"
  | `Unification u, t | t, `Unification u -> solve state u t
  | _, _ -> failwith "cannot unify types"

let rec infer (state : State.t) (e : expr) : mono_t * q_constraint list =
  match e with
  | `Bool _ -> (`Bool, [])
  | `Int _ -> (`Int, [])
  | `Variable v -> (
      match State.get_mono state v with
      | Some t -> (t, [])
      | None -> (
          match State.get_poly state v with
          | Some t -> instantiate state t
          | None -> failwith "variable is unbound"))
  | `Application (f, x) ->
      let f_t, f_c = infer state f in
      let x_t, x_c = infer state x in
      let r_t = State.fresh_unification state in
      unify state f_t (`Function (x_t, r_t));
      (r_t, f_c @ x_c)
  | `Lambda (v, e) ->
      let v_t = State.fresh_unification state in
      let e_t, e_c = State.with_mono state v v_t @@ fun () -> infer state e in
      (`Function (v_t, e_t), e_c)

let deref =
  let rec aux (t : mono_t) =
    match t with `Unification { contents = `Solved t } -> aux t | _ -> t
  in
  aux

let solve_eq (given : q_constraint list) (t : mono_t) =
  let rec matches (x_t : mono_t) (y_t : mono_t) =
    match (x_t, y_t) with
    | `Bool, `Bool -> true
    | `Int, `Int -> true
    | `Application (x_f, x_a), `Application (y_f, y_a) ->
        matches x_f y_f && matches x_a y_a
    | `Function (x_a, x_r), `Function (y_a, y_r) ->
        matches x_a y_a && matches x_r y_r
    | `Unification x_u, `Unification y_u -> x_u = y_u
    | `Variable x, `Variable y -> String.equal x y
    | _ -> false
  in
  let search_given = function `Eq t' -> matches t t' | _ -> false in
  given |> List.exists search_given

let solve (state : State.t) (given : q_constraint list)
    (wanted : q_constraint list) : q_constraint list =
  let rec aux (residual : q_constraint list) (constraints : q_constraint list) =
    match constraints with
    | head :: rest -> (
        match head with
        | `Unify (x_t, y_t) ->
            unify state x_t y_t;
            aux residual rest
        | `Eq t ->
            if solve_eq given (deref t) then aux residual rest
            else aux (head :: residual) rest)
    | [] -> residual
  in
  aux [] wanted

let check_binding (state : State.t) (e : expr) (t : scheme_t) =
  let e_t, e_c = infer state e in
  let r_c =
    match t with
    | `Forall (_, predicates, t) ->
        unify state e_t t;
        solve state predicates e_c
  in
  match r_c with [] -> [] | _ -> failwith "unsolved constraints"

let program () =
  let state = State.create () in

  let eq_t : scheme_t =
    `Forall
      ( [ "a" ],
        [ `Eq (`Variable "a") ],
        `Function (`Variable "a", `Function (`Variable "a", `Bool)) )
  in
  State.add_poly state "eq" eq_t;

  check_binding state (`Variable "eq") eq_t
