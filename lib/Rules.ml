open Syntax
module StringMap = Map.Make (String)

module Environment = struct
  type t = { mutable values : ty StringMap.t }

  let create () = { values = StringMap.empty }
  let add_value k v e = e.values <- StringMap.add k v e.values
  let get_value k e = StringMap.find_opt k e.values

  let with_value k v f e =
    e.values <- StringMap.add k v e.values;
    let r = f () in
    e.values <- StringMap.remove k e.values;
    r
end

let fresh_unification : string option -> ty =
  let counter = ref 0 in
  fun name ->
    let count = !counter in
    counter := count + 1;
    Unification (name, Unsolved count |> ref)

let instantiate (t : ty) =
  (* FIXME: Maybe account for potential shadowing when we introduce rank-n types?
     An interesting solution would be to include the skolem level as part of the
     key, to further restrict usage. *)
  Logging.info (fun log -> log "instantiate: %s" (Pretty.render_ty t));
  let make_traversal variables =
    object
      inherit [unit] Traversal.traversal

      method! ty state t =
        match t with
        | Skolem s -> begin
            match StringMap.find_opt s variables with
            | Some t -> (t, state)
            | None -> (t, state)
          end
        | _ -> (t, state)
    end
  in
  match t with
  | Forall (variables, predicates, t) ->
      let traversal =
        let from_variable v = (v, fresh_unification (Some v)) in
        variables |> List.map from_variable |> StringMap.of_list
        |> make_traversal
      in

      let predicates, _ =
        Traversal.traverse_list traversal#traverse_ty_predicate () predicates
      in
      let t, _ = traversal#traverse_ty () t in

      (t, predicates |> List.map Predicate.to_constraint)
  | _ -> (t, [])

let occurs_check (u : ty_unification ref) (t : ty) =
  let traversal =
    object
      inherit [bool] Traversal.traversal

      method! ty state ty =
        match ty with
        | Unification (_, u') -> (t, state || Unification.equal !u !u')
        | _ -> (ty, state)
    end
  in
  let _, result = traversal#traverse_ty false t in
  result

let rec solve_unification (environment : Environment.t) (u : ty_unification ref)
    (t : ty) =
  Logging.info (fun log ->
      log "solve: %s ~ %s"
        (Pretty.render_ty_unification None u)
        (Pretty.render_ty t));
  if occurs_check u t then failwith (__LOC__ ^ ": failed occurs check.")
  else
    match !u with
    | Unsolved i -> u := Solved (i, t)
    | Solved (_, t') -> unify environment t t'

and unify (environment : Environment.t) (x_ty : ty) (y_ty : ty) =
  Logging.info (fun log ->
      log "unify: %s ~ %s" (Pretty.render_ty x_ty) (Pretty.render_ty y_ty));
  let x_ty = Type.normalize x_ty in
  let y_ty = Type.normalize y_ty in
  match (x_ty, y_ty) with
  | Int, Int -> ()
  | Bool, Bool -> ()
  | Application (x_f, x_a), Application (y_f, y_a) ->
      unify environment x_f y_f;
      unify environment x_a y_a
  | Function (x_a, x_r), Function (y_a, y_r) ->
      unify environment x_a y_a;
      unify environment x_r y_r
  | Skolem x_s, Skolem y_s ->
      if String.equal x_s y_s then ()
      else failwith (__LOC__ ^ ": cannot unify skolem variables.")
  | Forall _, _
  | _, Forall _ ->
      failwith (__LOC__ ^ ": todo bidirectional type checking")
  | Unification (_, x_u), Unification (_, y_u) ->
      if Unification.equal !x_u !y_u then ()
      else solve_unification environment x_u y_ty
  | Unification (_, u), t
  | t, Unification (_, u) ->
      solve_unification environment u t
  | _, _ -> failwith (__LOC__ ^ ": cannot unify these types.")

let rec infer (environment : Environment.t) (e : tm) =
  Logging.info (fun log -> log "infer: %s" (Pretty.render_tm e));
  match e with
  | Int _ -> ((Int : ty), [])
  | Bool _ -> ((Bool : ty), [])
  | Apply (f, a) ->
      let f_t, c0 = infer environment f in
      let f_t, c1 = instantiate f_t in
      let a_t, c2 = infer environment a in

      let r_t = fresh_unification None in
      unify environment f_t (Function (a_t, r_t));

      (r_t, List.concat [ c0; c1; c2 ])
  | Lambda (v, e) ->
      let v_t = fresh_unification (Some v) in
      let e_t, c0 =
        environment
        |> Environment.with_value v v_t @@ fun () -> infer environment e
      in
      (Function (v_t, e_t), c0)
  | Variable v -> begin
      match environment |> Environment.get_value v with
      | None -> failwith (__LOC__ ^ ": unbound variable")
      | Some t -> (t, [])
    end

let rec match_type (x_ty : ty) (y_ty : ty) : bool =
  let x_ty = Type.normalize x_ty in
  let y_ty = Type.normalize y_ty in
  match (x_ty, y_ty) with
  | Int, Int
  | Bool, Bool ->
      true
  | Application (x_f, x_a), Application (y_f, y_a) ->
      match_type x_f y_f && match_type x_a y_a
  | Function (x_a, x_r), Function (y_a, y_r) ->
      match_type x_a y_a && match_type x_r y_r
  | Skolem x_s, Skolem y_s -> String.equal x_s y_s
  | Unification (_, x_u), Unification (_, y_u) -> Unification.equal !x_u !y_u
  | _, _ -> false

(*
   TODO:

   1. Figure out how to do subgoals in instances e.g. Eq a => Eq [a]
   2. Given constraints should be a part of the environment, that is,
      it can be represented not by a list of constraints but using a
      more convenient type that allows for more generic searching.
*)
let solve (environment : Environment.t) (given : ty_constraint list)
    (wanted : ty_constraint list) : ty_constraint list =
  let rec solve_eq (t : ty) =
    let t = Type.normalize t in
    match t with
    | Int
    | Bool ->
        true
    | _ ->
        let eq_instances =
          given
          |> List.filter_map (fun c ->
                 match c with
                 | Predicate (Eq t) -> Some t
                 | _ -> None)
        in
        List.exists (fun t' -> match_type t t') eq_instances
  and aux residual wanted =
    match wanted with
    | [] -> residual
    | Predicate head :: rest -> begin
        match head with
        | Eq t ->
            if solve_eq t then aux residual rest
            else aux (Predicate head :: residual) rest
        | Unify (x_ty, y_ty) ->
            unify environment x_ty y_ty;
            aux residual rest
      end
  in
  aux [] wanted

let program () =
  let environment = Environment.create () in
  let eq_t =
    Forall
      ( [ "a" ],
        [ Eq (Skolem "a") ],
        Function ((Skolem "a" : ty), Function (Skolem "a", Bool)) )
  in
  environment |> Environment.add_value "eq" eq_t;

  print_endline "Case 1";
  let t, c =
    infer environment (Apply (Apply (Variable "eq", Int 10), Int 10))
  in
  let c = solve environment [] c in
  print_endline @@ Pretty.render_ty t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  print_endline "Case 2";
  let t, c0 = infer environment (Variable "eq") in
  let t, c1 = instantiate t in
  unify environment t (Function (Skolem "a", Function (Skolem "a", Bool)));
  let c = solve environment [ Predicate (Eq (Skolem "a")) ] (c0 @ c1) in
  print_endline @@ Pretty.render_ty t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p)
