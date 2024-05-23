open Syntax
module StringMap = Map.Make (String)

module Environment = struct
  type t = {
    mutable instances : ty_instance list StringMap.t;
    mutable values : ty StringMap.t;
  }

  let create () = { instances = StringMap.empty; values = StringMap.empty }
  let add_value k v e = e.values <- StringMap.add k v e.values
  let get_value k e = StringMap.find_opt k e.values

  let with_value k v f e =
    let previous_values = e.values in
    e.values <- StringMap.add k v e.values;
    let r = f () in
    e.values <- previous_values;
    r

  let add_instance k v e = e.instances <- StringMap.add_to_list k v e.instances

  let get_instances k e =
    StringMap.find_opt k e.instances |> Option.value ~default:[]

  let with_instance k v f e =
    let previous_instances = e.instances in
    e.instances <- StringMap.add_to_list k v e.instances;
    let r = f () in
    e.instances <- previous_instances;
    r
end

let fresh_unification : string option -> ty =
  let counter = ref 0 in
  fun name ->
    let count = !counter in
    counter := count + 1;
    Unification (name, Unsolved count |> ref)

(* FIXME: Maybe account for potential shadowing when we introduce rank-n types?
   An interesting solution would be to include the skolem level as part of the
   key, to further restrict usage. *)
let replace_type_variables_traversal variables =
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

let instantiate (t : ty) =
  Logging.info (fun log -> log "instantiate: %s" (Pretty.render_ty t));
  match t with
  | Forall (variables, predicates, t) ->
      let traversal =
        let from_variable v = (v, fresh_unification (Some v)) in
        variables |> List.map from_variable |> StringMap.of_list
        |> replace_type_variables_traversal
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
  | List es -> begin
      match es with
      | [] -> (fresh_unification None, [])
      | head :: rest ->
          let head_t, head_c = infer environment head in
          let rest_t, rest_c =
            List.map (infer environment) rest |> List.split
          in
          List.iter (unify environment head_t) rest_t;
          (List head_t, head_c :: rest_c |> List.flatten)
    end
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

let rec match_type (x_ty : ty) (y_ty : ty) : ty StringMap.t =
  Logging.info (fun log ->
      log "match: %s = %s" (Pretty.render_ty x_ty) (Pretty.render_ty y_ty));
  let x_ty = Type.normalize x_ty in
  let y_ty = Type.normalize y_ty in
  match (x_ty, y_ty) with
  | Int, Int
  | Bool, Bool ->
      StringMap.empty
  | List x_l, List y_l -> match_type x_l y_l
  | Application (x_f, x_a), Application (y_f, y_a) ->
      let s0 = match_type x_f y_f in
      let s1 = match_type x_a y_a in
      StringMap.merge (fun _ l _ -> l) s0 s1
  | Function (x_a, x_r), Function (y_a, y_r) ->
      let s0 = match_type x_a y_a in
      let s1 = match_type x_r y_r in
      StringMap.merge (fun _ l _ -> l) s0 s1
  | Skolem x_s, Skolem y_s ->
      if String.equal x_s y_s then StringMap.of_list [ (x_s, y_ty) ]
      else failwith (__LOC__ ^ ": cannot match types")
  | Unification (_, x_u), Unification (_, y_u) ->
      if Unification.equal !x_u !y_u then StringMap.empty
      else failwith (__LOC__ ^ ": cannot match types")
  | Skolem s, t
  | t, Skolem s ->
      StringMap.of_list [ (s, t) ]
  | _, _ -> failwith (__LOC__ ^ ": cannot match types")

let match_arguments (predicate_arguments : ty list)
    (instance_arguments : ty list) =
  let substitutions =
    List.map2 match_type predicate_arguments instance_arguments
  in
  let merge_left = StringMap.union (fun _ l _ -> Some l) in
  let substitutions = List.fold_left merge_left StringMap.empty substitutions in
  replace_type_variables_traversal substitutions

let solve (environment : Environment.t) (wanted : ty_constraint list) :
    ty_constraint list =
  let find_instance (class_name : string) (predicate_arguments : ty list) =
    let predicate_arguments = List.map Type.normalize predicate_arguments in
    let instances = environment |> Environment.get_instances class_name in
    instances
    |> List.find_map (fun (Instance (subgoals, instance_arguments)) ->
           try
             let traversal =
               match_arguments predicate_arguments instance_arguments
             in
             Some
               (subgoals
               |> List.map (fun subgoal ->
                      let t, _ = traversal#traverse_ty_predicate () subgoal in
                      Predicate.to_constraint t))
           with
           | _ -> None)
  in
  let rec aux residual wanted =
    match wanted with
    | [] -> residual
    | Predicate head :: rest -> begin
        match head with
        | Eq t -> begin
            Logging.info (fun log ->
                log "finding eq instance: Eq %s" (Pretty.render_ty t));
            match find_instance "Eq" [ t ] with
            | None -> aux (Predicate head :: residual) rest
            | Some subgoals -> aux residual (rest @ subgoals)
          end
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

  environment |> Environment.add_instance "Eq" (Instance ([], [ Int ]));
  environment |> Environment.add_instance "Eq" (Instance ([], [ Bool ]));

  print_endline "Case 1";
  let t, c =
    infer environment (Apply (Apply (Variable "eq", Int 10), Int 10))
  in
  let c = solve environment c in
  print_endline @@ Pretty.render_ty t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  print_endline "Case 2";
  let t, c0 = infer environment (Variable "eq") in
  let t, c1 = instantiate t in
  unify environment t (Function (Skolem "a", Function (Skolem "a", Bool)));
  let c =
    environment
    |> Environment.with_instance "Eq"
         (Instance ([], [ Skolem "a" ]))
         (fun () -> solve environment (c0 @ c1))
  in
  print_endline @@ Pretty.render_ty t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  environment
  |> Environment.add_instance "Eq"
       (Instance ([ Eq (Skolem "a") ], [ List (Skolem "a") ]));

  print_endline "Case 3";
  let t, c =
    infer environment (Apply (Variable "eq", List [ Int 21; Int 42 ]))
  in
  let c = solve environment c in
  print_endline @@ Pretty.render_ty @@ Type.normalize t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p)
