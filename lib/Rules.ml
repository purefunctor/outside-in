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

let rec solve (environment : Environment.t) (u : ty_unification ref) (t : ty) =
  if occurs_check u t then failwith (__LOC__ ^ ": failed occurs check.")
  else
    match !u with
    | Unsolved i -> u := Solved (i, t)
    | Solved (_, t') -> unify environment t t'

and unify (environment : Environment.t) (x_ty : ty) (y_ty : ty) =
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
      if Unification.equal !x_u !y_u then () else solve environment x_u y_ty
  | Unification (_, u), t
  | t, Unification (_, u) ->
      solve environment u t
  | _, _ -> failwith (__LOC__ ^ ": cannot unify these types.")

let rec infer (environment : Environment.t) (e : tm) =
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

let program () =
  let environment = Environment.create () in
  let eq_t =
    Forall
      ( [ "a" ],
        [ Eq (Skolem "a") ],
        Function ((Skolem "a" : ty), Function (Skolem "a", Bool)) )
  in
  environment |> Environment.add_value "eq" eq_t;
  let t, c =
    infer environment (Apply (Apply (Variable "eq", Int 10), Int 10))
  in
  (Type.normalize t, c)
