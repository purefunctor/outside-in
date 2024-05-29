open Prelude
open Syntax

let trace_instantiate t =
  Logging.info (fun log -> log "instantiate: %s" (Pretty.render_ty t))

let trace_infer e =
  Logging.info (fun log -> log "infer: %s" (Pretty.render_tm e))

let instantiate (t : ty) =
  trace_instantiate t;
  match t with
  | Forall (variables, predicates, t) ->
      let traverse_ty, traverse_ty_predicate =
        let from_variable v = (v, Utils.fresh_unification (Some v)) in
        variables |> List.map from_variable |> StringMap.of_list
        |> Utils.replace_type_variables
      in

      let constraints =
        List.map
          (fun predicate ->
            predicate |> traverse_ty_predicate |> Predicate.to_constraint)
          predicates
      in
      let t = traverse_ty t in

      (t, constraints)
  | _ -> (t, [])

let split_ty_function =
  let rec aux arguments (t : ty) =
    match t with
    | Function (a, r) -> aux (a :: arguments) r
    | _ -> (List.rev arguments, t)
  in
  aux []

let rec infer (env : Env.t) (e : tm) =
  trace_infer e;
  match e with
  | Int _ -> ((Int : ty), [])
  | Bool _ -> ((Bool : ty), [])
  | List es -> begin
      match es with
      | [] -> (Utils.fresh_unification None, [])
      | head :: rest ->
          let head_t, head_c = infer env head in
          let rest_t, rest_c = List.map (infer env) rest |> List.split in
          List.iter (Unify.unify env head_t) rest_t;
          (List head_t, head_c :: rest_c |> List.flatten)
    end
  | Apply (f, a) ->
      let f_t, c0 = infer env f in
      let f_t, c1 = instantiate f_t in

      let a_t, c2 = infer env a in
      let a_t, c3 = instantiate a_t in

      let r_t = Utils.fresh_unification None in
      Unify.unify env f_t (Function (a_t, r_t));

      (r_t, List.concat [ c0; c1; c2; c3 ])
  | Case (e, p, b) ->
      let e_t, e_c = infer env e in
      let b_t = Utils.fresh_unification None in
      let b_c =
        match p with
        | PtConstructor (c, a) ->
            let (Constructor (_, c_t)) =
              env |> Env.get_constructor c |> Option.get
            in
            let c_t, c_c = instantiate c_t in
            let c_t_a, c_t_r = split_ty_function c_t in
            let i_b_t, i_b_c =
              let a =
                a
                |> List.filter_map (fun p ->
                       match p with
                       | PtVariable v -> Some v
                       | _ -> failwith "TODO: non-variables not supported yet.")
              in
              let in_scope = List.combine a c_t_a in
              env |> Env.with_values in_scope (fun () -> infer env b)
            in
            let c = Implication (c_c, i_b_c) in
            Unify.unify env e_t c_t_r;
            Unify.unify env b_t i_b_t;
            [ c ]
        | _ -> failwith "TODO: not supported yet."
      in
      (b_t, e_c @ b_c)
  | Lambda (v, e) ->
      let v_t = Utils.fresh_unification (Some v) in
      let e_t, c0 = env |> Env.with_value v v_t @@ fun () -> infer env e in
      (Function (v_t, e_t), c0)
  | Constructor c -> begin
      match env |> Env.get_constructor c with
      | None -> failwith (__LOC__ ^ ": unbound constructor")
      | Some (Constructor (e, t)) -> begin
          match t with
          | Forall (v, p, t) -> (Forall (v @ e, p, t), [])
          | t -> (Forall (e, [], t), [])
        end
    end
  | Variable v -> begin
      match env |> Env.get_value v with
      | None -> failwith (__LOC__ ^ ": unbound variable")
      | Some t -> (t, [])
    end
