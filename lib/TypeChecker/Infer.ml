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
  | Lambda (v, e) ->
      let v_t = Utils.fresh_unification (Some v) in
      let e_t, c0 = env |> Env.with_value v v_t @@ fun () -> infer env e in
      (Function (v_t, e_t), c0)
  | Constructor c -> begin
      match env |> Env.get_constructor c with
      | None -> failwith (__LOC__ ^ ": unbound constructor")
      | Some t -> begin
          match t with
          | Regular t -> (t, [])
          | Generalized (_, t) -> (t, [])
        end
    end
  | Variable v -> begin
      match env |> Env.get_value v with
      | None -> failwith (__LOC__ ^ ": unbound variable")
      | Some t -> (t, [])
    end
