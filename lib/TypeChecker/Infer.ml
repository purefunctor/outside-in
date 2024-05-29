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

(** [check_pt env p t] checks the pattern [p] against the type [t].

    Returns:
    - values to be introduced to the environment.
    - constraints discharged from matching GADTs. *)
let rec check_pt (env : Env.t) (p : pt) (t : ty) =
  match p with
  | PtConstructor (c, a) ->
      (* Get the constructor, instantiate its type, and check the argument
         and result types. For example, given the following constructor:

         Just :: forall a. a -> Maybe a

         c_t_a = ?a
         c_t_r = Maybe ?a

         For GADTs, we want existential variables (i.e. type variables only
         appearing in the argument position) to remain rigid. We achieve this
         by storing them separately from the constructor's type.

         Showable :: exists a. Eq a => a -> Showable

         c_c = [ Eq ^a ]
         c_t_a = ^a
         c_t_r = Showable
      *)
      let (Constructor (_, c_t)) = env |> Env.get_constructor c |> Option.get in
      let c_t, c_c = instantiate c_t in
      let c_t_a, c_t_r = Type.split_function c_t in
      let m, a_c = List.combine a c_t_a |> check_pt_list env in
      Unify.unify env t c_t_r;
      (m, c_c @ a_c)
  | PtVariable v -> (StringMap.singleton v t, [])
  | PtInt _ ->
      Unify.unify env t Int;
      (StringMap.empty, [])
  | PtBool _ ->
      Unify.unify env t Bool;
      (StringMap.empty, [])
  | PtList l ->
      let u = Utils.fresh_unification None in
      let r =
        let with_u l = (l, u) in
        l |> List.map with_u |> check_pt_list env
      in
      Unify.unify env t (List u);
      r

(** [check_pt_list env p_t] is [check_pt] against a list of arguments. *)
and check_pt_list (env : Env.t) (p_t : (pt * ty) list) =
  let aux (m, c) (p, t) =
    let m', c' = check_pt env p t in
    (StringMap.union_left m' m, c' @ c)
  in
  List.fold_left aux (StringMap.empty, []) p_t

and infer (env : Env.t) (e : tm) =
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
      let m, p_c = check_pt env p e_t in
      let b_t, b_c = env |> Env.with_values m (fun () -> infer env b) in
      let b_c = Implication (p_c, b_c) in
      (b_t, b_c :: e_c)
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
