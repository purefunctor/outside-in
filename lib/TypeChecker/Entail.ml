open Prelude
open Syntax

let trace_match_type p_ty i_ty =
  Logging.info (fun log ->
      log "match_type: %s = %s" (Pretty.render_ty p_ty) (Pretty.render_ty i_ty))

let trace_entail class_name predicate_arguments =
  Logging.info (fun log ->
      let predicate_arguments =
        String.concat " " @@ List.map Pretty.render_ty predicate_arguments
      in
      log "find_instance: %s %s" class_name predicate_arguments)

let rec match_type (p_ty : ty) (i_ty : ty) : ty list StringMap.t =
  trace_match_type p_ty i_ty;
  let p_ty = Type.normalize p_ty in
  let i_ty = Type.normalize i_ty in
  match (p_ty, i_ty) with
  | Int, Int
  | Bool, Bool ->
      StringMap.empty
  | List p_l, List i_l -> match_type p_l i_l
  | Application (p_f, p_a), Application (i_f, i_a) ->
      StringMap.union_append (match_type p_f i_f) (match_type p_a i_a)
  | Function (p_a, p_r), Function (i_a, i_r) ->
      StringMap.union_append (match_type p_a i_a) (match_type p_r i_r)
  | Skolem p_s, Skolem i_s ->
      if String.equal p_s i_s then StringMap.of_list [ (p_s, [ i_ty ]) ]
      else failwith (__LOC__ ^ ": cannot match types")
  | Unification (_, p_u), Unification (_, i_u) ->
      if Unification.equal !p_u !i_u then StringMap.empty
      else failwith (__LOC__ ^ ": cannot match types")
  | Skolem s, t
  | t, Skolem s ->
      StringMap.of_list [ (s, [ t ]) ]
  | _, _ -> failwith (__LOC__ ^ ": cannot match types")

let match_heads (env : Env.t) (predicate_arguments : ty list)
    (instance_arguments : ty list) =
  let verify_substitution k v =
    match v with
    | [] -> failwith "invariant violated: empty substitutions."
    | _ ->
        let u = Utils.fresh_unification (Some k) in
        List.iter (Unify.unify env u) v;
        u
  in
  List.map2 match_type predicate_arguments instance_arguments
  |> List.fold_left StringMap.union_append StringMap.empty
  |> StringMap.mapi verify_substitution

let try_instance (env : Env.t) (predicate_arguments : ty list)
    (instance : ty_instance) =
  let (Instance (subgoals, instance_arguments)) = instance in
  try
    let _, traverse_ty_predicate =
      match_heads env predicate_arguments instance_arguments
      |> Utils.replace_type_variables
    in
    let subgoal_to_constraint subgoal =
      subgoal |> traverse_ty_predicate |> Predicate.to_constraint
    in
    Some (List.map subgoal_to_constraint subgoals)
  with
  | _ -> None

let entail (env : Env.t) (class_name : string) (predicate_arguments : ty list) =
  trace_entail class_name predicate_arguments;
  let predicate_arguments = List.map Type.normalize predicate_arguments in
  let class_instances = env |> Env.get_instances class_name in
  List.find_map (try_instance env predicate_arguments) class_instances
