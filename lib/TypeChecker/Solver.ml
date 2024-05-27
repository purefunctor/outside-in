open Syntax

type solution_result =
  | Solved of ty_constraint list
  | Unsolved of ty_constraint
  | WithGiven of (string * ty_instance) list * ty_constraint list

let solve_predicate (env : Env.t) (predicate : ty_predicate) =
  match predicate with
  | Eq t -> begin
      match Entail.entail env "Eq" [ t ] with
      | None -> Unsolved (Predicate predicate)
      | Some subgoals -> Solved subgoals
    end
  | Unify (x_ty, y_ty) ->
      Unify.unify env x_ty y_ty;
      Solved []

let solve_implication (env : Env.t) (given : ty_constraint list)
    (local : ty_constraint list) =
  let to_instance (c : ty_constraint) =
    match c with
    | Predicate p -> begin
        match p with
        | Eq t -> Some ("Eq", Instance ([], [ t ]))
        | Unify (x_ty, y_ty) ->
            Unify.unify env x_ty y_ty;
            None
      end
    | _ ->
        failwith "invariant violated: given must only consist of Q-constraints."
  in
  let given = List.filter_map to_instance given in
  WithGiven (given, local)

let solve (env : Env.t) (wanted : ty_constraint list) : ty_constraint list =
  let trace_head head =
    Logging.info (fun log -> log "solve: %s" (Pretty.render_ty_constraint head))
  in
  let rec aux (residual : ty_constraint list) (wanted : ty_constraint list) =
    match wanted with
    | [] -> residual
    | head :: rest -> begin
        trace_head head;
        let result =
          match head with
          | Predicate predicate -> solve_predicate env predicate
          | Implication (given, local) -> solve_implication env given local
        in
        match result with
        | Solved subgoals -> aux residual (rest @ subgoals)
        | Unsolved unsolved -> aux (unsolved :: residual) rest
        | WithGiven (given, local) ->
            let aux () = aux residual (rest @ local) in
            Env.with_instances given aux env
      end
  in
  aux [] wanted
