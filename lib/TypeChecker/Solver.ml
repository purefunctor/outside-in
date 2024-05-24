open Syntax

type solution_result =
  | Solved of ty_constraint list
  | Unsolved of ty_constraint

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

let solve (env : Env.t) (wanted : ty_constraint list) : ty_constraint list =
  let rec aux (residual : ty_constraint list) (wanted : ty_constraint list) =
    match wanted with
    | [] -> residual
    | head :: rest -> begin
        let result =
          match head with
          | Predicate predicate -> solve_predicate env predicate
        in
        match result with
        | Solved subgoals -> aux residual (rest @ subgoals)
        | Unsolved unsolved -> aux (unsolved :: residual) rest
      end
  in
  aux [] wanted
