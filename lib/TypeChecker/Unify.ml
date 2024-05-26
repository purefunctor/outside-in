open Syntax

let trace_solve u t =
  Logging.info (fun log ->
      log "solve: %s ~ %s"
        (Pretty.render_ty_unification None u)
        (Pretty.render_ty t))

let trace_unify x_ty y_ty =
  Logging.info (fun log ->
      log "unify: %s ~ %s" (Pretty.render_ty x_ty) (Pretty.render_ty y_ty))

let occurs_check (u : ty_unification ref) (t : ty) =
  let traversal =
    object
      inherit [bool] Traversal.traversal

      method! ty state ty =
        match ty with
        | Unification (_, u') -> (ty, state || Unification.equal !u !u')
        | _ -> (ty, state)
    end
  in
  t |> traversal#traverse_ty false |> snd

let rec solve (env : Env.t) (u : ty_unification ref) (t : ty) =
  trace_solve u t;
  if occurs_check u t then failwith (__LOC__ ^ ": infinitely recursive type")
  else
    match !u with
    | Unsolved i -> u := Solved (i, t)
    | Solved (_, t') -> unify env t t'

and unify (env : Env.t) (x_ty : ty) (y_ty : ty) =
  trace_unify x_ty y_ty;
  let x_ty = Type.normalize x_ty in
  let y_ty = Type.normalize y_ty in
  match (x_ty, y_ty) with
  | Int, Int -> ()
  | Bool, Bool -> ()
  | List x_l, List y_l -> unify env x_l y_l
  | Constructor x_c, Constructor y_c ->
      if String.equal x_c y_c then ()
      else failwith (__LOC__ ^ ": cannot unify constructors.")
  | Application (x_f, x_a), Application (y_f, y_a) ->
      unify env x_f y_f;
      unify env x_a y_a
  | Function (x_a, x_r), Function (y_a, y_r) ->
      unify env x_a y_a;
      unify env x_r y_r
  | Skolem x_s, Skolem y_s ->
      if String.equal x_s y_s then ()
      else failwith (__LOC__ ^ ": cannot unify skolem variables.")
  | Forall _, _
  | _, Forall _ ->
      failwith (__LOC__ ^ ": todo bidirectional type checking")
  | Unification (_, x_u), Unification (_, y_u) ->
      if Unification.equal !x_u !y_u then () else solve env x_u y_ty
  | Unification (_, u), t
  | t, Unification (_, u) ->
      solve env u t
  | _, _ -> failwith (__LOC__ ^ ": cannot unify these types.")
