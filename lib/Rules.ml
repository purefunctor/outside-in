open Syntax

module State = struct
  module StringMap = Map.Make (String)

  type t = { mutable index : int; mutable environment : mono_t StringMap.t }

  let create () = { index = 0; environment = StringMap.empty }

  let fresh_unification state =
    let index = state.index in
    state.index <- state.index + 1;
    `Unification (ref (`Unsolved index))

  let add_mono state k v =
    state.environment <- StringMap.add k v state.environment

  let get_mono state k = StringMap.find_opt k state.environment

  let with_mono state k v f =
    state.environment <- StringMap.add k v state.environment;
    let r = f () in
    state.environment <- StringMap.remove k state.environment;
    r
end

let rec solve (state : State.t) (u : unification_variable ref) (t : mono_t) =
  match !u with `Unsolved _ -> u := `Solved t | `Solved t' -> unify state t' t

and unify (state : State.t) (x_t : mono_t) (y_t : mono_t) =
  match (x_t, y_t) with
  | `Bool, `Bool -> ()
  | `Int, `Int -> ()
  | `Application (x_f, x_a), `Application (y_f, y_a) ->
      unify state x_f y_f;
      unify state x_a y_a
  | `Function (x_a, x_r), `Function (y_a, y_r) ->
      unify state x_a y_a;
      unify state x_r y_r
  | `Unification x_u, `Unification _ -> solve state x_u y_t
  | `Variable x, `Variable y ->
      if x == y then () else failwith "cannot unify skolems"
  | `Unification u, t | t, `Unification u -> solve state u t
  | _, _ -> failwith "cannot unify types"

let rec infer (state : State.t) (e : expr) : mono_t =
  match e with
  | `Bool _ -> `Bool
  | `Int _ -> `Int
  | `Variable v -> (
      match State.get_mono state v with
      | Some t -> t
      | None -> failwith "could not find variable")
  | `Application (f, x) ->
      let f_t = infer state f in
      let x_t = infer state x in
      let r_t = State.fresh_unification state in
      unify state f_t (`Function (x_t, r_t));
      r_t
  | `Lambda (v, e) ->
      let v_t = State.fresh_unification state in
      let e_t = State.with_mono state v v_t @@ fun () -> infer state e in
      `Function (v_t, e_t)

let program () =
  let state = State.create () in
  let id = `Lambda ("a", `Variable "a") in
  let x = `Application (id, id) in
  infer state x
