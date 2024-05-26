type ty =
  | Application of (ty * ty)
  | Forall of (string list * ty_predicate list * ty)
  | Function of (ty * ty)
  | Skolem of string
  | Unification of (string option * ty_unification ref)
  | Int
  | Bool
  | List of ty

and ty_predicate = Eq of ty | Unify of ty * ty
and ty_unification = Unsolved of int | Solved of (int * ty)

type ty_constraint = Predicate of ty_predicate
type ty_instance = Instance of ty_predicate list * ty list

type tm =
  | Apply of tm * tm
  | Lambda of string * tm
  | Variable of string
  | Int of int
  | Bool of bool
  | List of tm list

module Type = struct
  type t = ty

  let normalize : t -> t =
    let rec aux = function
      | Unification (_, { contents = Solved (_, t) }) -> aux t
      | t -> t
    in
    aux
end

module Predicate = struct
  type t = ty_predicate

  let to_constraint predicate = Predicate predicate

  let normalize : t -> t = function
    | Eq t -> Eq (Type.normalize t)
    | Unify (x_ty, y_ty) -> Unify (Type.normalize x_ty, Type.normalize y_ty)
end

module Unification = struct
  type t = ty_unification

  let get_identifier = function
    | Unsolved i -> i
    | Solved (i, _) -> i

  let equal x y = Int.equal (get_identifier x) (get_identifier y)
end

module Traversal = struct
  let ignore state value = (value, state)

  let traverse_list :
        'state 'value.
        ('state -> 'value -> 'value * 'state) ->
        'state ->
        'value list ->
        'value list * 'state =
   fun traversal state values ->
    List.fold_right
      begin
        fun value (values, state) ->
          let value, state = traversal state value in
          (value :: values, state)
      end
      values ([], state)

  class ['state] traversal =
    object (self)
      method ty : 'state -> ty -> ty * 'state = ignore

      method ty_predicate : 'state -> ty_predicate -> ty_predicate * 'state =
        ignore

      method traverse_ty : 'state -> ty -> ty * 'state =
        fun state ty ->
          let ty, state =
            match ty with
            | Application (f, a) ->
                let f, state = self#traverse_ty state f in
                let a, state = self#traverse_ty state a in
                (Application (f, a), state)
            | Forall (v, p, m) ->
                let p, state =
                  traverse_list self#traverse_ty_predicate state p
                in
                let m, state = self#traverse_ty state m in
                (Forall (v, p, m), state)
            | Function (a, r) ->
                let a, state = self#traverse_ty state a in
                let r, state = self#traverse_ty state r in
                (Function (a, r), state)
            | Skolem _ -> (ty, state)
            | Unification (n, u) -> begin
                match !u with
                | Unsolved _ -> (ty, state)
                | Solved (i, s) ->
                    let s, state = self#traverse_ty state s in
                    (Unification (n, Solved (i, s) |> ref), state)
              end
            | Int
            | Bool ->
                (ty, state)
            | List t ->
                let t, state = self#traverse_ty state t in
                (List t, state)
          in
          self#ty state ty

      method traverse_ty_predicate
          : 'state -> ty_predicate -> ty_predicate * 'state =
        fun state predicate ->
          let predicate, state =
            match predicate with
            | Eq t ->
                let t, state = self#traverse_ty state t in
                (Eq t, state)
            | Unify (x_ty, y_ty) ->
                let x_ty, state = self#traverse_ty state x_ty in
                let y_ty, state = self#traverse_ty state y_ty in
                (Unify (x_ty, y_ty), state)
          in
          self#ty_predicate state predicate
    end
end
