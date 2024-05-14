type unification_variable = [ `Unsolved of int | `Solved of mono_t ]

and mono_t =
  [ `Application of mono_t * mono_t
  | `Function of mono_t * mono_t
  | `Unification of unification_variable ref
  | `Variable of string
  | `Int
  | `Bool ]

type expr =
  [ `Int of int
  | `Bool of bool
  | `Variable of string
  | `Lambda of string * expr
  | `Application of expr * expr ]

type predicate = [ `Unify of mono_t * mono_t ]
type scheme_t = [ `Forall of string list * predicate list * mono_t ]
type q_constraint = [ | predicate ]
