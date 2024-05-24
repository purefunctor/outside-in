open Prelude
open Syntax

let fresh_unification : string option -> ty =
  let counter = ref 0 in
  fun name ->
    let count = !counter in
    counter := count + 1;
    Unification (name, Unsolved count |> ref)

let replace_type_variables variables =
  let traversal =
    object
      inherit [unit] Traversal.traversal

      method! ty state t =
        match t with
        | Skolem s -> begin
            match StringMap.find_opt s variables with
            | Some t -> (t, state)
            | None -> (t, state)
          end
        | _ -> (t, state)
    end
  in
  let traverse_ty t = t |> traversal#traverse_ty () |> fst in
  let traverse_ty_predicate p =
    p |> traversal#traverse_ty_predicate () |> fst
  in
  (traverse_ty, traverse_ty_predicate)
