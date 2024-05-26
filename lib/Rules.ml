open Syntax
open TypeChecker

let program () =
  let environment = Env.create () in
  let eq_t =
    Forall
      ( [ "a" ],
        [ Eq (Skolem "a") ],
        Function ((Skolem "a" : ty), Function (Skolem "a", Bool)) )
  in

  environment |> Env.add_value "eq" eq_t;
  environment |> Env.add_instance "Eq" (Instance ([], [ Int ]));
  environment |> Env.add_instance "Eq" (Instance ([], [ Bool ]));
  environment
  |> Env.add_instance "Eq"
       (Instance ([ Eq (Skolem "a") ], [ List (Skolem "a") ]));

  print_endline "Case 1";
  let t, c =
    Infer.infer environment (Apply (Apply (Variable "eq", Int 10), Int 10))
  in
  let c = Solver.solve environment c in
  print_endline @@ Pretty.render_ty t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  print_endline "Case 2";
  let t, c0 = Infer.infer environment (Variable "eq") in
  let t, c1 = Infer.instantiate t in
  Unify.unify environment t (Function (Skolem "a", Function (Skolem "a", Bool)));
  let c =
    environment
    |> Env.with_instance "Eq"
         (Instance ([], [ Skolem "a" ]))
         (fun () -> Solver.solve environment (c0 @ c1))
  in
  print_endline @@ Pretty.render_ty t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  print_endline "Case 3";
  let t, c =
    Infer.infer environment (Apply (Variable "eq", List [ Int 21; Int 42 ]))
  in
  let c = Solver.solve environment c in
  print_endline @@ Pretty.render_ty @@ Type.normalize t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  environment
  |> Env.add_constructor "Nil"
       (Regular (Forall ([ "a" ], [], List (Skolem "a"))));
  environment
  |> Env.add_constructor "Cons"
       (Regular
          (Forall
             ( [ "a" ],
               [],
               Function
                 (Skolem "a", Function (List (Skolem "a"), List (Skolem "a")))
             )));

  let t, c = Infer.infer environment (Constructor "Nil") in
  let c = Solver.solve environment c in
  print_endline @@ Pretty.render_ty @@ Type.normalize t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  let t, c = Infer.infer environment (Constructor "Cons") in
  let c = Solver.solve environment c in
  print_endline @@ Pretty.render_ty @@ Type.normalize t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  let t, c = Infer.infer environment (Apply (Constructor "Cons", Int 0)) in
  let c = Solver.solve environment c in
  print_endline @@ Pretty.render_ty @@ Type.normalize t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p);

  let t, c =
    Infer.infer environment
      (Apply (Apply (Constructor "Cons", Int 0), Constructor "Nil"))
  in
  let c = Solver.solve environment c in
  print_endline @@ Pretty.render_ty @@ Type.normalize t;
  c
  |> List.iter (fun (Predicate p) ->
         print_endline @@ Pretty.render_ty_predicate @@ Predicate.normalize p)
