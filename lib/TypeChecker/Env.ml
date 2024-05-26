open Prelude
open Syntax

type t = {
  mutable constructors : ty_constructor StringMap.t;
  mutable instances : ty_instance list StringMap.t;
  mutable values : ty StringMap.t;
}

let create () =
  {
    constructors = StringMap.empty;
    instances = StringMap.empty;
    values = StringMap.empty;
  }

let add_constructor k v e = e.constructors <- StringMap.add k v e.constructors
let get_constructor k e = StringMap.find_opt k e.constructors
let add_instance k v e = e.instances <- StringMap.add_to_list k v e.instances

let get_instances k e =
  StringMap.find_opt k e.instances |> Option.value ~default:[]

let with_instance k v f e =
  let previous_instances = e.instances in
  e.instances <- StringMap.add_to_list k v e.instances;
  let r = f () in
  e.instances <- previous_instances;
  r

let add_value k v e = e.values <- StringMap.add k v e.values
let get_value k e = StringMap.find_opt k e.values

let with_value k v f e =
  let previous_values = e.values in
  e.values <- StringMap.add k v e.values;
  let r = f () in
  e.values <- previous_values;
  r
