module StringMap = struct
  include Map.Make (String)

  let union_append m m' = union (fun _ v v' -> Some (v @ v')) m m'
end
