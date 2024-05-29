module StringMap = struct
  include Map.Make (String)

  let union_left m m' = union (fun _ l _ -> Some l) m m'
  let union_append m m' = union (fun _ v v' -> Some (v @ v')) m m'
end
