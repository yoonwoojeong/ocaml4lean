(* growable array *)
type 'a t = { mutable data : 'a array; mutable len : int }
let create () = { data = [||]; len = 0 }
let length v = v.len
let data v = v.data
let push v x =
  if v.len = Array.length v.data then begin
    let nd = Array.make (max 8 (2 * v.len)) x in
    Array.blit v.data 0 nd 0 v.len;
    v.data <- nd
  end;
  v.data.(v.len) <- x;
  v.len <- v.len + 1
let to_array v = Array.sub v.data 0 v.len
let get v i = v.data.(i)
