(* reads "op a b" lines, prints results; compared against Python by tests/ztest.py *)
module Z = Kernel.Z
let () =
  try while true do
    match String.split_on_char ' ' (input_line stdin) with
    | [op; a; b] ->
      let x = Z.of_string a and y = Z.of_string b in
      let r = match op with
        | "add" -> Z.to_string (Z.add x y)
        | "sub" -> if Z.leq y x then Z.to_string (Z.sub x y) else "0"
        | "mul" -> Z.to_string (Z.mul x y)
        | "div" -> if Z.sign y = 0 then "0" else Z.to_string (Z.div x y)
        | "mod" -> if Z.sign y = 0 then a else Z.to_string (Z.rem x y)
        | "gcd" -> Z.to_string (Z.gcd x y)
        | "and" -> Z.to_string (Z.logand x y)
        | "or" -> Z.to_string (Z.logor x y)
        | "xor" -> Z.to_string (Z.logxor x y)
        | "shl" -> Z.to_string (Z.shift_left x (Z.to_int y))
        | "shr" -> Z.to_string (Z.shift_right x (Z.to_int y))
        | "pow" -> Z.to_string (Z.pow x (Z.to_int y))
        | "cmp" -> string_of_int (Z.compare x y)
        | "bits" -> string_of_int (Z.numbits x)
        | _ -> "?" in
      print_endline r
    | _ -> ()
  done with End_of_file -> ()
