module Test1_7

module DM = FStar.DependentMap
module S  = FStar.Pointer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

type struct_fd =
| F1
| F2
| F3
| F4
| F5
| F6
| F7

let struct_struct_ty = function
| F1 -> int
| F2 -> int
| F3 -> int
| F4 -> int
| F5 -> int
| F6 -> int
| F7 -> int

let struct_struct = DM.t struct_fd struct_struct_ty

let struct = S.pointer struct_struct

let write_struct_spec (h : HS.mem) (s : struct) : GTot Type0 =
  Pointer.gread h (Pointer.gfield s F1) = 1 /\
  Pointer.gread h (Pointer.gfield s F2) = 2 /\
  Pointer.gread h (Pointer.gfield s F3) = 3 /\
  Pointer.gread h (Pointer.gfield s F4) = 4 /\
  Pointer.gread h (Pointer.gfield s F5) = 5 /\
  Pointer.gread h (Pointer.gfield s F6) = 6 /\
  Pointer.gread h (Pointer.gfield s F7) = 7 /\
  True

let write_struct (s : struct) : HST.Stack unit
  (requires (fun h -> Pointer.live h s))
  (ensures (fun h0 _ h1 ->
    Pointer.live h1 s /\
    write_struct_spec h1 s
  ))
=
  let _ = Pointer.write (Pointer.field s F1) 1 in
  let _ = Pointer.write (Pointer.field s F2) 2 in
  let _ = Pointer.write (Pointer.field s F3) 3 in
  let _ = Pointer.write (Pointer.field s F4) 4 in
  let _ = Pointer.write (Pointer.field s F5) 5 in
  let _ = Pointer.write (Pointer.field s F6) 6 in
  let _ = Pointer.write (Pointer.field s F7) 7 in
  ()


