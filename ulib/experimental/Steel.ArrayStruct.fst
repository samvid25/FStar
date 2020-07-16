(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.ArrayStruct

module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
open Steel.PCM
module PCMBase = Steel.PCM.Base
module Mem = Steel.Memory

open Steel.Effect
open Steel.Reference
open Steel.FractionalPermission

let extract_struct_field_update: unit -> Tot unit = fun () -> ()
let extract_struct_field_read: unit -> Tot unit = fun () -> ()
let extract_struct_explode: unit -> Tot unit = fun () -> ()
let extract_struct_recombine: unit -> Tot unit = fun () -> ()

module Basics = Steel.SteelT.Basics

let get_y (r: u32_pair_p.pref) (pair: Ghost.erased u32_pair)
  : SteelT (v:UInt32.t{pair.y == v})
  (u32_pair_p.pslref r pair) (fun x -> u32_pair_p.pslref r pair)
  =
  let (rx, ry) = r in
  Basics.h_commute (pts_to rx full_perm pair.x) (pts_to ry full_perm pair.y);
  let v =  Basics.frame (fun () -> read #UInt32.t #full_perm #pair.y ry) (pts_to rx full_perm pair.x) in
  Basics.h_commute (pts_to ry full_perm pair.y) (pts_to rx full_perm pair.x);
  v

let update_x (r: u32_pair_p.pref) (pair: Ghost.erased u32_pair) (new_val: UInt32.t)
  : SteelT unit
    (u32_pair_p.pslref r pair)
    (fun _ -> u32_pair_p.pslref r ({ pair with x = new_val}))
  =
  let (rx, ry) = r in
  Basics.frame (fun () -> write #UInt32.t #pair.x rx new_val) (pts_to ry full_perm pair.y)

let recombinable (r: u32_pair_p.pref) (r12: u32_ref & u32_ref) = r == r12

let explose_u32_pair_into_x_y (r: u32_pair_p.pref) (pair: Ghost.erased u32_pair)
  : SteelT (r12:(u32_ref & u32_ref){recombinable r r12})
  (u32_pair_p.pslref r pair)
  (fun (r1, r2) ->
    pts_to r1 full_perm pair.x `Mem.star`
    pts_to r2 full_perm pair.y)
  =
  Basics.change_slprop _ _ (fun _ -> ());
  Basics.return r

let recombine_u32_pair_from_x_y
  (r: u32_pair_p.pref)
  (r1: u32_ref)
  (v1: Ghost.erased UInt32.t)
  (r2: u32_ref{recombinable r (r1, r2)})
  (v2: Ghost.erased UInt32.t)
  : SteelT unit
    (pts_to r1 full_perm v1 `Mem.star` pts_to r2 full_perm v2)
    (fun _ -> slu32_pair r ({ x = v1; y = v2}))
  =
  Basics.change_slprop _ _ (fun _ -> ())
