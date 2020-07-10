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

open Steel.Effect
open Steel.Memory

let extract_update: unit -> Tot unit = (fun () -> ())
let extract_get: unit -> Tot unit = (fun () -> ())
let extract_explode: unit -> Tot unit = (fun () -> ())
let extract_recombine: unit -> Tot unit = (fun () -> ())
let op_String_Access : unit -> Tot unit = (fun () -> ())
let generic_index: unit -> Tot unit = (fun () -> ())

#set-options "--fuel 0 --ifuel 1"

let update_x
  (r: ref (option u32_pair) u32_pair_pcm)
  (old_pair: Ghost.erased u32_pair)
  (new_val: UInt32.t)
    : SteelT unit
      (pts_to r (Some (Ghost.reveal old_pair)))
      (fun _ -> pts_to r (Some ({ old_pair with x = new_val})))
  =
  let real_old_pair =  read r (Some (Ghost.reveal old_pair)) in
  let new_pair = (Some ({Some?.v real_old_pair with x = new_val })) in
  write r (Some (Ghost.reveal old_pair)) new_pair

let get_x
  (r: ref (option u32_pair) u32_pair_pcm)
  (pair: Ghost.erased u32_pair)
    : SteelT (x:UInt32.t{pair.x == x})
      (pts_to r (Some (Ghost.reveal pair)))
      (fun x -> (pts_to r (Some (Ghost.reveal pair))))
  =
  let real_pair = read r (Some (Ghost.reveal pair)) in
  (Some?.v real_pair).x

let increment_generic
  (#cls: rw_pointer UInt32.t)
  (r: cls.pointer_ref)
  (v: Ghost.erased UInt32.t{UInt32.v v + 1 <= UInt.max_int 32})
    : SteelT unit
      (cls.pointer_slref r v)
      (fun _ -> cls.pointer_slref r (UInt32.add v 1ul))
  =
  let old_v = cls.pointer_get r v in
  cls.pointer_upd r v (UInt32.add old_v 1ul)

module Basics = Steel.SteelT.Basics

let u32_pair_get : rw_pointer_get_sig u32_pair u32_pair_ref slu32_pair =
  fun r g_pair ->
    let (rx, ry) : u32_ref & u32_ref = r in
    let g_stored = Ghost.hide (Some (MkStoredU32 g_pair.x)) in
    Basics.h_admit _ _

    (*let x  =
      Basics.frame #_ #(slu32_pair r g_pair) #(fun _ -> slu32_pair r g_pair)
       (fun _ -> read rx g_stored)
       (pts_to ry (Some (MkStoredU32 g_pair.y)))
    in
    let y  =
      Basics.frame #_ #(slu32_pair r g_pair) #(fun _ -> slu32_pair r g_pair)
       (fun _ -> read ry g_stored)
       (pts_to rx (Some (MkStoredU32 g_pair.x)))
    in
    let Some (MkStoredU32 x) = x in
    let Some (MkStoredU32 y) = y in
    let real_val = { x; y} in
    real_val*)


let u32_pair_upd: rw_pointer_upd_sig u32_pair u32_pair_ref slu32_pair =
  fun r g_pair v ->
    Basics.h_admit _ _

let recombinable (r: u32_pair_ref) (r12: u32_pair_ref) : prop
  = admit()

let explose_u32_pair_into_x_y (r: u32_pair_ref) (pair: u32_pair)
  : SteelT (r12:(u32_pair_ref){recombinable r r12})
  (slu32_pair r pair)
  (fun (r1, r2) ->
    pts_to r1 (Some (MkStoredU32 pair.x)) `star`
    pts_to r2 (Some (MkStoredU32 pair.y)))
  =
  Steel.SteelT.Basics.h_admit _ _


let recombine_u32_pair_from_x_y
  (r: u32_pair_ref)
  (r1: u32_ref)
  (v1: UInt32.t)
  (r2: u32_ref)
  (v2: UInt32.t)
  : SteelT unit
    (pts_to r1 (Some (MkStoredU32 v1)) `star` pts_to r2 (Some (MkStoredU32 v2)))
    (fun _ -> slu32_pair r ({ x = v1; y = v2}))
  =
  Steel.SteelT.Basics.h_admit _ _
