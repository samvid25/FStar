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

/// This module defines a mechanism for extracting arraystructs compatible with separation logic
/// into C arraystructs via Kremlin. This is a rough sketch of Proposal 5 as described here
/// https://github.com/FStarLang/FStar/wiki/Array-Structs-in-Steel

#set-options "--fuel 0 --ifuel 1"

(*** arraystruct types *)

/// The core of proposal 5 is to define a grammar of attributes for memory actions that Kremlin can
/// recognize and extract as C arraystruct manipulation primitives. As such, these extractable memory
/// actions should operate on types that represent C arraystructs, like Seq.lseq for arrays or F*
/// structs for structs.

/// The types manipulated by extractable Steel programs have to be restrained to F* structs and
/// Seq.lseq, because these translate to C structs and arrays. To let the user freely work on
/// user-defined, high-level types while maintaining a connection to low-level extractable types, one
/// can use the projection system that comes with Steel.

/// As an ongoing example, let us take a struct representing a pair of integers (e.g. a 2D point). We
/// start by the F* type that will guide our development and that we want to manipulate conveniently.
type u32_pair : Type u#0 = {
  x: UInt32.t;
  y: UInt32.t;
}

/// We want to be able to manipulate this F* struct as a C struct with idiomatic operations like:
/// - fields getter and setters
/// - taking the adress of a field as a first-class pointer to the value in the field.
/// The current extraction mechanism of Kremlin does not allow us to get that level of granularity
/// for F* structs like `u32_pair`. So instead, we need to come up with a representation of a pointer
/// to u32_pair that can be justified in the Steel memory mode.

(**** The pointer typeclass *)

/// This entails a switch from the good old `ref` type, because now the pointers that we manipulate
/// are no longer only one address inside the memory. Instead, we are going to use as many `ref` as
/// there are atoms in the type that we want to consider individually from a memory placement
/// standpoint. Conceptually, that amounts to breaking down structs and arrays from a single memory
/// references to as many references as there are struct fields or array cells, but those little
/// references are "contiguous" so we can treat them as a whole.

/// For our ongoing example, this means that we want two references for each field of the struct.
/// CAREFUL: this representation should remain hidden behind a `.fsti` interface to be able to
/// justify the soudness of the extraction.
let u32_ref = Steel.Reference.ref UInt32.t

let u32_pair_ref = u32_ref & u32_ref

/// We also give a separation logic term to say that there is a `u32_pair` at `u32_pair_ref`'s address.
let slu32_pair (r: u32_pair_ref) (v: u32_pair) : Mem.slprop u#1 =
  let (rx, ry) = r in
  pts_to rx full_perm v.x `Mem.star` pts_to ry full_perm v.y


/// We now need to tell Kremlin that `u32_pair_ref` is a pointer `u32_pair`. We do that through a
/// special typeclass, which is below. Note that the typeclass is indexed by a type `a`. The
/// interesting effects of the typeclass will happen when `a` is either an F* struct or a `Seq.lseq`,
/// as we'll see later.
class pointer (a: Type u#a) = {
  pref:  Type u#0;
  pslref: pref -> a -> Mem.slprop u#1;
}

/// Here's our pointer typeclass instantiation for `u32_pair`.
instance u32_pair_p : pointer u32_pair = {
  pref = u32_pair_ref;
  pslref = slu32_pair;
}

/// At this point, our `.fsti` for `u32_pair` should only contain:

(*
type u32_pair : Type u#0 = {
  x: UInt32.t;
  y: UInt32.t;
}

val u32_pair_p: pointer u32_pair
*)

/// This will be extracted to C into the following code:

(*
typedef struct {
  x: u32;
  y: u32;
} *u32_pair_p;
*)

/// Note here that the extraction will be guided by the shape of `u32_pair`. The patterns that will
/// be recognized for extraction are:
/// - F* structs
/// - `Seq.seq`, extracted into arrays

(**** Extraction attributes *)

/// Now that we have "pointers" to structs or arrays that use in their Steel representations multiple
/// memory references, we can write as Steel functions some C idiomatism like :
/// - struct field read or update;
/// - array index read or update.

/// This is a generalization of the current extraction mechanism that considers F* structs field taking
/// (e.g. `pair.x` like struct field reads), and the special treatment of `Low*.Buffer` functions
/// for array manipulation.

/// We will now proceed to tag Steel functions with "extraction attributes" corresponding to these
/// C idiomatic operations.

/// To ensure that the attribute grammar typechecks, we have to define dummy
/// functions so that the names are recognized.
val extract_struct_field_update: unit -> Tot unit
val extract_struct_field_read: unit -> Tot unit
val extract_struct_explode: unit -> Tot unit
val extract_struct_recombine: unit -> Tot unit

(***** struct field read *)

/// Let us now see what how to annotate a function corresponding to a struct field read. We add this
/// to our `.fsti`.

[@@extract_struct_field_read u32_pair_p.y]
val get_y (r: u32_pair_p.pref) (pair: Ghost.erased u32_pair)
  : SteelT (v:UInt32.t{pair.y == v})
  (u32_pair_p.pslref r pair) (fun x -> u32_pair_p.pslref r pair)

/// The attribute `[@@extract_struct_field_read u32_pair_p.y]` has to check syntactically that the
/// signature of `get_y` corresponds to a C struct field read. This entail the corresponding checks:
/// - `u32_pair_p` is an instantiation of `pointer u32_pair`
/// - `u32_pair` is an F* struct
/// - `y` is a field of `u32_pair`
/// - there exists a `pointer` typeclass instantiation `cls` indexed by the `u32_pair` type
/// - the first argument (`r`) of `get_y` has type `cls.pointer_ref`
/// - the second argument (`v`) of `get_y` has type `Ghost.erased u32_pair`
/// - the return type of `get_y` has the type of `u32_pair.y` and should have a refinement saying that
///   implies that its value is equal to the one of the second argument
/// - the pre and post ressources should imply `pointer.slref r v`

/// All these checks can be performed by a tactic that discharges some proof obligations to SMT if
/// need be.

/// Some comments about the meta-arguments that justify the soundness of extraction, given a read
/// that respect all of the above conditions.
///
/// We now thanks to separation logic that `get_y` only has access to the memory location of
/// reference [r], and nothing else.
///
/// This meta-argument justifies the fact that it is admissible to compile `get_y` with a mere
/// struct field read. `get_y` can do other things such as allocating a new address and then ditching
/// it, but this is not observable by another thread in our semantic. So we eliminate by extracting
/// to Kremlin execution traces that are unobservable and didn't change the computation result.
///
/// What if [get_y] assigns first one value then another? Then we claim that it does not matter since
/// this more complicated execution trace will be extracted by Kremlin to a simpler one. In F*
/// you would still have to prove that the F* body of `get_y` is frame perserving, so if you do
/// that then the frame preservedness still holds for the simpler version extracted by Kremlin.

(***** struct field update *)

/// Let us also suppose that we want to update the [x] field of the pair, but the action actually
/// takes the whole object. However, we only want this update to be extracted to an update of the [x]
/// field in C. This is how we would write it:

[@@ extract_struct_field_update u32_pair_p.x]
val update_x (r: u32_pair_p.pref) (old_pair: Ghost.erased u32_pair) (new_val: UInt32.t)
    : SteelT unit
    (u32_pair_p.pslref r old_pair)
    (fun _ -> u32_pair_p.pslref r ({ old_pair with x = new_val}))

/// What should the attribute `[@@extract_struct_field_update u32_pair]` checks for the signature of
/// `update_z` ?
///  - `u32_pair_p` is an instantiation of `pointer u32_pair`
///  - `u32_pair` is an F* struct
///  - `x` is a field of `u32_pair`
///  - `extract_struct_fieldupdate` means that `update_x` should have two arguments, the first
///     being the reference and the second being the new value
///  - `x` can actually be a path into the low-level structs, a sequence of field accesses and
///     array indexes. The type of the new value for update should correspond to the low-level type
///     at the end of the path in the low-level structure
///  -  pre and post-ressource should be `u32_pair_p.pslref r` with the right values

(***** struct explode *)

/// The explode/recombine functions are specialized to each struct, and to each pattern of struct
/// explosion that is allowed by the PCM governing the internal representation of the struct in
/// Steel. We'll show here an example for our pair of integers.

val recombinable (r: u32_pair_p.pref) (r12: u32_ref & u32_ref) : prop

[@@ extract_struct_explode u32_pair_p ->
  (ref UInt32.t, ref UInt32.t) ->
  recombinable
]
val explose_u32_pair_into_x_y (r: u32_pair_p.pref) (pair: Ghost.erased u32_pair)
  : SteelT (r12:(u32_ref & u32_ref){recombinable r r12})
  (u32_pair_p.pslref r pair)
  (fun (r1, r2) ->
    pts_to r1 full_perm pair.x `Mem.star`
    pts_to r2 full_perm pair.y)

/// This function can be easily implemented as it merely reveals the internal representation of
/// u32_pair_p. The attribute `extract_struct_explode` should perform the same kind of syntactic
/// checks that the previous attributes, and especially that the value of the `pair` splitted inside
/// the multiple references after explosion has not been modified. For more than two fields, the tuple
/// can be extended.
///
/// In the case of arrays, the explosion can have a signature similar to `sub`.

/// The recombine function is the reciprocal, and the attribute has to be made aware of the prior
/// definition of exlode, since you can only recombine things that you have previously splitted.
[@@ extract_struct_recombine u32_ref -> u32_ref -> u32_pair_p -> explose_u32_pair_into_x_y ]
val recombine_u32_pair_from_x_y
  (r: u32_pair_p.pref)
  (r1: u32_ref)
  (v1: Ghost.erased UInt32.t)
  (r2: u32_ref{recombinable r (r1, r2)})
  (v2: Ghost.erased UInt32.t)
  : SteelT unit
    (pts_to r1 full_perm v1 `Mem.star` pts_to r2 full_perm v2)
    (fun _ -> slu32_pair r ({ x = v1; y = v2}))
