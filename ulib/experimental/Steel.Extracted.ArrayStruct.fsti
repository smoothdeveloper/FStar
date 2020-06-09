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

module Steel.Extracted.ArrayStruct

module AS = Steel.ArrayStruct
module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
open Steel.PCM
module PCMBase = Steel.PCM.Base

open Steel.Effect
open Steel.Memory

/// This module defines a mechanism for extracting arraystructs compatible with separation logic
/// into C arraystructs via Kremlin. This is a rough sketch of Proposal 5 as described here
/// https://github.com/FStarLang/FStar/wiki/Array-Structs-in-Steel

#set-options "--fuel 0 --ifuel 0"


(*** arraystruct types *)

/// The core of proposal 5 is to define a grammar of attributes for memory actions that Kremlin can
/// recognize and extract as C arraystruct manipulation primitives. As such, these extractable memory
/// actions should operate on types that represent C arraystructs, like Seq.lseq for arrays or F* structs for structs.

/// The types manipulated by extractable Steel programs have to be restrained to F* structs and Seq.lseq, because
/// these translate to C structs and arrays. To let the user freely work on user-defined, high-level types while
/// maintaining a connection to low-level extractable types, one can use the projection system that comes with Steel.

(*
  Ongoing example: foo_low is the low-level representation of [foo_view],
  compatible with Kremlin extraction
*)
type u32_pair : Type u#1 = {
  x: UInt32.t;
  y: UInt32.t;
}

open FStar.Tactics

(**
  This tactics checks whether a declared type falls into the subset allowed by Kremlin.
  Can also be done at extraction but less useful error messages
*)
let check_low (src: string) : Tac unit =
  exact (`(()))

(* Ongoing example : this check could be inserted via some metaprogramming or surface language *)
let _ : unit  = _ by (check_low (`%u32_pair))

(*** The attribute grammar in actions *)

/// Let us now illustrate what the attribute language will look like by annotating memory actions,
/// either generic for all low/view pairs or on our ongoing example [foo].

open FStar.Tactics.Typeclasses

(** We are going to use pre/post conditions for specifications in Steel, so we need this helper *)
let uref (#a: Type u#a) (#pcm: pcm a) (r: ref a pcm) : slprop u#a =
  h_exists (pts_to r)

(**
  Also this helper [sel] function will allow use to retrieve the values of references witout
  while we don't have selectors.
*)
val selref (#a: Type) (#pcm: pcm a) (r: ref a pcm) (h: hmem (uref r)) : GTot a

(** Let us give a simple PCM for the pair *)
let u32_pair_pcm : pcm (option u32_pair) = PCMBase.exclusive_pcm

(** We don't bother proving the self-framedness of pre/postconditions in this sketch *)
val admitted_post
  (#a: Type) (#pre:slprop) (#post: a -> slprop)
  (p:(hmem pre -> x:a -> hmem (post x) -> GTot prop))
  : GTot (p:(hmem pre -> x:a -> hmem (post x) -> prop){respects_binary_fp p})

val admitted_pre
  (#pre:slprop)
  (p:(hmem pre -> GTot prop))
  : GTot (p:(hmem pre -> prop){respects_fp p})

/// To ensure that the attribute grammar typechecks, we have to define dummy functions so that
/// the names are recognized.

val extract_update: unit -> Tot unit
val extract_get: unit -> Tot unit
val extract_explode: unit -> Tot unit
val extract_recombine: unit -> Tot unit
val op_String_Access : unit -> Tot unit
val generic_index: unit -> Tot unit

(**** update *)

/// Let us also suppose that we want to update the [x] field of the pair, but the action actually
/// takes the whole object. However, we only want
/// this update to be extracted to an update of the [x] field in C. This is how we would write it:

[@@ extract_update u32_pair.x]
val update_x (r: ref (option u32_pair) u32_pair_pcm) (new_val: UInt32.t)
    : Steel unit (uref r) (fun _ -> uref r)
    (admitted_pre (fun h0 -> if Some? (selref r h0) then True else False)) (admitted_post (fun h0 _ h1 ->
     Some? (selref r h1) /\ Some? (selref r h0) /\
     Some?.v (selref r h1) == { Some?.v (selref r h0) with x = new_val }
    ))

/// What should the attribute `[@@extract_update u32_pair]` checks for the signature of
/// `update_z` ?
///  - `extract_update` means that `update_x` should have two arguments, the first being the
///     reference and the second being the new value
///  - `u32_pair` means that the reference should point to a option u32_pair
///  - `x` can actually be a path into the low-level structs, a sequence of field accesses and
///     array indexes. The type of the new value for update should correspond to the low-level type
///     at the end of the path in the low-level structure
///  -  pre and post-ressource should be `uref r`, return type unit
///  -  finally, the postcondition of `update_x` should imply the following semantic definition
///     of a low-level update:
///     ```
///     Some?.v (selref r h1) == { Some?.v (selref r h0) with x = new_val }
///     ```
///
/// While the first 4 checks are completely syntactic, the last one can be discharged to SMT. Please
/// note that the bijection is important here because it will allow us to prove this last semantic
/// obligation, by "lifting" the equality in the low-level world to the high-level views where
/// the real postcondition of the function is specified.

(* Ongoing example: sketch on how to use a tactic for checking what is described above *)
let check_extract_update (src: string) : Tac unit =
  exact (`(()))

let _ : unit  = _ by (check_extract_update (`%update_x))

/// Some comments about the meta-arguments that justify the soundness of extraction, given an
/// update with attribute that respect all of the above conditions.
///
/// We now thanks to separation logic that `update_x` can only modify the memory location of
/// reference [r], and nothing else.
/// This meta-argument justifies the fact that it is admissible to compile `update_z` with a mere
/// memory update. `update_z` can do other things such as allocating a new address and then ditching
/// it, but this is not observable by another thread in our semantic. So we eliminate by extracting
/// to Kremlin execution traces that are unobservable and didn't change the computation result.
///
/// What if [update_z] assigns first one value then another? Then we claim that it does not matter since this more complicated execution trace will be extracted by Kremlin to a simpler one. In F*
/// you would still have to prove that the F* body of `update_x` is frame perserving, so if you do
/// that then the frame preservedness still holds for the simpler version extracted by Kremlin.


(**** get *)

/// Let us now see what how to annotate a function corresponding to a low-level read.

[@@extract_get u32_pair.y]
val get_x (r: ref (option u32_pair) u32_pair_pcm)
  : Steel UInt32.t
  (uref r) (fun _ -> uref r)
  (admitted_pre (fun h0 -> if Some? (selref r h0) then True else False)) (admitted_post (fun h0 v h1 ->
    Some? (selref r h0) /\ Some? (selref r h1) /\
    selref r h0 == selref r h1 /\ v == (Some?.v (selref r h1)).y
  ))

/// The attribute `[@@extract_get u32_pair.x]` still has to check syntactically that the
/// signature of `get_x` corresponds to a low-level get (one argument which is a ref, returns
/// a value of the right type).
///
/// So what is the semantic post-condition implication check here ? Let's call `v` the returned value
///
/// ```
/// selref r h0 == selref r h1 /\ v == (Some?.v (selref r h1)).y
/// ```
///

(*** Address taking *)

/// Let us now tackle an important feature requested for our extraction and object manipulation
/// language: first-class pointers to parts of a arraystruct.

(**** The pointer typeclass *)

/// This entails a switch from the good old `ref` type, because now the pointers that we manipulate
/// are no longer only addresses inside the memory, we need to add the info of the path inside the
/// reference. Because we want functions not to care whether they receive a pointer that is a full
/// reference or just part of a reference, we create a "pointer" typeclass that will define the
/// interface that our pointers should implement.

let pointer_get_sig
  (a: Type u#a)
  (ref: Type u#0)
  (slref: ref -> slprop)
  (sel: (r:ref) -> hmem (slref r) -> GTot a)
  =
  r:ref ->
    Steel a
      (slref r)
      (fun _ -> slref r)
      (fun _ -> True)
      (admitted_post (fun h0 x h1 -> sel r h0 == sel r h1 /\ sel r h0 == x))

let pointer_upd_sig
  (a: Type u#a)
  (ref: Type u#0)
  (slref: ref -> slprop)
  (sel: (r:ref) -> hmem (slref r) -> GTot a)
  (upd_pre: (r:ref) -> hmem (slref r) -> GTot prop)
  =
  r: ref ->
  new_val: a -> (* This has to be a Low* type because this upd *)
    Steel unit
      (slref r)
      (fun _ -> slref r)
      (admitted_pre (fun h0 -> upd_pre r h0))
      (admitted_post (fun h0 _ h1 -> sel r h1 == new_val))

#push-options "--admit_smt_queries true" (* fails, points to subcomp_pre? *)
class pointer (a: Type u#a) = {
  ref:  Type u#0;
  slref: ref -> slprop;
  sel: (r:ref) -> hmem (slref r) -> GTot a;
  get: pointer_get_sig a ref slref sel; (* this get should have been annotated with the attribute*)
  upd_pre: (r:ref) -> hmem (slref r) -> GTot prop;
  upd: pointer_upd_sig a ref slref sel upd_pre;
   (* this upd should have been annotated with the attribute*)
}
#pop-options

/// Lets us now instantiate this typeclass of the fields of of our u32_pair. What will be the ref
/// type ? We have to introduce a new piece of information inside the memory reference, to allow us
/// to distinguish which part of the reference we are owning inside a thread.


type u32_pair_path =
| Full
| XField
| YField

let u32_pair_stored = option (u32_pair & u32_pair_path)

/// Now, we have to define a PCM that will render possible the fact to share the ownership on the
/// fields of the struct.

#push-options "--ifuel 1"
let u32_pair_composable : symrel (u32_pair_stored) = fun a b -> match a, b with
  | Some (a, a_path), Some (b, b_path) -> begin
    match a_path, b_path with
    | XField, YField
    | YField, XField -> True
    | _ -> False
  end
  | _ -> True
#pop-options

let u32_pair_compose
  (a: u32_pair_stored)
  (b: u32_pair_stored{a `u32_pair_composable` b})
  : u32_pair_stored =
  match a, b with
  | Some (a, a_path), Some (b, b_path) -> begin
    match a_path, b_path with
    | XField, YField -> Some (({ x = a.x; y = b.y}), Full)
    | YField, XField -> Some (({ x = b.x; y = a.y}), Full)
  end
  | None, Some _ -> b
  | Some _, None -> a
  | None, None -> None

#push-options "--z3rlimit 15 --ifuel 1"
let u32_pair_stored_pcm : pcm u32_pair_stored = {
  p = {
    composable = u32_pair_composable;
    op = u32_pair_compose;
    one = None;
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
}
#pop-options

let u32_pair_ref = Steel.Memory.ref u32_pair_stored u32_pair_stored_pcm

/// We can now instantiate the pointer typeclass!

let slu32_pair (r: u32_pair_ref) =
  h_exists (fun (v: u32_pair_stored) -> pts_to r v `star` pure (Some? v /\ snd (Some?.v v) == Full))

#push-options "--admit_smt_queries false"
instance u32_pair_pointer : pointer u32_pair = {
  ref = u32_pair_ref;
  slref = slu32_pair;
  sel = (fun r h ->
    fst (Some?.v (selref r h))
  );
  get = admit();
  upd_pre = admit();
  upd = admit();
}
#pop-options

/// But we can also instantiate it for the leaves of our structure

#push-options "--admit_smt_queries true"
instance u32_pair_x_pointer : pointer UInt32.t = {
  ref = u32_pair_ref;
  slref = (fun r ->
    (* h_refine (fun h -> Some? (sel r h) /\ snd (Some?.v (sel r h)) == XField *)
    h_exists (pts_to r)
  );
  sel = (fun r h ->
    assume(Some? (selref r h) /\ snd (Some?.v (selref r h)) == XField);
    (fst (Some?.v (selref r h))).x
  );
  get = admit();
  upd_pre = admit();
  upd = admit();
}
#pop-options

(* Note for explode/recombine:
  - no magic wand in explode, have to encode it with a recombinable predicate
  - no ties to parent object after explode, recombine stitches back views together like array split
  - focus encapsulates an explode with a magic wand signature
*)

(**** explode *)

/// For explode, we want to decompose a arraystruct into multiple parts. This decomposition should
/// be total, meaning that you can recompose the parts to get your arraystruct later. To qualify the
/// totalness of this decomposition, we instantiante the same `low_level` typeclass which qualifies
/// a bijection.

/// Let us see what it gives with our ongoing example. Let's suppose our decomposition is simply

let exploded_foo =
  Seq.lseq u#1 (Universe.raise_t UInt32.t) 2 & (Universe.raise_t u#0 u#1 UInt64.t)

/// Tuples would receive special treatment by Kremlin, as they would be extracted to multiple pointer
/// values.

(* Here is the bijection of the decomposition *)
instance low_level_decomposition_foo : low_level foo_view  =
  let view_to_low : foo_view -> exploded_foo = fun v ->
    (
      Seq.init 2 (fun i ->
        if i = 0 then Universe.raise_val v.view_x else Universe.raise_val v.view_y
      ),
      Universe.raise_val v.view_z
    )
  in
  let low_to_view : exploded_foo -> foo_view = fun (v1, v2) ->
    {
      view_x = Universe.downgrade_val (Seq.index v1 0);
      view_y = Universe.downgrade_val (Seq.index v1 1);
      view_z = Universe.downgrade_val v2;
    }
  in
  {
  low = exploded_foo;
  view_to_low = view_to_low;
  low_to_view = low_to_view;
  bijection_one = (fun _ -> ());
  bijection_two = (fun l ->
    let new_l = view_to_low (low_to_view l) in
    assert((fst new_l) `Seq.equal` (fst l));
    assert((snd new_l) == (snd l));
    assert(new_l == l)
  );
}

/// Now that we have specified how our view should be decomposed, we can write our explode function,
/// with an attribute.


(*TODO: use magic wands for the signature *)
[@@ extract_explode foo_low -> low_level_decomposition_foo -> (low_level_xy, low_level_z)]
val explode_foo (r: ref foo_view foo_pcm)
  : Steel (
    ref (Seq.lseq (Universe.raise_t UInt32.t) 2) xy_pcm &
    ref (Universe.raise_t UInt64.t) u64_pcm
  )
  (slref r) (fun (r1, r2) ->
    slref r1 `star` slref r2
  )
  (fun _ -> True) (admitted_post (fun h0 (r1, r2) h1 ->
    sel r h0 == low_level_decomposition_foo.low_to_view (sel r1 h1, sel r2 h1)
  ))

/// How can this function be implemented? Simply by allocating two new references inside the memory
/// model corresponding to r1 and r2, then copying the contents of r into r1 and r2. But then
/// we still have `slref r` in the post-resource, whereas the function only talks about `r1` and `r2`.
///
/// The solution is that we simply drop `slref r` by affinity of the memory model. There again we
/// need a meta-argument to justify that this can safely be extracted to an address taking
/// instruction, whereas this is implemented in F* by allocating and dropping memory.

[@@ extract_recombine (low_level_xy, low_level_z) -> low_level_decomposition_foo -> foo_low]
val recombine_foo
  (r1: ref (Seq.lseq (Universe.raise_t UInt32.t) 2) xy_pcm)
  (r2: ref (Universe.raise_t UInt64.t) u64_pcm)
  : Steel (ref foo_view foo_pcm)
  (slref r1 `star` slref r2) (fun r -> slref r)
  (fun _ -> True) (admitted_post (fun (h0 : hmem (slref r1 `star` slref r2)) r h1 ->
    sel r h1 == low_level_decomposition_foo.low_to_view (sel r1 h0, sel r2 h0)
  ))
(*

(*
1. Drop the foo_view, do everything with the foo_low, foo_view can later be user-defined
2. we need a pointer type for exploded objects ->
  a) having a subref type that is defined with a ref and then a path inside a ref, depending on the struct
  b) then, the subref type should implement a "pointer-like" typeclass
*)

type foo : Type u#1 = {
  x: UInt32.t;
  y: UInt32.t;
}

class pointer_like (a: Type u#a) = {
  ref: Type u#0;
  slprop: slprop;
  deref: ref -> Steel a (slprop) (fun _ -> slprop) (fun _ -> True) (fun _ _ _ -> True); (* here put sel specs *)
  upd: ref -> (new_val: a) -> Steel unit (slprop) (fun _ -> slprop) (fun _ -> True) (fun _ _ _ -> True); (* here put sel specs *)
}

type foo_path = option bool

val type_inside_foo (path:foo_path) : Type u#a

instance _ : pointer_like (type_inside_foo None) = {
  ref: (r:ref (foo & foo_path))
  slprop: h_refine (slref foo) (fun h -> snd (sel r h) == None)
  deref: deref_foo;
  upd: upd_foo;
}

type subref_foo = ref (foo, foo_path)  (* the int is here to encode which field of foo you want to choose, there are 3 fields in foo *)

val explode_foo (r: ref subref_foo) :
  Steel (r1: subref_foo & r2: subref_foo)

instance _ : pointer_like UInt32.t = {
  ref: ref (foo,;
  slprop:
}


val incr (r: pointer_like UInt32) : Steel
*)

/// Things to talk with Nik :
///  - (if Some? (selref r h0) then True else False) weird universe bug
///  - we want custom paths for our structs because with a generic thing it'll have to be recursive
///    and that will not play out well with the SMT
///  - whole arrays cannot be updated at once in C, the checking tactic can make sure it is not
///    the case
