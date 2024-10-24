/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Plausible.Sampleable
import Plausible.Testable

/-!
## `plausible`: generators for functions

This file defines `Sampleable` instances for `α → β` functions and
`Int → Int` injective functions.

Functions are generated by creating a list of pairs and one more value
using the list as a lookup table and resorting to the additional value
when a value is not found in the table.

Injective functions are generated by creating a list of numbers and
a permutation of that list. The permutation insures that every input
is mapped to a unique output. When an input is not found in the list
the input itself is used as an output.

Injective functions `f : α → α` could be generated easily instead of
`Int → Int` by generating a `List α`, removing duplicates and creating a
permutation. One has to be careful when generating the domain to make
it vast enough that, when generating arguments to apply `f` to,
they argument should be likely to lie in the domain of `f`. This is
the reason that injective functions `f : Int → Int` are generated by
fixing the domain to the range `[-2*size .. 2*size]`, with `size`
the size parameter of the `gen` monad.

Much of the machinery provided in this file is applicable to generate
injective functions of type `α → α` and new instances should be easy
to define.

Other classes of functions such as monotone functions can generated using
similar techniques. For monotone functions, generating two lists, sorting them
and matching them should suffice, with appropriate default values.
Some care must be taken for shrinking such functions to make sure
their defining property is invariant through shrinking. Injective
functions are an example of how complicated it can get.
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Sort w}

namespace Plausible

/-- Data structure specifying a total function using a list of pairs
and a default value returned when the input is not in the domain of
the partial function.

`withDefault f y` encodes `x => f x` when `x ∈ f` and `x => y`
otherwise.

We use `Σ` to encode mappings instead of `×` because we
rely on the association list API defined in `Mathlib/Data/List/Sigma.lean`.
 -/
inductive TotalFunction (α : Type u) (β : Type v) : Type max u v
  | withDefault : List (Σ _ : α, β) → β → TotalFunction α β

instance TotalFunction.inhabited [Inhabited β] : Inhabited (TotalFunction α β) :=
  ⟨TotalFunction.withDefault ∅ default⟩

namespace TotalFunction

-- Porting note: new
/-- Compose a total function with a regular function on the left -/
def comp {γ : Type w} (f : β → γ) : TotalFunction α β → TotalFunction α γ
  | TotalFunction.withDefault m y =>
    TotalFunction.withDefault (m.map fun ⟨a, b⟩ => ⟨a, f b⟩) (f y)

/-- Apply a total function to an argument. -/
def apply [DecidableEq α] : TotalFunction α β → α → β
  | TotalFunction.withDefault m y, x => (m.find? fun ⟨a, _⟩ => a = x).map Sigma.snd |>.getD y

/-- Implementation of `Repr (TotalFunction α β)`.

Creates a string for a given `Finmap` and output, `x₀ => y₀, .. xₙ => yₙ`
for each of the entries. The brackets are provided by the calling function.
-/
def reprAux [Repr α] [Repr β] (m : List (Σ _ : α, β)) : String :=
  String.join <|
    -- Porting note: No `List.qsort`, so convert back and forth to an `Array`.
    Array.toList <| Array.qsort (lt := fun x y => x < y)
      (m.map fun x => s!"{(repr <| Sigma.fst x)} => {repr <| Sigma.snd x}, ").toArray

/-- Produce a string for a given `TotalFunction`.
The output is of the form `[x₀ => f x₀, .. xₙ => f xₙ, _ => y]`.
-/
protected def repr [Repr α] [Repr β] : TotalFunction α β → String
  | TotalFunction.withDefault m y => s!"[{(reprAux m)}_ => {repr y}]"

instance (α : Type u) (β : Type v) [Repr α] [Repr β] : Repr (TotalFunction α β) where
  reprPrec f _ := TotalFunction.repr f

/-- Create a `Finmap` from a list of pairs. -/
def List.toFinmap' (xs : List (α × β)) : List (Σ _ : α, β) :=
  xs.map (fun ⟨a, b⟩ => ⟨a, b⟩)

section

universe ua ub
variable [SampleableExt.{_,u} α] [SampleableExt.{_,ub} β]

variable [DecidableEq α]

/-- Shrink a total function by shrinking the lists that represent it. -/
def shrink {α β} [DecidableEq α] [Shrinkable α] [Shrinkable β] :
    TotalFunction α β → List (TotalFunction α β)
  | ⟨m, x⟩ => (Shrinkable.shrink (m, x)).map fun ⟨m', x'⟩ => ⟨dedup m', x'⟩
where
  dedup (m' : List ((_ : α) × β)) : List ((_ : α) × β) :=
    let rec insertKey (xs : List ((_ : α) × β))  (pair : (_ : α) × β) : List ((_ : α) × β) :=
      match xs with
      | [] => [pair]
      | x :: xs =>
        if pair.fst = x.fst then
          pair :: xs
        else
          x :: insertKey xs pair
    m'.foldl (init := []) insertKey

variable [Repr α]

instance Pi.sampleableExt : SampleableExt (α → β) where
  proxy := TotalFunction α (SampleableExt.proxy β)
  interp f := SampleableExt.interp ∘ f.apply
  sample := do
    let xs : List (_ × _) ← (SampleableExt.sample (α := List (α × β)))
    let ⟨x⟩ ← Gen.up <| (SampleableExt.sample : Gen (SampleableExt.proxy β))
    pure <| TotalFunction.withDefault (List.toFinmap' <| xs.map <|
      Prod.map SampleableExt.interp id) x
  -- note: no way of shrinking the domain without an inverse to `interp`
  shrink := { shrink := letI : Shrinkable α := {}; TotalFunction.shrink }

end

section SampleableExt

open SampleableExt

instance (priority := 2000) PiPred.sampleableExt [SampleableExt (α → Bool)] :
    SampleableExt.{u + 1} (α → Prop) where
  proxy := proxy (α → Bool)
  interp m x := interp m x
  sample := sample
  shrink := SampleableExt.shrink

instance (priority := 2000) PiUncurry.sampleableExt [SampleableExt (α × β → γ)] :
    SampleableExt.{imax (u + 1) (v + 1) w} (α → β → γ) where
  proxy := proxy (α × β → γ)
  interp m x y := interp m (x, y)
  sample := sample
  shrink := SampleableExt.shrink

end SampleableExt

end TotalFunction

end Plausible
