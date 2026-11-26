/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Challenge: Written on the Wall II, Conjecture 61

**Conjecture (WOWII #61, Graffiti.pc).** If `G` is a simple connected graph, then
`f(G) ≥ residue(G) + ⌈diam(G)/3⌉`, where `f(G)` is the number of vertices of a largest induced
forest of `G`, `residue(G)` is the Havel–Hakimi residue of its degree sequence (the number of
zeros left when the Havel–Hakimi reduction terminates) and `diam(G)` is the diameter.

Source: E. DeLaViña, *Written on the Wall II (Conjectures of Graffiti.pc)*,
<http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj61>.

The statement is copied verbatim from google-deepmind/formal-conjectures,
`FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean` (theorem `conjecture61`, tagged
`research open` there), and the definitions of `havelHakimiStep`, `residueAux`, `residue` and
`largestInducedForestSize` verbatim from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/`
(`Residue.lean` and `Induced.lean`), all at commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53.
`diam`, `Connected` and `IsAcyclic` are Mathlib's. Only the Formal Conjectures attributes
(`category`, `AMS`) and the sanity checks are left out. Two proofs differ from the source, and no
definition or statement is changed: the helper lemma `havelHakimiStep_length_cons` is proved by
`rw` instead of `grind` (so that its proof term is identical in `Challenge.lean` and in
`Wowii61/Defs.lean`), and the final `omega` of the termination proof of `residueAux` is removed,
because on Lean 4.35 the preceding `rw` already closes the goal. The `sorry` marks the statement to be
proved; it is not a proof.
-/

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-!
## Residue
The residue of a graph is the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
-/

/--
Helper function: Performs one step of the Havel-Hakimi reduction on a degree sequence.
Assumes the input list `s` is sorted descending.
Removes the first element `d`, decrements the next `d` elements by 1, and re-sorts the list descending.

Note: when `s` is the list of vertices arising from a simple graph, if the first index is `s` then
the degree list always has length at least `s+1` so this makes sense.
-/
def havelHakimiStep (s : List ℕ) : List ℕ :=
  match s with
  | [] => []
  | d :: rest =>
    -- Split the rest into the part to decrement (first d elements) and the remaining part.
    let (to_decrement, remaining) := rest.splitAt d
    -- Decrement the elements
    let decremented := to_decrement.map (· - 1)
    -- Combine and re-sort descending.
    (decremented ++ remaining).mergeSort (· ≥ ·)

/--
`havelHakimiStep` drops the list length by exactly one on a nonempty list:
`(havelHakimiStep (d :: rest)).length = rest.length`. `splitAt` partitions `rest`,
and `map`, `++`, and `mergeSort` all preserve the total length while the head `d`
is dropped. This is the termination measure for the well-founded `residueAux` below.
-/
theorem havelHakimiStep_length_cons (d : ℕ) (rest : List ℕ) :
    (havelHakimiStep (d :: rest)).length = rest.length := by
  show (((rest.splitAt d).1.map (· - 1) ++ (rest.splitAt d).2).mergeSort (· ≥ ·)).length = rest.length
  rw [List.splitAt_eq, List.length_mergeSort, List.length_append, List.length_map,
    ← List.length_append, List.take_append_drop]

/--
Auxiliary function to calculate the residue recursively.
Applies Havel-Hakimi steps until the sequence consists only of zeros or is empty.
Defined by well-founded recursion on the list length (via `havelHakimiStep_length_cons`),
so that it admits equational and inductive reasoning.
-/
def residueAux : List ℕ → ℕ
  | [] => 0        -- Empty sequence, residue is 0.
  | 0 :: s => 1 + s.length -- If the largest degree is 0 (and the list is sorted), all are 0.
  | d :: rest => residueAux (havelHakimiStep (d :: rest)) -- Apply one reduction step and recurse.
termination_by l => l.length
decreasing_by
  simp_wf
  rw [havelHakimiStep_length_cons]

/--
Computes the residue of a graph `G`, i.e. the number of zeros remaining after iteratively
applying the Havel-Hakimi algorithm to the degree sequence until all remaining degrees are zero.
Starts with the descending degree sequence and applies the Havel-Hakimi process.
-/
noncomputable def residue (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Get the degree sequence sorted in descending order and apply `residueAux`.
  residueAux ((Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·))

end SimpleGraph

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `largestInducedForestSize G` is the size of a largest induced forest of `G`. -/
noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture61

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- **WOWII Conjecture 61.** For a finite simple connected graph `G` on at least two vertices,
the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ residue(G) + ⌈diam(G) / 3⌉`. -/
theorem conjecture61 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

end WrittenOnTheWallII.GraphConjecture61
