module

public import Wowii61.Main

/-!
# Solution: Written on the Wall II, Conjecture 61

Supplies the proof of `WrittenOnTheWallII.GraphConjecture61.conjecture61` stated in
`Challenge.lean`. The definitions come from `Wowii61/Defs.lean` (identical to the Challenge
definitions); the proof is `Graffiti61.conjecture61` in `Wowii61/Main.lean`.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture61

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- **WOWII Conjecture 61.** For a finite simple connected graph `G` on at least two vertices,
the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ residue(G) + ⌈diam(G) / 3⌉`. -/
theorem conjecture61 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) :=
  Graffiti61.conjecture61 G h

end WrittenOnTheWallII.GraphConjecture61
