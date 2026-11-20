import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Take `⟨l, hl⟩` from `h1 K b`. Rewrite using `[hl f]`. Use `clear hl`. Proceed by induction on `l with`. Consider the case `nil`.

Introduce `cs`. Use `Filter.Eventually.of_forall fun m => ?_` and prove the remaining obligations. Establish `h0` using `(h2 K n cs f f 0 0 0).2.1`. Rewrite `h0` using `[zero_smul, zero_smul]`. Simplify using `only [List.map_nil, List.sum_nil]`.

Rewrite using `[h0]`. Both sides reduce to the same expression. Consider the case `cons t l ih`. Simplify using `only [List.map_cons, List.sum_cons]`. Establish `hs : DegLT (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n` using `(h3 K n (diffStep (Pi.single t.1.1 1) f) f 0 t.1.2).2.2.1 (hf t.1.1)`.

Establish `hc : DegLT (t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n` using `(h3 K n (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) f t.2 0).2.1 hs`. Conclude with `(h3 K n _ (List.map (fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) l).sum 0 0).1 hc ih`.
-/
theorem DegLTOfUnitSteps.degLT_diffStep (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement)
    (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ)
    (hf : ∀ k, DegLT (diffStep (Pi.single k 1) f) n) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  obtain ⟨l, hl⟩ := h1 K b
  rw [hl f]
  clear hl
  induction l with
  | nil =>
    intro cs
    refine Filter.Eventually.of_forall fun m => ?_
    have h0 := (h2 K n cs f f 0 0 0).2.1
    rw [zero_smul, zero_smul] at h0
    simp only [List.map_nil, List.sum_nil]
    rw [h0]
    rfl
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs : DegLT (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (diffStep (Pi.single t.1.1 1) f) f 0 t.1.2).2.2.1 (hf t.1.1)
    have hc : DegLT (t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) f t.2 0).2.1 hs
    exact (h3 K n _ (List.map (fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) l).sum
      0 0).1 hc ih

/- English proof (translation)
Introduce `K _ _ n f hf bs`. Establish `key : mixedDiff bs f = mixedDiff (Fin.tail bs) (diffStep (bs 0) f)`. Rewrite using `[(h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.1, ← (h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.2]`. Use `congr 1`. Conclude with `(Fin.cons_self_tail bs).symm`.

Rewrite using `[key]`. Conclude with `DegLTOfUnitSteps.degLT_diffStep h1 h2 h3 K n f hf (bs 0) _`.
-/
theorem DegLTOfUnitSteps.proof (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement) :
    DegLTOfUnitSteps.Statement := by
  intro K _ _ n f hf bs
  have key : mixedDiff bs f = mixedDiff (Fin.tail bs) (diffStep (bs 0) f) := by
    rw [(h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.1,
      ← (h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.2]
    congr 1
    exact (Fin.cons_self_tail bs).symm
  rw [key]
  exact DegLTOfUnitSteps.degLT_diffStep h1 h2 h3 K n f hf (bs 0) _

end GroundTheory.Heights₂.Heights.NumbersDVR
