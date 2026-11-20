import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GraphClosed.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G H : LineBundle k x), G.toSubSystem.Generated → IsVeryAmple H.toSubSystem →
    IsVeryAmple (G.toSubSystem.twist H.toSubSystem)

def PointGenerated.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x), IsSubvar x (primeOf (S := k) x) 0 → Q.toSubSystem.Generated

section Hypotheses

variable (k : Type u) [Field k]

/- English proof (translation)
Establish `h1 : (1 : Ω) ∈ (twistSys S x 0).secs`. Rewrite using `[SubSystem.secs, Submodule.mem_iInf]`. Introduce `I`. Conclude with `one_mem_twistMod_zero I`. Introduce `I`.

Take `⟨i, hi⟩` from `I.2.1`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr fun z hz => ?_` and prove the remaining obligations. Rewrite `hz` using `[SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf]`. Conclude with `hz I`.

Express the relevant statement in the definitionally equal form `twistMod S x 0 I ≤ _`. Rewrite using `[twistMod_eq_span 0 I hi, zpow_zero]`. Conclude with `Submodule.span_mono (Set.singleton_subset_iff.mpr h1)`.
-/
theorem generated_twistSys_zero' {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} : (twistSys S x 0).Generated := by
  have h1 : (1 : Ω) ∈ (twistSys S x 0).secs := by
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact one_mem_twistMod_zero I
  intro I
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf] at hz
    exact hz I
  · change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr h1)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
