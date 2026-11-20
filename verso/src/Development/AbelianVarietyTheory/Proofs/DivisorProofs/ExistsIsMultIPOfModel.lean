import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Supply the required witnesses or components. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem IsMultIP₂ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := by
  have h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := fun x y hxy => by
    by_contra hc
    apply hxy
    rw [h, ipM, dif_neg hc, mul_zero]
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, fun v v' => by simp⟩
  by_cases hxy : inner ℂ x y = 0
  · obtain ⟨c, hc⟩ := h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)
    obtain ⟨c', hc'⟩ := h1 x x (inner_self_ne_zero.2 hx)
    refine ⟨c - c', fun v v' => ?_⟩
    have e : (fun g => star (H.e x v g) * H.e y v' g) =
        fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
      funext g; simp [mul_add]
    rw [e]
    exact ⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩
  · exact h1 x y hxy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem schurMult_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R h i σ _ _ _ T hT T' hT'
  obtain ⟨-, hr, hip⟩ := h i σ
  have hT1 : T ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT
  have hT2 : T' ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT'
  obtain ⟨x, rfl⟩ := hT1
  obtain ⟨y, rfl⟩ := hT2
  exact IsMultIP₂ (R.HW i σ) hip x y

end GlobalTheory.LiftLower

end
