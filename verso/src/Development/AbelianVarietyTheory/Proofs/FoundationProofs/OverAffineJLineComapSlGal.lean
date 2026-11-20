import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRatStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

/- English proof (translation)
Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem vs_mem_of_isIntegral {K : Type} [Field K] (W : ValuationSubring K) {x : K} (h : IsIntegral W x) : x ∈ W := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]; exact y.2

/- English proof (translation)
Rewrite using `[HahnSeries.algebraMap_apply']`. Establish `: algebraMap Ω (PowerSeries Ω) c = PowerSeries.C c` using `rfl`. Rewrite using `[this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]`. Simplify using the standard rewrite rules.
-/
theorem hs_coeff_algebraMap {Ω : Type} [Field Ω] (c : Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  have : algebraMap Ω (PowerSeries Ω) c = PowerSeries.C c := rfl
  rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  simp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Apply `(X.exp : X.K →+* HahnSeries ℚ Ω).injective` to reduce the goal to its premises. Use extensionality with `r`. Express the relevant statement in the definitionally equal form `(X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r`. Rewrite using `[X.gal_exp, AlgHom.commutes, AlgHom.commutes, hs_coeff_algebraMap, hs_coeff_algebraMap]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Tower.gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, hs_coeff_algebraMap, hs_coeff_algebraMap]
  split_ifs <;> simp

/- English proof (translation)
Apply `(X.exp : X.K →+* HahnSeries ℚ Ω).injective` to reduce the goal to its premises. Use extensionality with `r`. Express the relevant statement in the definitionally equal form `(X.exp (X.gal s X.jK)).coeff r = (X.exp X.jK).coeff r`. Rewrite using `[X.gal_exp]`. Take `⟨n, hn⟩` from `X.j_exp.2.2 r`.

Rewrite using `[hn, map_intCast]`.
-/
theorem Tower.gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s X.jK)).coeff r = (X.exp X.jK).coeff r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Rewrite using `[Set.mem_singleton_iff.mp hy]`. Conclude with `hW.2`.

Consider the case `algebraMap c => exact hW.1 c`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`.
-/
theorem Tower.adjoin_le_of_overY (X : Tower Ω ε) (W : ValuationSubring X.K) (hW : X.OverY W) :
    ∀ x ∈ Algebra.adjoin Ω {X.jK}, x ∈ W := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]; exact hW.2
  | algebraMap c => exact hW.1 c
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

/- English proof (translation)
Introduce `Ω _ _ _ ε X hε hj W hW`. Use `⟨fun g => ⟨fun c => ?_, ?_⟩, fun s => ⟨fun c => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[ValuationSubring.mem_comap]`. Express the relevant statement in the definitionally equal form `X.sl g (algebraMap Ω X.K c) ∈ W`. Rewrite using `[AlgEquiv.commutes]`.

Conclude with `hW.1 c`. Rewrite using `[ValuationSubring.mem_comap]`. Express the relevant statement in the definitionally equal form `X.sl g X.jK ∈ W`. Establish `hint` using `GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat ε X hε hj g`. Set `A` to `Algebra.adjoin Ω {X.jK}`.

Establish `hle : A.toSubring ≤ W.toSubring` using `fun x hx => X.adjoin_le_of_overY W hW x hx`. Set `ι : A →+* W` to `Subring.inclusion hle`. Set `_ : Algebra A W` to `ι.toAlgebra`. Establish `: IsScalarTower A W X.K` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Conclude with `vs_mem_of_isIntegral W (hint.tower_top)`.

Rewrite using `[ValuationSubring.mem_comap]`. Express the relevant statement in the definitionally equal form `X.gal s (algebraMap Ω X.K c) ∈ W`. Rewrite using `[X.gal_algebraMap]`. Conclude with `hW.1 (s c)`. Rewrite using `[ValuationSubring.mem_comap]`.

Express the relevant statement in the definitionally equal form `X.gal s X.jK ∈ W`. Rewrite using `[X.gal_jK]`. Conclude with `hW.2`.
-/
theorem Tower.overY_comap_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ W : ValuationSubring X.K, X.OverY W →
      (∀ g : GQ, X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) ∧
        ∀ s : Ω ≃ₐ[ℚ] Ω, X.OverY (W.comap (X.gal s).toRingHom) := by
  intro Ω _ _ _ ε X hε hj W hW
  refine ⟨fun g => ⟨fun c => ?_, ?_⟩, fun s => ⟨fun c => ?_, ?_⟩⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl g (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl g X.jK ∈ W
    have hint := GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat ε X hε hj g
    let A := Algebra.adjoin Ω {X.jK}
    have hle : A.toSubring ≤ W.toSubring := fun x hx => X.adjoin_le_of_overY W hW x hx
    let ι : A →+* W := Subring.inclusion hle
    let _ : Algebra A W := ι.toAlgebra
    have : IsScalarTower A W X.K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact vs_mem_of_isIntegral W (hint.tower_top)
  · rw [ValuationSubring.mem_comap]
    change X.gal s (algebraMap Ω X.K c) ∈ W
    rw [X.gal_algebraMap]; exact hW.1 (s c)
  · rw [ValuationSubring.mem_comap]
    change X.gal s X.jK ∈ W
    rw [X.gal_jK]; exact hW.2

end GlobalTheory.KZ
