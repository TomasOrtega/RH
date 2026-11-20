import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerDifferentialsFreeCoordinateFormsAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

/- English proof (translation)
Use `ContinuousLinearMap.ext fun v ↦ ?_` and prove the remaining obligations. Use `conv_lhs => rw [pi_eq_sum_univ' v]`. Simplify using `[map_sum, mul_comm]`.
-/
theorem clm_eq_sum_single_smul_proj {g : ℕ} (f : (Fin g → ℂ) →L[ℂ] ℂ) :
    f = ∑ a, f (Pi.single a 1) • (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, mul_comm]

/- English proof (translation)
Establish `hn : s ∈ 𝓝 z` using `hs.mem_nhds hz`. Establish `h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt h (fderiv ℂ h y) y` using `by filter_upwards [hn] with y hy using (hh.differentiableAt (hs.mem_nhds hy)).hasFDerivAt`. Establish `h2 : fderiv ℂ h =ᶠ[𝓝 z] fun y ↦ ∑ c, k c y • (ContinuousLinearMap.proj c : (Fin g → ℂ) →L[ℂ] ℂ)` using `by filter_upwards [hn] with y hy`. Rewrite using `[clm_eq_sum_single_smul_proj (fderiv ℂ h y)]`. Conclude with `Finset.sum_congr rfl fun c _ ↦ by rw [e c y hy]`.

Establish `h3 : DifferentiableAt ℂ (fderiv ℂ h) z`. Use `DifferentiableAt.congr_of_eventuallyEq ?_ h2` and prove the remaining obligations. Conclude with `DifferentiableAt.fun_sum fun c _ ↦ ((hk c).differentiableAt hn).smul_const _`. Establish `h4 : ∀ c v, fderiv ℂ (k c) z v = fderiv ℂ (fderiv ℂ h) z v (Pi.single c 1)`. Introduce `c v`.

Establish `h5 : k c =ᶠ[𝓝 z] fun y ↦ fderiv ℂ h y (Pi.single c 1)` using `by filter_upwards [hn] with y hy using (e c y hy).symm`. Rewrite using `[h5.fderiv_eq, fderiv_clm_apply h3 (differentiableAt_const _)]`. Simplify using the standard rewrite rules. Rewrite using `[h4, h4]`. Conclude with `second_derivative_symmetric_of_eventually h1 h3.hasFDerivAt _ _`.
-/
theorem fderiv_partial_symm {g : ℕ} {s : Set (Fin g → ℂ)} (hs : IsOpen s) {h : (Fin g → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h s) {k : Fin g → (Fin g → ℂ) → ℂ} (hk : ∀ a, DifferentiableOn ℂ (k a) s)
    (e : ∀ a, ∀ z ∈ s, fderiv ℂ h z (Pi.single a 1) = k a z) (a b : Fin g) {z : Fin g → ℂ} (hz : z ∈ s) :
    fderiv ℂ (k b) z (Pi.single a 1) = fderiv ℂ (k a) z (Pi.single b 1) := by
  have hn : s ∈ 𝓝 z := hs.mem_nhds hz
  have h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt h (fderiv ℂ h y) y := by
    filter_upwards [hn] with y hy using (hh.differentiableAt (hs.mem_nhds hy)).hasFDerivAt
  have h2 : fderiv ℂ h =ᶠ[𝓝 z]
      fun y ↦ ∑ c, k c y • (ContinuousLinearMap.proj c : (Fin g → ℂ) →L[ℂ] ℂ) := by
    filter_upwards [hn] with y hy
    rw [clm_eq_sum_single_smul_proj (fderiv ℂ h y)]
    exact Finset.sum_congr rfl fun c _ ↦ by rw [e c y hy]
  have h3 : DifferentiableAt ℂ (fderiv ℂ h) z := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h2
    exact DifferentiableAt.fun_sum fun c _ ↦ ((hk c).differentiableAt hn).smul_const _
  have h4 : ∀ c v, fderiv ℂ (k c) z v = fderiv ℂ (fderiv ℂ h) z v (Pi.single c 1) := by
    intro c v
    have h5 : k c =ᶠ[𝓝 z] fun y ↦ fderiv ℂ h y (Pi.single c 1) := by
      filter_upwards [hn] with y hy using (e c y hy).symm
    rw [h5.fderiv_eq, fderiv_clm_apply h3 (differentiableAt_const _)]
    simp
  rw [h4, h4]
  exact second_derivative_symmetric_of_eventually h1 h3.hasFDerivAt _ _

/- English proof (translation)
Take `⟨hop, hdiff, -, -, -, -, -, -, -, halg, -, -⟩` from `GlobalTheory.T.uniformisation_preimage_value_rules A g L u`. Take `⟨d, ω, hcomm, hd, hdual, hspan, hev⟩` from `GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian A g L u hA U`. Use `choose k₀ hk₀ using hr`. Set `k : Fin g → Sec (str A) U.1` to `k₀`. Establish `hk : ∀ a, ∀ z ∈ pre u.ex U.1, fderiv ℂ h z (Pi.single a 1) = val u.ex U.1 (k a) z` using `hk₀`.

Use `⟨∑ a, k a • ω a, GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame _ g d ω hcomm hdual hspan k fun a b ↦ ?_, fun z hz ↦ ?_⟩` and prove the remaining obligations. Establish `h0 : d a (k b) - d b (k a) = 0`. Use `GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U.1 _ fun z hz ↦ ?_` and prove the remaining obligations. Take `⟨e, he⟩` from `halg U.1 z hz`. Establish `h1` using `he (d a (k b) - d b (k a))`.

Rewrite `h1` using `[map_sub, ← he (d a (k b)), ← he (d b (k a)), hd a _ z hz, hd b _ z hz, fderiv_partial_symm (hop U.1) hh (fun c ↦ hdiff U.1 (k c)) hk a b hz, sub_self]`. Conclude with `h1`. Conclude with `sub_eq_zero.mp h0`. Rewrite using `[clm_eq_sum_single_smul_proj (fderiv ℂ h z), clm_eq_sum_single_smul_proj (evForm u.ex U.1 z _)]`. Use `Finset.sum_congr rfl fun a _ ↦ ?_` and prove the remaining obligations.

Establish `h1 : (d a).liftKaehlerDifferential (∑ c, k c • ω c) = k a`. Simplify using `[map_sum, hdual]`. Rewrite using `[hev a _ z hz, h1, hk a z hz]`.
-/
theorem exists_closed_form_fderiv_eq (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g)
    (hA : IsAbelianScheme A) (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ) (hh : DifferentiableOn ℂ h (pre u.ex U.1))
    (hr : ∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) :
    ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  obtain ⟨hop, hdiff, -, -, -, -, -, -, -, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨d, ω, hcomm, hd, hdual, hspan, hev⟩ := GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian A g L u hA U
  choose k₀ hk₀ using hr
  let k : Fin g → Sec (str A) U.1 := k₀
  have hk : ∀ a, ∀ z ∈ pre u.ex U.1, fderiv ℂ h z (Pi.single a 1) = val u.ex U.1 (k a) z := hk₀
  refine ⟨∑ a, k a • ω a, GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame _ g d ω hcomm hdual hspan k fun a b ↦ ?_, fun z hz ↦ ?_⟩
  · have h0 : d a (k b) - d b (k a) = 0 := by
      refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U.1 _ fun z hz ↦ ?_
      obtain ⟨e, he⟩ := halg U.1 z hz
      have h1 := he (d a (k b) - d b (k a))
      rw [map_sub, ← he (d a (k b)), ← he (d b (k a)), hd a _ z hz, hd b _ z hz,
        fderiv_partial_symm (hop U.1) hh (fun c ↦ hdiff U.1 (k c)) hk a b hz, sub_self] at h1
      exact h1
    exact sub_eq_zero.mp h0
  · rw [clm_eq_sum_single_smul_proj (fderiv ℂ h z), clm_eq_sum_single_smul_proj (evForm u.ex U.1 z _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have h1 : (d a).liftKaehlerDifferential (∑ c, k c • ω c) = k a := by
      simp [map_sum, hdual]
    rw [hev a _ z hz, h1, hk a z hz]

end GlobalTheory.CechPer
