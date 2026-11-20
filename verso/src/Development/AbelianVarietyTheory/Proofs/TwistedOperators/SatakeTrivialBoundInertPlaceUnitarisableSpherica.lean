import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeTrivialBoundOfBoundedZonalSphericalUnitaryStatement

noncomputable section

namespace GlobalTheory.SatBoundInert

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

/- English proof (translation)
Establish `hnn : ∀ z, 0 ≤ (B z z).re` using `fun z => by`. Distinguish the cases in `hz : z = 0`. Simplify using `[hz]`. Conclude with `(hpos z hz).le`. Distinguish the cases in `h0 : B u v = 0`.

Rewrite using `[h0, norm_zero]`. Conclude with `hnn v`. Establish `hn : (‖B u v‖ : ℂ) ≠ 0` using `by exact_mod_cast (norm_ne_zero_iff.2 h0)`. Establish `hz` using `hnn (u - (B u v / (‖B u v‖ : ℂ)) • v)`. Establish `e : B (u - (B u v / (‖B u v‖ : ℂ)) • v) (u - (B u v / (‖B u v‖ : ℂ)) • v) = B u u - starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v - (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) + (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B v v`.

Simplify using `only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]`. Rewrite using `[hsym u v]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v = ‖B u v‖`. Rewrite using `[map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq]`.

Clear the denominators using the available nonvanishing facts. Establish `h2 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) = ‖B u v‖`. Rewrite using `[div_mul_eq_mul_div, Complex.mul_conj', sq]`. Clear the denominators using the available nonvanishing facts. Establish `h3 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) = 1`.

Rewrite using `[map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', sq]`. Clear the denominators using the available nonvanishing facts. Rewrite `hz` using `[e, h1, h2, h3, h]`. Simplify using `only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, one_mul] at hz`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_form_le {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hpos : ∀ v, v ≠ 0 → 0 < (B v v).re) (u v : V)
    (h : B u u = B v v) : ‖B u v‖ ≤ (B v v).re := by
  have hnn : ∀ z, 0 ≤ (B z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hpos z hz).le
  by_cases h0 : B u v = 0
  · rw [h0, norm_zero]; exact hnn v
  have hn : (‖B u v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h0)
  have hz := hnn (u - (B u v / (‖B u v‖ : ℂ)) • v)
  have e : B (u - (B u v / (‖B u v‖ : ℂ)) • v) (u - (B u v / (‖B u v‖ : ℂ)) • v) =
      B u u - starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v - (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) +
        (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B v v := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
    rw [hsym u v]
    ring
  have h1 : starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v = ‖B u v‖ := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq]
    field_simp
  have h2 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) = ‖B u v‖ := by
    rw [div_mul_eq_mul_div, Complex.mul_conj', sq]
    field_simp
  have h3 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) = 1 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', sq]
    field_simp
  rw [e, h1, h2, h3, h] at hz
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, one_mul] at hz
  linarith

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n hU V _ _ π α _ hun hsat`. Take `⟨B, hsym, hpos, hinv⟩` from `hun`. Take `⟨x, hx⟩` from `hsat.exists_vec`. Establish `hxx : B x x ≠ 0` using `fun h => by`. Use `hpos x hx.1` as an intermediate fact.

Rewrite `this` using `[h]`. Simplify using `at this`. Set `c : ℂ` to `(B x x)⁻¹`. Set `l : V →ₗ[ℂ] ℂ` to `{ toFun := fun y => B y x * c map_add' := fun a b => by simp [add_mul] map_smul' := fun a y => by simp [mul_assoc] }`. Establish `hl : ∀ k ∈ KU σ n, ∀ y, l (π k y) = l y` using `fun k hk y => by show B (π k y) x * c = B y x * c conv_lhs => rw [← GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk]`.

Rewrite using `[hinv]`. Establish `h1 : l x = 1` using `mul_inv_cancel₀ hxx`. Establish `hz` using `GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.isZonal_of_isSatVecU hU hx l hl h1`. Establish `hϖ : ϖ ≠ 0`. Introduce `h`.

Use `hU.2.2.2.1` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe this`. Use `GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary GlobalTheory.InertZeta.unramDoublingInert L (Units.mk0 ϖ hϖ) σ q n hU α _ hz ⟨(B x x).re * ‖c‖, fun g => ?_⟩` and prove the remaining obligations. Use `show ‖B (π g x) x * c‖ ≤ _`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (norm_form_le B hsym hpos _ _ (hinv g x x)) (norm_nonneg _)`.
-/
theorem satakeBoundInert : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  intro L _ _ _ ϖ σ q n hU V _ _ π α _ hun hsat
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  obtain ⟨x, hx⟩ := hsat.exists_vec
  have hxx : B x x ≠ 0 := fun h => by
    have := hpos x hx.1
    rw [h] at this
    simp at this
  let c : ℂ := (B x x)⁻¹
  let l : V →ₗ[ℂ] ℂ :=
    { toFun := fun y => B y x * c
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun a y => by simp [mul_assoc] }
  have hl : ∀ k ∈ KU σ n, ∀ y, l (π k y) = l y := fun k hk y => by
    show B (π k y) x * c = B y x * c
    conv_lhs => rw [← GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk]
    rw [hinv]
  have h1 : l x = 1 := mul_inv_cancel₀ hxx
  have hz := GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.isZonal_of_isSatVecU hU hx l hl h1
  have hϖ : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  refine GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary GlobalTheory.InertZeta.unramDoublingInert L (Units.mk0 ϖ hϖ) σ q n hU α _ hz ⟨(B x x).re * ‖c‖, fun g => ?_⟩
  show ‖B (π g x) x * c‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_form_le B hsym hpos _ _ (hinv g x x)) (norm_nonneg _)

end GlobalTheory.SatBoundInert

end
