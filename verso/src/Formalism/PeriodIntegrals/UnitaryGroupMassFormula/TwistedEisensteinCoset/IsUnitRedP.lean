import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IntegralApproximationByInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Use `haveI := P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Establish `hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0` using `fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Establish `hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧ Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r` using `⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by field_simp⟩`. Unfold `redP`.

Rewrite using `[dif_pos hex]`. Take `⟨r', s', hs', h', hc'⟩` from `hex.choose_spec`. Establish `hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0` using `fun h0 => hs' (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Establish `hE : algebraMap (𝓞 E) E (s' * r) = algebraMap (𝓞 E) E (s * r')`. Rewrite using `[map_mul, map_mul, ← h, ← h']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hO : s' * r = s * r'` using `FaithfulSMul.algebraMap_injective (𝓞 E) E hE`. Establish `hQ : Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r = Ideal.Quotient.mk P.asIdeal s * Ideal.Quotient.mk P.asIdeal r'`. Rewrite using `[← map_mul, ← map_mul, hO]`. Apply `mul_left_cancel₀ hs'0` to reduce the goal to its premises.

Rewrite using `[hQ, ← hc']`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mk_mul_reduction_eq_mk {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    redP P a * Ideal.Quotient.mk P.asIdeal s = Ideal.Quotient.mk P.asIdeal r := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      field_simp⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc'⟩ := hex.choose_spec
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 :=
    fun h0 => hs' (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hE : algebraMap (𝓞 E) E (s' * r) = algebraMap (𝓞 E) E (s * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have hO : s' * r = s * r' := FaithfulSMul.algebraMap_injective (𝓞 E) E hE
  have hQ : Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r =
      Ideal.Quotient.mk P.asIdeal s * Ideal.Quotient.mk P.asIdeal r' := by
    rw [← map_mul, ← map_mul, hO]
  apply mul_left_cancel₀ hs'0
  rw [hQ, ← hc']
  ring

/- English proof (translation)
Use `haveI := P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Take `⟨r, s, hs, h⟩` from `ha`. Take `⟨r', s', hs', h'⟩` from `hb`. Establish `hss : s * s' ∉ P.asIdeal` using `fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'`.

Establish `hab : algebraMap (𝓞 E) E (s * s') * (a * b) = algebraMap (𝓞 E) E (r * r')`. Rewrite using `[map_mul, map_mul, ← h, ← h']`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `mk_mul_reduction_eq_mk P hss hab`. Establish `ha'` using `mk_mul_reduction_eq_mk P hs h`.

Establish `hb'` using `mk_mul_reduction_eq_mk P hs' h'`. Establish `hss0 : Ideal.Quotient.mk P.asIdeal (s * s') ≠ 0` using `fun h0 => hss (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Apply `mul_right_cancel₀ hss0` to reduce the goal to its premises. Rewrite using `[h1, map_mul, map_mul, ← ha', ← hb']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reduction_mul' {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a * b) = redP P a * redP P b := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have hab : algebraMap (𝓞 E) E (s * s') * (a * b) = algebraMap (𝓞 E) E (r * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have h1 := mk_mul_reduction_eq_mk P hss hab
  have ha' := mk_mul_reduction_eq_mk P hs h
  have hb' := mk_mul_reduction_eq_mk P hs' h'
  have hss0 : Ideal.Quotient.mk P.asIdeal (s * s') ≠ 0 :=
    fun h0 => hss (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  apply mul_right_cancel₀ hss0
  rw [h1, map_mul, map_mul, ← ha', ← hb']
  ring

/- English proof (translation)
Establish `h1 : (1 : 𝓞 E) ∉ P.asIdeal` using `fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `h` using `mk_mul_reduction_eq_mk P (a := 1) (r := 1) h1 (by simp)`. Simplify using `using h`.
-/
theorem reduction_one' : redP P (1 : E) = 1 := by
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have h := mk_mul_reduction_eq_mk P (a := 1) (r := 1) h1 (by simp)
  simpa using h

/- English proof (translation)
Take `⟨hw0, hi, hi'⟩` from `hw`. Establish `h` using `reduction_mul' P hi hi'`. Rewrite `h` using `[mul_inv_cancel₀ hw0, reduction_one']`. Conclude with `IsUnit.of_mul_eq_one (b := redP P w⁻¹) h.symm`.
-/
theorem isUnit_redP {w : E} (hw : UnitAt P w) : IsUnit (redP P w) := by
  obtain ⟨hw0, hi, hi'⟩ := hw
  have h := reduction_mul' P hi hi'
  rw [mul_inv_cancel₀ hw0, reduction_one'] at h
  exact IsUnit.of_mul_eq_one (b := redP P w⁻¹) h.symm

end Red

/- English proof (translation)
Introduce `E K _ _ _ _ P hp hq cq χ hcq a ha`. Take `⟨e, w, hae, hw0, hw1, hw2⟩` from `hN.2.2.1 E P hp hq a ha`. Establish `hex : ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z))`. Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `: a / (qOf P : E) ^ e = w`.

Rewrite using `[hae]`. Clear denominators, using `[zpow_ne_zero e (qE_ne P hp)]` for the nonvanishing conditions. Rewrite using `[this]`. Conclude with `isUnit_redP P ⟨hw0, hw1, hw2⟩`. Establish `hspec : IsUnit (redP P (a / (qOf P : E) ^ vP P (qOf P) a))` using `Classical.epsilon_spec hex`.

Unfold `locChar`. Use `mul_ne_zero (zpow_ne_zero _ hcq) ?_` and prove the remaining obligations. Unfold `unitV`. Rewrite using `[dif_pos hspec]`. Conclude with `Units.ne_zero _`.
-/
theorem muNe_of (hN : NTAll) : MuNeP := by
  intro E K _ _ _ _ P hp hq cq χ hcq a ha
  obtain ⟨e, w, hae, hw0, hw1, hw2⟩ := hN.2.2.1 E P hp hq a ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z)) := by
    refine ⟨e, ?_⟩
    have : a / (qOf P : E) ^ e = w := by
      rw [hae]
      field_simp [zpow_ne_zero e (qE_ne P hp)]
    rw [this]
    exact isUnit_redP P ⟨hw0, hw1, hw2⟩
  have hspec : IsUnit (redP P (a / (qOf P : E) ^ vP P (qOf P) a)) := Classical.epsilon_spec hex
  unfold locChar
  refine mul_ne_zero (zpow_ne_zero _ hcq) ?_
  unfold unitV
  rw [dif_pos hspec]
  exact Units.ne_zero _

/- English proof (translation)
Introduce `E K _ _ _ _ P hp hq sq cq hsq hcq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 g₀ h ρ κ hκ`. Take `⟨lam, hlam, hlaw⟩` from `hJ E K P hp hq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 κ hκ`. Establish `hdet : ∀ f : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det f : E) ≠ 0` using `fun f => hM E K P hp hq cq ξ⁻¹ hcq _ (Units.ne_zero _)`. Use `⟨(locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det (ρ * h * κ) : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det (ρ * h * κ) : E) * ((n' + c' : ℕ) : ℤ)) * lam / ((locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det h : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ))), ?_, fun x …` and prove the remaining obligations. Use `hdet (ρ * h * κ)` as an intermediate fact.

Use `hdet h` as an intermediate fact. Use `div_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq)) hlam) (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq))` and prove the remaining obligations. Establish `ey : (ρ * h * κ).symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap = κ.symm.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ ((ρ⁻¹).toLinearMap ∘ₗ x) ∘ₗ g₀.toLinearMap)`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use `show _ = ρ (h (κ (κ.symm _)))`. Rewrite using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Use `show _ = (ρ * ρ⁻¹) _`.

Rewrite using `[mul_inv_cancel]`. Both sides reduce to the same expression. Unfold `om`. Rewrite using `[ey, hlaw]`. Establish `a1` using `hdet (ρ * h * κ)`.

Establish `a0` using `hdet h`. Establish `s0 : sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ)) ≠ 0` using `zpow_ne_zero _ hsq`. Clear the denominators using the available nonvanishing facts.
-/
theorem omStep_of (hJ : JLawP) (hM : MuNeP) : OmStepP := by
  intro E K _ _ _ _ P hp hq sq cq hsq hcq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 g₀ h ρ κ hκ
  obtain ⟨lam, hlam, hlaw⟩ := hJ E K P hp hq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 κ hκ
  have hdet : ∀ f : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det f : E) ≠ 0 :=
    fun f => hM E K P hp hq cq ξ⁻¹ hcq _ (Units.ne_zero _)
  refine ⟨(locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det (ρ * h * κ) : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det (ρ * h * κ) : E) * ((n' + c' : ℕ) : ℤ)) * lam /
      ((locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det h : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ))), ?_, fun x => ?_⟩
  · have := hdet (ρ * h * κ)
    have := hdet h
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq)) hlam)
      (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq))
  · have ey : (ρ * h * κ).symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap =
        κ.symm.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ ((ρ⁻¹).toLinearMap ∘ₗ x) ∘ₗ g₀.toLinearMap) := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_eq]
      show _ = ρ (h (κ (κ.symm _)))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      show _ = (ρ * ρ⁻¹) _
      rw [mul_inv_cancel]
      rfl
    unfold om
    rw [ey, hlaw]
    have a1 := hdet (ρ * h * κ)
    have a0 := hdet h
    have s0 : sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ hsq
    field_simp

end PI.TwistedEisensteinNonvanishing.W
