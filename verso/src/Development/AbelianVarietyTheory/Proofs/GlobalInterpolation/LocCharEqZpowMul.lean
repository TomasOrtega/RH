import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.LocCharVal

/- English proof (translation)
Establish `h1 : Formalism.L2.Col.IntAt P b` using `(GlobalTheory.CharVal.intAt_iff _).2 hb.le`. Establish `h2 : Formalism.L2.Col.IntAt P b⁻¹` using `(GlobalTheory.CharVal.intAt_iff _).2 (by rw [map_inv₀, hb]; simp)`. Establish `hb0 : b ≠ 0` using `by rintro rfl; simp at hb`. Establish `h3` using `reduction_mul h1 h2`. Rewrite `h3` using `[mul_inv_cancel₀ hb0]`.

Establish `h4 : redP P (1 : E) = 1` using `by simpa using reduction_coe P 1`. Rewrite `h3` using `[h4]`. Conclude with `IsUnit.of_mul_eq_one _ h3.symm`.
-/
theorem isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : P.valuation E b = 1) : IsUnit (redP P b) := by
  have h1 : Formalism.L2.Col.IntAt P b := (GlobalTheory.CharVal.intAt_iff _).2 hb.le
  have h2 : Formalism.L2.Col.IntAt P b⁻¹ := (GlobalTheory.CharVal.intAt_iff _).2 (by rw [map_inv₀, hb]; simp)
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have h3 := reduction_mul h1 h2
  rw [mul_inv_cancel₀ hb0] at h3
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

/- English proof (translation)
Introduce `E K _ _ _ P q cq χ a hq ha`. Establish `hv : P.valuation E a ≠ 0` using `by simpa using ha`. Establish `hex : ∃ z : ℤ, IsUnit (redP P (a / (q : E) ^ z))`. Use `⟨-WithZero.log (P.valuation E a), isUnit_redP P _ ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]`.

Simplify using `[WithZero.exp_log hv, hv]`. Establish `hu : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a))` using `Classical.epsilon_spec hex`. Establish `: Finite (𝓞 E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`. Use `⟨LocE.vP P q a, χ hu.unit, MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite _), ?_⟩` and prove the remaining obligations. Unfold `LocE.locChar LocE.unitV`.

Rewrite using `[dif_pos hu]`.
-/
theorem locChar_eq_zpow_mul : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), P.valuation E (q : E) = WithZero.exp (-1 : ℤ) → a ≠ 0 → ∃ (z : ℤ) (ζ : Kˣ), IsOfFinOrder ζ ∧ LocE.locChar q cq χ a = cq ^ z * (ζ : K) := by
  intro E K _ _ _ P q cq χ a hq ha
  have hv : P.valuation E a ≠ 0 := by simpa using ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (q : E) ^ z)) := by
    refine ⟨-WithZero.log (P.valuation E a), isUnit_redP P _ ?_⟩
    rw [map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hv, hv]
  have hu : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) := Classical.epsilon_spec hex
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨LocE.vP P q a, χ hu.unit, MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite _), ?_⟩
  unfold LocE.locChar LocE.unitV
  rw [dif_pos hu]

end GlobalTheory.LocCharVal
