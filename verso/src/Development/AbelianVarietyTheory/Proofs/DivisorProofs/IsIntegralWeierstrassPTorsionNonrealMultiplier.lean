import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTauStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionIntegralJStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.LatTorsVal

/- English proof (translation)
Establish `hom` using `GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf L c τ hτ`. Establish `tm` using `GlobalTheory.WpFam.TorsMem.main M τ`. Establish `hc : c ≠ 0` using `hτ.1`. Establish `hPz : P = c * (P / c)` using `by field_simp`. Establish `hMz : (M : ℂ) * (P / c) ∈ (tauPair τ).lattice`.

Rewrite using `[← hom.1]`. Establish `: c * ((M : ℂ) * (P / c)) = (M : ℂ) * P` using `by rw [hPz]; field_simp`. Rewrite using `[this]`. Conclude with `hP`. Take `⟨x, hx⟩` from `tm.2.2.2.2 (P / c) hMz`.

Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Use `(hom.1 _).2 hx` as an intermediate fact. Rewrite `this` using `[mul_sub, ← hPz]`. Then use the resulting hypothesis. Introduce and unpack `hPL rfl`. Apply `hPL` to reduce the goal to its premises.

Establish `h0` using `(tm.2.2.1 0).2 rfl`. Establish `: P / c ∈ (tauPair τ).lattice`. Use `add_mem hx h0` as an intermediate fact. Simplify using `using this`. Rewrite using `[hPz]`.

Conclude with `(hom.1 _).2 this`.
-/
theorem exists_tors {L : PeriodPair} {c : ℂ} {τ : ℍ} (hτ : IsTauOf L c τ) (M : ℕ) [NeZero M] (P : ℂ)
    (hP : (M : ℂ) * P ∈ L.lattice) :
    ∃ x : Fin 2 → ZMod M, P - c * tors M τ x ∈ L.lattice ∧ (P ∉ L.lattice → x ≠ 0) := by
  have hom := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf L c τ hτ
  have tm := GlobalTheory.WpFam.TorsMem.main M τ
  have hc : c ≠ 0 := hτ.1
  have hPz : P = c * (P / c) := by field_simp
  have hMz : (M : ℂ) * (P / c) ∈ (tauPair τ).lattice := by
    rw [← hom.1]
    have : c * ((M : ℂ) * (P / c)) = (M : ℂ) * P := by rw [hPz]; field_simp
    rw [this]; exact hP
  obtain ⟨x, hx⟩ := tm.2.2.2.2 (P / c) hMz
  refine ⟨x, ?_, ?_⟩
  · have := (hom.1 _).2 hx
    rwa [mul_sub, ← hPz] at this
  · rintro hPL rfl
    apply hPL
    have h0 := (tm.2.2.1 0).2 rfl
    have : P / c ∈ (tauPair τ).lattice := by
      have := add_mem hx h0
      simpa using this
    rw [hPz]; exact (hom.1 _).2 this

/- English proof (translation)
Establish `e : P = c * tors M τ x + ((⟨P - c * tors M τ x, h⟩ : L.lattice) : ℂ)` using `by simp`. Prove the components needed by the constructor for the conclusion. Rewrite using `[e, L.weierstrassP_add_coe]`. Rewrite using `[e, L.derivWeierstrassP_add_coe]`.
-/
theorem wp_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (M : ℕ) (P : ℂ) (x : Fin 2 → ZMod M)
    (h : P - c * tors M τ x ∈ L.lattice) :
    L.weierstrassP P = L.weierstrassP (c * tors M τ x) ∧
      L.derivWeierstrassP P = L.derivWeierstrassP (c * tors M τ x) := by
  have e : P = c * tors M τ x + ((⟨P - c * tors M τ x, h⟩ : L.lattice) : ℂ) := by simp
  constructor
  · rw [e, L.weierstrassP_add_coe]
  · rw [e, L.derivWeierstrassP_add_coe]

/- English proof (translation)
Introduce `L β Ω M hβ hβi hΩ hM`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Take `⟨c, τ, hτ⟩` from `latTau L`. Establish `hj` using `GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication L c τ β hτ hβ hβi`. Establish `hω` using `(GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD L c τ hτ).2 Ω hΩ`.

Establish `st` using `(GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau L c Ω τ hτ).2 M`. Use `⟨fun P hP => ?_, fun P Q hP hQ hMP hMQ => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, -⟩` from `exists_tors hτ M P hP`. Take `⟨e1, e2⟩` from `wp_eq M P x hx`. Establish `hv` using `GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j M τ _ hj hω x`.

Rewrite using `[e1, e2, mul_div_assoc, mul_div_assoc, ← (st x).1, ← (st x).2, ← mul_div_assoc, ← mul_div_assoc]`. Conclude with `hv`. Take `⟨x, hx, hx0⟩` from `exists_tors hτ M P hMP`. Take `⟨y, hy, hy0⟩` from `exists_tors hτ M Q hMQ`. Establish `hv` using `GlobalTheory.T.isIntegral_weierstrassP_torsion_difference M τ _ hj hω x y (hx0 hP) (hy0 hQ)`.

Rewrite using `[(wp_eq M P x hx).1, (wp_eq M Q y hy).1, mul_div_assoc, sub_div, ← (st x).1, ← (st y).1, ← sub_div, ← mul_div_assoc]`. Conclude with `hv`.
-/
theorem main : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  intro L β Ω M hβ hβi hΩ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication L c τ β hτ hβ hβi
  have hω := (GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD L c τ hτ).2 Ω hΩ
  have st := (GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau L c Ω τ hτ).2 M
  refine ⟨fun P hP => ?_, fun P Q hP hQ hMP hMQ => ?_⟩
  · obtain ⟨x, hx, -⟩ := exists_tors hτ M P hP
    obtain ⟨e1, e2⟩ := wp_eq M P x hx
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j M τ _ hj hω x
    rw [e1, e2, mul_div_assoc, mul_div_assoc, ← (st x).1, ← (st x).2, ← mul_div_assoc, ← mul_div_assoc]
    exact hv
  · obtain ⟨x, hx, hx0⟩ := exists_tors hτ M P hMP
    obtain ⟨y, hy, hy0⟩ := exists_tors hτ M Q hMQ
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_difference M τ _ hj hω x y (hx0 hP) (hy0 hQ)
    rw [(wp_eq M P x hx).1, (wp_eq M Q y hy).1, mul_div_assoc, sub_div, ← (st x).1, ← (st y).1, ← sub_div,
      ← mul_div_assoc]
    exact hv

end GlobalTheory.WpFam.LatTorsVal
