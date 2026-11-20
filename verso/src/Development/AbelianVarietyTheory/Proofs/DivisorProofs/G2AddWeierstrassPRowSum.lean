import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre

noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Establish `h` using `(L.hasSum_weierstrassPExcept 0 z).summable`. Use `(h.add (summable_of_ne_finset_zero (s := {0}) (f := fun l : L.lattice => if (l : ℂ) = 0 then 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 else 0) ?_)).congr ?_` and prove the remaining obligations. Introduce `l hl`. Simplify using `only [Finset.mem_singleton] at hl`. Simplify using `[hl]`.

Introduce `l`. Apply the tactic sequence `by_cases hl : (l : ℂ) = 0 <;> simp [hl]`.
-/
private lemma summable_weierstrassP_terms (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 := by
  have h := (L.hasSum_weierstrassPExcept 0 z).summable
  refine (h.add (summable_of_ne_finset_zero (s := {0})
    (f := fun l : L.lattice => if (l : ℂ) = 0 then 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 else 0)
    ?_)).congr ?_
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro l
    by_cases hl : (l : ℂ) = 0 <;> simp [hl]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Simplify using `[PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply, Finsupp.sum_fintype, PeriodPair.latticeBasis]`.
-/
private lemma latticeEquivProd_symm_coe (L : PeriodPair) (p : ℤ × ℤ) :
    (L.latticeEquivProd.symm p : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ := by
  simp [PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    PeriodPair.latticeBasis]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

/- English proof (translation)
Use `set L := _root_.GlobalTheory.QFam.tauPair τ with hLdef`. Establish `hω₁ : L.ω₁ = τ` using `rfl`. Establish `hω₂ : L.ω₂ = 1` using `rfl`. Use `set f : ℤ × ℤ → ℂ := fun p => 1 / (z - (p.1 * τ + p.2)) ^ 2 - 1 / ((p.1 : ℂ) * τ + p.2) ^ 2 with hfdef`. Establish `hg : HasSum (fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2) (L.weierstrassP z)` using `(summable_weierstrassP_terms L z).hasSum`.

Establish `hf : HasSum f (L.weierstrassP z)`. Use `(L.latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hg` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, LinearEquiv.coe_toEquiv, latticeEquivProd_symm_coe, hω₁, hω₂, hfdef, mul_one]`.

Establish `hrow : HasSum (fun n : ℤ => ∑' m : ℤ, f (n, m)) (L.weierstrassP z)` using `hf.prod_fiberwise fun n => (hf.summable.prod_factor n).hasSum`. Establish `hG : HasSum (fun n : ℤ => EisensteinSeries.e2Summand n τ) (EisensteinSeries.G2 τ)`. Rewrite using `[← _root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.tsum_e2Summand τ]`. Conclude with `(_root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand τ).hasSum`. Establish `hsum` using `hG.add hrow`.

Establish `hF : HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z - (n * τ + m)) ^ 2) (EisensteinSeries.G2 τ + L.weierstrassP z)`. Use `hsum using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Establish `ha : Summable fun m : ℤ => 1 / ((n : ℂ) * τ + m) ^ 2`. Use `EisensteinSeries.linear_right_summable (τ : ℂ) n (k := 2) le_rfl` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Simplify using `[zpow_ofNat]`. Establish `hba : Summable fun m : ℤ => f (n, m)` using `hf.summable.prod_factor n`. Establish `he : EisensteinSeries.e2Summand n τ = ∑' m : ℤ, 1 / ((n : ℂ) * τ + m) ^ 2`.

Unfold `EisensteinSeries.e2Summand`. Use `congr 1`. Use function extensionality and compare the values at `m`. Simplify using `[EisensteinSeries.eisSummand]`. Rewrite using `[he]`.

Use `(ha.hasSum.add hba.hasSum).tsum_eq` as an intermediate fact. Simplify using `only [hfdef, add_sub_cancel] at this`. Conclude with `this`. Establish `hneg` using `(Equiv.neg ℤ).hasSum_iff.mpr hF`. Use `hneg using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `n`. Simplify using `only [Function.comp_apply, Equiv.neg_apply]`. Rewrite using `[← (Equiv.neg ℤ).tsum_eq]`. Use `congr 1`. Use function extensionality and compare the values at `m`.

Simplify using `only [Equiv.neg_apply, Int.cast_neg]`. Put the polynomial expressions in normal form.
-/
lemma _root_.GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * τ + m) ^ 2)
      (EisensteinSeries.G2 τ + (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP z) := by
  set L := _root_.GlobalTheory.QFam.tauPair τ with hLdef
  have hω₁ : L.ω₁ = τ := rfl
  have hω₂ : L.ω₂ = 1 := rfl
  set f : ℤ × ℤ → ℂ := fun p => 1 / (z - (p.1 * τ + p.2)) ^ 2 - 1 / ((p.1 : ℂ) * τ + p.2) ^ 2
    with hfdef
  have hg : HasSum (fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2) (L.weierstrassP z) :=
    (summable_weierstrassP_terms L z).hasSum
  have hf : HasSum f (L.weierstrassP z) := by
    have := (L.latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hg
    convert this using 1
    funext p
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, latticeEquivProd_symm_coe, hω₁, hω₂,
      hfdef, mul_one]
  have hrow : HasSum (fun n : ℤ => ∑' m : ℤ, f (n, m)) (L.weierstrassP z) :=
    hf.prod_fiberwise fun n => (hf.summable.prod_factor n).hasSum
  have hG : HasSum (fun n : ℤ => EisensteinSeries.e2Summand n τ) (EisensteinSeries.G2 τ) := by
    rw [← _root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.tsum_e2Summand τ]
    exact (_root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand τ).hasSum
  have hsum := hG.add hrow
  have hF : HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z - (n * τ + m)) ^ 2)
      (EisensteinSeries.G2 τ + L.weierstrassP z) := by
    convert hsum using 1
    funext n
    have ha : Summable fun m : ℤ => 1 / ((n : ℂ) * τ + m) ^ 2 := by
      have := EisensteinSeries.linear_right_summable (τ : ℂ) n (k := 2) le_rfl
      convert this using 1
      funext m
      simp [zpow_ofNat]
    have hba : Summable fun m : ℤ => f (n, m) := hf.summable.prod_factor n
    have he : EisensteinSeries.e2Summand n τ = ∑' m : ℤ, 1 / ((n : ℂ) * τ + m) ^ 2 := by
      unfold EisensteinSeries.e2Summand
      congr 1
      funext m
      simp [EisensteinSeries.eisSummand]
    rw [he]
    have := (ha.hasSum.add hba.hasSum).tsum_eq
    simp only [hfdef, add_sub_cancel] at this
    exact this
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hF
  convert hneg using 1
  funext n
  simp only [Function.comp_apply, Equiv.neg_apply]
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext m
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring_nf

end GlobalTheory.WpFam
