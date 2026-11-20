import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LinearIndependentOfDetGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FinrankOFOE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramDeterminantFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersEqInv

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical ValuativeRel

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `h0`. Establish `hc : 0 < Fintype.card D.what₂.Tau`. Rewrite using `[D.what₂.card_Tau]`. Unfold `Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n`. Check the signs of the components of the expression.

Take `⟨τ⟩` from `Fintype.card_pos_iff.mp hc`. Use `hpos τ` as an intermediate fact. Rewrite `this` using `[h0, map_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ this`.
-/
theorem gZ_ne_zero (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D)
    (hpos : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ T T' Z)) : GZ T T' Z ≠ 0 := by
  intro h0
  have hc : 0 < Fintype.card D.what₂.Tau := by
    rw [D.what₂.card_Tau]
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    positivity
  obtain ⟨τ⟩ := Fintype.card_pos_iff.mp hc
  have := hpos τ
  rw [h0, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `h1` using `(D.host.g_prime 0).pos`. Establish `h2` using `(D.host.g_prime 1).pos`. Unfold `gS`. Conclude with `(Nat.mul_pos h1 h2).ne'` after adjusting the coercions.
-/
theorem gS_ne_zero (D : Formalism.BasicNotions.D7) : ((gS D : D.host.E)) ≠ 0 := by
  have h1 := (D.host.g_prime 0).pos
  have h2 := (D.host.g_prime 1).pos
  unfold gS
  exact_mod_cast (Nat.mul_pos h1 h2).ne'

/- English proof (translation)
The claim follows from `| 0 => by simp | n + 1 => by rw [Fin.prod_univ_succ, mul_pow] have h1 : ∀ a : Fin n, c ^ (-(((n + 1 : ℕ) : ℤ) - ((a.succ : Fin (n + 1)) : ℕ))) = c ^ (-((n : ℤ) - (a : ℕ))) := by intro a congr 1 simp only [Fin.val_succ] push_cast ring simp only [h1, prod_tri hc n, Fin.val_zero] rw …`.
-/
theorem prod_tri {c : ℚ} (hc : c ≠ 0) :
    ∀ n : ℕ, (∏ a : Fin n, c ^ (-((n : ℤ) - (a : ℕ)))) ^ 2 = c ^ (-((n * (n + 1) : ℕ) : ℤ))
  | 0 => by simp
  | n + 1 => by
    rw [Fin.prod_univ_succ, mul_pow]
    have h1 : ∀ a : Fin n, c ^ (-(((n + 1 : ℕ) : ℤ) - ((a.succ : Fin (n + 1)) : ℕ))) =
        c ^ (-((n : ℤ) - (a : ℕ))) := by
      intro a
      congr 1
      simp only [Fin.val_succ]
      push_cast
      ring
    simp only [h1, prod_tri hc n, Fin.val_zero]
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hc]
    congr 1
    push_cast
    ring

/- English proof (translation)
Establish `hd : (((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ≠ 0`. Use `NumberField.discr_ne_zero D.host.F` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using `only [differentIdealPowers, Fin.snoc_castSucc, Fin.snoc_last, map_one, mul_one, map_zpow₀, absNorm_ddS]`.

Conclude with `prod_tri hd D.R.rS`.
-/
theorem prod_absNorm_differentIdealPowers (D : Formalism.BasicNotions.D7) :
    (∏ a : Fin (D.R.rS + 1), FractionalIdeal.absNorm (differentIdealPowers D a)) ^ 2 =
      (((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) := by
  have hd : (((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ≠ 0 := by
    have := NumberField.discr_ne_zero D.host.F
    positivity
  rw [Fin.prod_univ_castSucc]
  simp only [differentIdealPowers, Fin.snoc_castSucc, Fin.snoc_last, map_one, mul_one, map_zpow₀, absNorm_ddS]
  exact prod_tri hd D.R.rS

/- English proof (translation)
The claim follows from `|(Algebra.norm ℚ ((-1) ^ k * y) : ℚ)| = |(Algebra.norm ℚ y : ℚ)| := by rw [map_mul, map_pow, abs_mul, abs_pow] have h1 : |(Algebra.norm ℚ (-1 : K) : ℚ)| = 1 := by have h2 : (Algebra.norm ℚ (-1 : K)) * (Algebra.norm ℚ (-1 : K)) = 1 := by rw [← map_mul]; simp have h3 : |(Algebra.no …`.
-/
theorem abs_norm_negOnePow {K : Type} [Field K] [NumberField K] (k : ℕ) (y : K) :
    |(Algebra.norm ℚ ((-1) ^ k * y) : ℚ)| = |(Algebra.norm ℚ y : ℚ)| := by
  rw [map_mul, map_pow, abs_mul, abs_pow]
  have h1 : |(Algebra.norm ℚ (-1 : K) : ℚ)| = 1 := by
    have h2 : (Algebra.norm ℚ (-1 : K)) * (Algebra.norm ℚ (-1 : K)) = 1 := by
      rw [← map_mul]; simp
    have h3 : |(Algebra.norm ℚ (-1 : K) : ℚ)| * |(Algebra.norm ℚ (-1 : K) : ℚ)| = 1 := by
      rw [← abs_mul, h2, abs_one]
    nlinarith [abs_nonneg (Algebra.norm ℚ (-1 : K) : ℚ)]
  rw [h1, one_pow, one_mul]

/- English proof (translation)
Introduce `D u u' hc F0 what₂ hr Z F' hz hZ hpos hint`. Establish `hMM` using `hM D u u' hc F0 what₂ hr Z F' hz hZ hpos hint`. Rewrite `hint`, the goal using `[hMM]`. Take `⟨hcm, hfix, -⟩` from `field_dictionary_holds D`. Establish `hG` using `gZ_ne_zero D _ _ Z hpos`.

Establish `hg` using `gS_ne_zero D`. Establish `hdetGa` using `hΔ D (Tn u) (Tn u') (star_natCast _) (star_natCast _) Z`. Establish `hdet` using `det_gram_flagDifference F0 F' Z hZ`. Rewrite `hdet` using `[hdetGa]`. Establish `hdet0 : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det ≠ 0`.

Rewrite using `[hdet]`. Conclude with `mul_ne_zero (pow_ne_zero _ (inv_ne_zero hg)) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG)`. Establish `hstar : ∀ i, ∀ a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E), star a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E)`. Apply the tactic sequence `rintro (a | a) <;> exact stable_differentIdealPowers D a`. Establish `hne : ∀ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ≠ 0`.

Apply the tactic sequence `rintro (a | a) <;> exact differentIdealPowers_ne_zero D a`. Establish `hsq` using `hN D.host.E D.host.F (VS D).V _ (VS D).hT (UPair D F0 F') (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) hcm hfix D.sp.cm.deg2 (VS D).herm hstar hne (linearIndependent_of_det_gram _ _ hdet0) (span_flagDifferenceBasis F0 F') hdet0 hint`. Establish `hm : D.R.m = 2 * (D.R.rS + 1)`. Establish `h2` using `D.R.two_le_m`. Take `⟨a, ha⟩` from `D.R.m_even`.

Unfold `Formalism.BasicNotions.Ranks.rS`. Use linear arithmetic over natural numbers and integers. Establish `hy : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det = (-1) ^ (D.R.rS + 1) * (GZ (Tn u) (Tn u') Z / ((gS D : D.host.E) ^ D.R.m))`. Rewrite using `[hdet, hm, div_eq_mul_inv, ← inv_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hN2 : (FractionalIdeal.absNorm ((∏ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ^ 2) * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (gram (VS D).hT (flagDifferenceVectors D F0 F')).det) : ℝ) = ((((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ^ …`. Rewrite using `[map_mul, FractionalIdeal.absNorm_span_singleton, hy, abs_norm_negOnePow, map_prod, Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, map_pow]`. Rewrite using `[Finset.prod_pow, ← prod_absNorm_differentIdealPowers D]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnm0 : 0 ≤ nM D.host.F (VS D).hT (UPair D F0 F') (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D)))` using `tprod_nonneg fun _ => by positivity`. Establish `hr0 : 0 ≤ |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z`. Unfold `sqrtAbsNormOfScaledGram`. Check the signs of the components of the expression.

Use `(pow_left_inj₀ hnm0 hr0 two_ne_zero).mp ?_` and prove the remaining obligations. Rewrite using `[hsq, hN2, mul_pow]`. Unfold `sqrtAbsNormOfScaledGram`. Rewrite using `[Real.sq_sqrt (abs_nonneg _)]`. Use `congr 1`.

Establish `hcast : (((NumberField.discr D.host.F).natAbs : ℕ) : ℝ) = |(NumberField.discr D.host.F : ℝ)|`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Use `push_cast`. Rewrite using `[hcast]`. Establish `e1 : (|(NumberField.discr D.host.F : ℝ)| ^ 2) ^ (-((D.R.rS : ℤ) * (D.R.rS + 1))) = |(NumberField.discr D.host.F : ℝ)| ^ (-(2 * (D.R.rS : ℤ) * (D.R.rS + 1)))`.

Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Conclude with `Rat.cast_abs _`.
-/
theorem normMM_of (hN : NMPseudo) (hM : MMPseudo) (hΔ : DetGa) : NormMM := by
  intro D u u' hc F0 what₂ hr Z F' hz hZ hpos hint
  have hMM := hM D u u' hc F0 what₂ hr Z F' hz hZ hpos hint
  rw [hMM] at hint ⊢
  obtain ⟨hcm, hfix, -⟩ := field_dictionary_holds D
  have hG := gZ_ne_zero D _ _ Z hpos
  have hg := gS_ne_zero D
  have hdetGa := hΔ D (Tn u) (Tn u') (star_natCast _) (star_natCast _) Z
  have hdet := det_gram_flagDifference F0 F' Z hZ
  rw [hdetGa] at hdet
  have hdet0 : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hg)) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hG)
  have hstar : ∀ i, ∀ a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E),
      star a ∈ ((Sum.elim (differentIdealPowers D) (differentIdealPowers D) i : FractionalIdeal _ _) : Submodule (𝓞 D.host.E) D.host.E) := by
    rintro (a | a) <;> exact stable_differentIdealPowers D a
  have hne : ∀ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ≠ 0 := by
    rintro (a | a) <;> exact differentIdealPowers_ne_zero D a
  have hsq := hN D.host.E D.host.F (VS D).V _ (VS D).hT (UPair D F0 F') (flagDifferenceVectors D F0 F')
    (Sum.elim (differentIdealPowers D) (differentIdealPowers D)) hcm hfix D.sp.cm.deg2 (VS D).herm hstar hne
    (linearIndependent_of_det_gram _ _ hdet0) (span_flagDifferenceBasis F0 F') hdet0 hint

  have hm : D.R.m = 2 * (D.R.rS + 1) := by
    have h2 := D.R.two_le_m
    obtain ⟨a, ha⟩ := D.R.m_even
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hy : (gram (VS D).hT (flagDifferenceVectors D F0 F')).det = (-1) ^ (D.R.rS + 1) * (GZ (Tn u) (Tn u') Z / ((gS D : D.host.E) ^ D.R.m)) := by
    rw [hdet, hm, div_eq_mul_inv, ← inv_pow]
    ring
  have hN2 : (FractionalIdeal.absNorm ((∏ i, (Sum.elim (differentIdealPowers D) (differentIdealPowers D) i) ^ 2) *
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (gram (VS D).hT (flagDifferenceVectors D F0 F')).det) : ℝ) =
      ((((NumberField.discr D.host.F).natAbs : ℚ) ^ 2) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) : ℚ) ^ 2 *
        |(Algebra.norm ℚ (GZ (Tn u) (Tn u') Z / ((gS D : D.host.E) ^ D.R.m)) : ℚ)| := by
    rw [map_mul, FractionalIdeal.absNorm_span_singleton, hy, abs_norm_negOnePow, map_prod,
      Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, map_pow]
    rw [Finset.prod_pow, ← prod_absNorm_differentIdealPowers D]
    push_cast
    ring
  have hnm0 : 0 ≤ nM D.host.F (VS D).hT (UPair D F0 F') (pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))) :=
    tprod_nonneg fun _ => by positivity
  have hr0 : 0 ≤ |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) *
      sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z := by
    unfold sqrtAbsNormOfScaledGram; positivity
  refine (pow_left_inj₀ hnm0 hr0 two_ne_zero).mp ?_
  rw [hsq, hN2, mul_pow]
  unfold sqrtAbsNormOfScaledGram
  rw [Real.sq_sqrt (abs_nonneg _)]
  congr 1
  have hcast : (((NumberField.discr D.host.F).natAbs : ℕ) : ℝ) = |(NumberField.discr D.host.F : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [hcast]
  have e1 : (|(NumberField.discr D.host.F : ℝ)| ^ 2) ^ (-((D.R.rS : ℤ) * (D.R.rS + 1))) =
      |(NumberField.discr D.host.F : ℝ)| ^ (-(2 * (D.R.rS : ℤ) * (D.R.rS + 1))) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [e1]
  exact Rat.cast_abs _

/- English proof (translation)
The claim follows from `normMM_of hN mass_pseudo_basis gram_determinant_formula_alt`.
-/
theorem normMM_of_NM (hN : NMPseudo) : NormMM :=
  normMM_of hN mass_pseudo_basis gram_determinant_formula_alt

end PI.UnitaryGroupMassFormula.CntFormula.R6
