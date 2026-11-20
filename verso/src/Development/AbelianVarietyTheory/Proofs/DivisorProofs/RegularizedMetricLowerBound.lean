import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviNonnegOfIsPshExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSmoothCurv
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.FlagPoly

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RegCurvAlg

/- English proof (translation)
Simplify using `only [thW, mul_neg, Finset.sum_neg_distrib, neg_inj]`. Use `conv_lhs => enter [2, z]`. Rewrite using `[← sum_coef_fund u z.1 z.2]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem thW_eq_sum {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ)
    (u : D.what₂.Tau → Fin O.N → ℝ) (ch : AlgChart (O.var c).str σ (O.var c).dim) (y : Pts (O.var c) σ)
    (ξ : Fin (O.var c).dim → ℂ) :
    thW (refMet x O.Φ) c σ u ch y ξ = ∑ τ, ∑ i, coef u τ i * thW (refMet x O.Φ) c σ (fund τ i) ch y ξ := by
  simp only [thW, mul_neg, Finset.sum_neg_distrib, neg_inj]
  conv_lhs => enter [2, z]; rw [← sum_coef_fund u z.1 z.2]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Introduce `hH hC D O x P hcore hN hex`. Take `⟨CH, tH, hCH, htH, hHess⟩` from `hH D O x P hcore hN hex`. Establish `hCent` using `hC D O x P hcore hN hex`. Use `⟨2 * CH * ((Fintype.card D.what₂.Tau : ℝ) * O.N), min tH (Real.exp (-1)), by positivity, lt_min htH (Real.exp_pos _), ?_⟩` and prove the remaining obligations. Introduce `t ht htt c σ u hu ch y hy ξ`.

Establish `htH' : t ≤ tH` using `htt.trans (min_le_left _ _)`. Establish `hte : t ≤ Real.exp (-1)` using `htt.trans (min_le_right _ _)`. Establish `hL : 1 ≤ Real.log (1 / t)`. Establish `h1 : Real.log t ≤ -1`. Use `Real.log_le_log ht hte` as an intermediate fact.

Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis. Rewrite using `[one_div, Real.log_inv]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set q := Real.log (Real.log (1 / t)) / Real.log (1 / t) with hq`. Establish `hq0 : 0 ≤ q` using `div_nonneg (Real.log_nonneg hL) (by linarith)`.

Establish `hom : 0 ≤ P.om c σ ch y ξ` using `GlobalTheory.RegularisationModel.kaehler_nonneg (P.om_kaehler c σ) ch hy ξ`. Establish `hcentral : ∀ τ (i : Fin O.N), ¬ ((i : ℕ) + 1 < O.N) → (i : ℕ) + 1 = O.N ∧ P.regFund c σ τ i t = extBd O.Φ (psi O x c σ τ i)`. Introduce `τ i hi`. Use `⟨by have := i.2; omega, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Simplify using `[PolDat.regFund, hi, HeightParts.psi]`. Establish `hsm : ∀ τ (i : Fin O.N), ContDiffAt ℝ 2 (P.regFund c σ τ i t ∘ ch.e.symm) (ch.e y)`. Introduce `τ i`. Distinguish the cases in `hi : (i : ℕ) + 1 < O.N`. Conclude with `(hHess t ht htH' c σ τ i hi).1.contDiffAt_two isOpen_univ hy trivial`.

Take `⟨hi', e⟩` from `hcentral τ i hi`. Rewrite using `[e]`. Conclude with `(hCent c σ τ i hi').1.contDiffAt_two isOpen_univ hy trivial`. Establish `hddc : ddcForm (P.reg c σ u t) ch y ξ = ∑ τ, ∑ i, coef u τ i * ddcForm (P.regFund c σ τ i t) ch y ξ`. Establish `e1 : ch.levi (P.reg c σ u t) y ξ = ∑ τ, ∑ i, coef u τ i * ch.levi (P.regFund c σ τ i t) y ξ` using `by show ch.levi (fun z => ∑ τ, ∑ i, coef u τ i * P.regFund c σ τ i t z) y ξ = _`.

Establish `hs1 : ∀ τ (i : Fin O.N), ContDiffAt ℝ 2 ((fun z => coef u τ i * P.regFund c σ τ i t z) ∘ ch.e.symm) (ch.e y)` using `fun τ i => contDiffAt_const.mul (hsm τ i)`. Rewrite using `[GlobalTheory.ShFam.CombCurv.levi_sum Finset.univ (fun τ z => ∑ i, coef u τ i * P.regFund c σ τ i t z) (fun τ => by`. Use `ContDiffAt.sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hs1 τ i` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Simplify using `[Function.comp_def]) ξ]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.ShFam.CombCurv.levi_sum Finset.univ (fun i z => coef u τ i * P.regFund c σ τ i t z) (hs1 τ) ξ]`. Conclude with `Finset.sum_congr rfl fun i _ => AlgChart.levi_const_mul _ (hsm τ i) ξ`. Simplify using `only [ddcForm, e1, Finset.sum_div, mul_div_assoc]`.

Establish `hterm : ∀ τ (i : Fin O.N), -(2 * CH * ‖u‖ * q * P.om c σ ch y ξ) ≤ coef u τ i * (thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (P.regFund c σ τ i t) ch y ξ)`. Introduce `τ i`. Establish `hA : 0 ≤ CH * q * P.om c σ ch y ξ` using `by positivity`. Establish `hu0 : 0 ≤ ‖u‖` using `norm_nonneg _`. Distinguish the cases in `hi : (i : ℕ) + 1 < O.N`.

Establish `h1` using `(hHess t ht htH' c σ τ i hi).2 ch y hy ξ`. Establish `hc0 : 0 ≤ coef u τ i` using `coef_nonneg (fun τ a b hab => hu τ a b hab) τ hi`. Establish `hc1 : coef u τ i ≤ 2 * ‖u‖`. Rewrite using `[ShFam.coef, dif_pos hi]`. Establish `ha` using `(norm_le_pi_norm (u τ) i).trans (norm_le_pi_norm u τ)`.

Establish `hb` using `(norm_le_pi_norm (u τ) ⟨i + 1, hi⟩).trans (norm_le_pi_norm u τ)`. Rewrite `ha`, `hb` using `[Real.norm_eq_abs]`. Combine the linear relations using `[le_abs_self (u τ i), neg_abs_le (u τ ⟨i + 1, hi⟩)]`. Use polynomial arithmetic with `[mul_nonneg hc0 (neg_le_iff_add_nonneg.1 h1), mul_nonneg (sub_nonneg.2 hc1) hA]`. Take `⟨hi', e⟩` from `hcentral τ i hi`.

Rewrite using `[e, (hCent c σ τ i hi').2 ch y hy ξ, mul_zero, neg_nonpos]`. Check the signs of the components of the expression. Rewrite using `[thW_eq_sum, hddc, ← Finset.sum_add_distrib]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ τ, ∑ i, coef u τ i * (thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (P.regFund c σ τ i t) ch y ξ) := Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hterm τ i`. Use `_ = _ := by`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_add _ _ _`.
-/
theorem curv_lower : HessSt → CentSt → OnCore fun D O x P => ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
    ∀ c σ (u : D.what₂.Tau → Fin O.N → ℝ), Dom u → ∀ ch : AlgChart (O.var c).str σ (O.var c).dim, ∀ y ∈ ch.e.source, ∀ ξ,
      -(C * ‖u‖ * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) * P.om c σ ch y ξ) ≤
        thW (refMet x O.Φ) c σ u ch y ξ + ddcForm (P.reg c σ u t) ch y ξ := by
  intro hH hC D O x P hcore hN hex
  obtain ⟨CH, tH, hCH, htH, hHess⟩ := hH D O x P hcore hN hex
  have hCent := hC D O x P hcore hN hex
  refine ⟨2 * CH * ((Fintype.card D.what₂.Tau : ℝ) * O.N), min tH (Real.exp (-1)), by positivity,
    lt_min htH (Real.exp_pos _), ?_⟩
  intro t ht htt c σ u hu ch y hy ξ
  have htH' : t ≤ tH := htt.trans (min_le_left _ _)
  have hte : t ≤ Real.exp (-1) := htt.trans (min_le_right _ _)
  have hL : 1 ≤ Real.log (1 / t) := by
    have h1 : Real.log t ≤ -1 := by
      have := Real.log_le_log ht hte
      rwa [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  set q := Real.log (Real.log (1 / t)) / Real.log (1 / t) with hq
  have hq0 : 0 ≤ q := div_nonneg (Real.log_nonneg hL) (by linarith)
  have hom : 0 ≤ P.om c σ ch y ξ := GlobalTheory.RegularisationModel.kaehler_nonneg (P.om_kaehler c σ) ch hy ξ
  have hcentral : ∀ τ (i : Fin O.N), ¬ ((i : ℕ) + 1 < O.N) →
      (i : ℕ) + 1 = O.N ∧ P.regFund c σ τ i t = extBd O.Φ (psi O x c σ τ i) := by
    intro τ i hi
    refine ⟨by have := i.2; omega, ?_⟩
    funext z
    simp [PolDat.regFund, hi, HeightParts.psi]
  have hsm : ∀ τ (i : Fin O.N), ContDiffAt ℝ 2 (P.regFund c σ τ i t ∘ ch.e.symm) (ch.e y) := by
    intro τ i
    by_cases hi : (i : ℕ) + 1 < O.N
    · exact (hHess t ht htH' c σ τ i hi).1.contDiffAt_two isOpen_univ hy trivial
    · obtain ⟨hi', e⟩ := hcentral τ i hi
      rw [e]
      exact (hCent c σ τ i hi').1.contDiffAt_two isOpen_univ hy trivial
  have hddc : ddcForm (P.reg c σ u t) ch y ξ =
      ∑ τ, ∑ i, coef u τ i * ddcForm (P.regFund c σ τ i t) ch y ξ := by
    have e1 : ch.levi (P.reg c σ u t) y ξ = ∑ τ, ∑ i, coef u τ i * ch.levi (P.regFund c σ τ i t) y ξ := by
      show ch.levi (fun z => ∑ τ, ∑ i, coef u τ i * P.regFund c σ τ i t z) y ξ = _
      have hs1 : ∀ τ (i : Fin O.N), ContDiffAt ℝ 2 ((fun z => coef u τ i * P.regFund c σ τ i t z) ∘ ch.e.symm) (ch.e y) :=
        fun τ i => contDiffAt_const.mul (hsm τ i)
      rw [GlobalTheory.ShFam.CombCurv.levi_sum Finset.univ (fun τ z => ∑ i, coef u τ i * P.regFund c σ τ i t z)
        (fun τ => by
          have := ContDiffAt.sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hs1 τ i
          convert this using 1
          funext z
          simp [Function.comp_def]) ξ]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [GlobalTheory.ShFam.CombCurv.levi_sum Finset.univ (fun i z => coef u τ i * P.regFund c σ τ i t z) (hs1 τ) ξ]
      exact Finset.sum_congr rfl fun i _ => AlgChart.levi_const_mul _ (hsm τ i) ξ
    simp only [ddcForm, e1, Finset.sum_div, mul_div_assoc]
  have hterm : ∀ τ (i : Fin O.N), -(2 * CH * ‖u‖ * q * P.om c σ ch y ξ) ≤
      coef u τ i * (thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (P.regFund c σ τ i t) ch y ξ) := by
    intro τ i
    have hA : 0 ≤ CH * q * P.om c σ ch y ξ := by positivity
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    by_cases hi : (i : ℕ) + 1 < O.N
    · have h1 := (hHess t ht htH' c σ τ i hi).2 ch y hy ξ
      have hc0 : 0 ≤ coef u τ i := coef_nonneg (fun τ a b hab => hu τ a b hab) τ hi
      have hc1 : coef u τ i ≤ 2 * ‖u‖ := by
        rw [ShFam.coef, dif_pos hi]
        have ha := (norm_le_pi_norm (u τ) i).trans (norm_le_pi_norm u τ)
        have hb := (norm_le_pi_norm (u τ) ⟨i + 1, hi⟩).trans (norm_le_pi_norm u τ)
        rw [Real.norm_eq_abs] at ha hb
        linarith [le_abs_self (u τ i), neg_abs_le (u τ ⟨i + 1, hi⟩)]
      nlinarith [mul_nonneg hc0 (neg_le_iff_add_nonneg.1 h1), mul_nonneg (sub_nonneg.2 hc1) hA]
    · obtain ⟨hi', e⟩ := hcentral τ i hi
      rw [e, (hCent c σ τ i hi').2 ch y hy ξ, mul_zero, neg_nonpos]
      positivity
  rw [thW_eq_sum, hddc, ← Finset.sum_add_distrib]
  calc -(2 * CH * ((Fintype.card D.what₂.Tau : ℝ) * O.N) * ‖u‖ * q * P.om c σ ch y ξ)
        = ∑ τ : D.what₂.Tau, ∑ i : Fin O.N, -(2 * CH * ‖u‖ * q * P.om c σ ch y ξ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    _ ≤ ∑ τ, ∑ i, coef u τ i * (thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (P.regFund c σ τ i t) ch y ξ) :=
          Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hterm τ i
    _ = _ := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => mul_add _ _ _

end GlobalTheory.RegCurvAlg

end
