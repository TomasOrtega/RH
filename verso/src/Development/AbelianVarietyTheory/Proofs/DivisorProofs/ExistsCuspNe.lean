import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivCoreUpPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralPotentialWeightChartLtTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerDifferentiableOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerRmulBorelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricScalarPoincareWeightEqTwoMulPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormScalarPoincareDetRatioLactLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfOrthonormalConjBlockUpperTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeTsumPowNeZeroOfSingleUnitStatement
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ScalarPoin
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Unfold `qS`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Establish `hu : IsUnit (mat x0 τ).det` using `isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)`. Rewrite using `[KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl_one]`. Establish `h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ).toBlocks₂₂ = 1`.

Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₂, Matrix.one_apply]`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
theorem qS_base (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) : qS X x0 k x0 = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl_one]
  have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ).toBlocks₂₂ = 1 := by
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [h1]
  simp

end GlobalTheory.ScalarPoin

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory GlobalTheory.ScalarPoin in
/- English proof (translation)
Introduce `E _ _ _ r X hp0 hpr hχ y hy N`. Take `⟨x0, ho, b, hb, rfl⟩` from `ortho_holds r X y hy`. Establish `hPD` using `GlobalTheory.ClosedDiscontinuity.propDisc_closed r X`. Establish `hx0 : x0 ∈ X.dom` using `KU.orth_dom X ho`. Use `set bb : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hbbdef`.

Establish `hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb` using `by linarith`. Take `⟨s0, hs0⟩` from `GlobalTheory.T.lintegral_potentialWeight_chart_lt_top E r X x0 ho`. Take `⟨k0, hk0⟩` from `exists_nat_ge ((s0 + bb) / 2)`. Establish `hla : ∀ k : ℕ, (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then (((2 * k) / 2 : ℕ) : ℤ) else -(((2 * k) / 2 : ℕ) : ℤ)) = laS X k`. Introduce `k`.

Use function extensionality and compare the values at `τ j`. Simplify using `[laS]`. Establish `hχk : ∀ k : ℕ, ∀ γ ∈ X.Γ, X.χ (laS X k) γ = 1`. Introduce `k γ hγ`. Use `hχ (2 * k) (even_two_mul k) γ hγ` as an intermediate fact.

Rewrite `this` using `[hla k]`. Then use the resulting hypothesis. Establish `hIn : ∀ k : ℕ, k0 ≤ k → InAt X x0 (fun x => ENNReal.ofReal (Real.exp (-phla X (laS X k) x))) bb (fun _ => (1 : ℂ))`. Introduce `k hk`. Establish `hs : s0 ≤ 2 * (k : ℝ) - bb`. Establish `: ((s0 + bb) / 2 : ℝ) ≤ k` using `le_trans hk0 (by exact_mod_cast hk)`.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `InAt`. Use `lt_of_le_of_lt (le_of_eq ?_) (hs0 _ hs)` and prove the remaining obligations. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0)] with z hz`.

Rewrite using `[GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential E r X x0 ho k z hz]`. Simplify using `only [norm_one, one_pow, kaF]`. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Rewrite using `[one_div, ← Real.exp_neg, ← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpo` using `fun k (hk : k0 ≤ k) => poin_holds r X x0 ho hPD (laS X k) _ bb (DivUpPf.metricW_exp X _) (DivUpPf.wLower_exp X _) hbb (fun _ => (1 : ℂ)) (qS X x0 k) (differentiableOn_const _) (hIn k hk) ⟨GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn E r X x0 ho k, fun x _ b hb => G …`. Use `set a : X.Γ → ℂ := fun γ => qS X x0 1 (lact γ.1 x0) with ha`. Establish `ha1 : a 1 = 1`.

Simplify using `only [ha, OneMemClass.coe_one, KU.lact_one]`. Conclude with `qS_base X ho 1`. Establish `hterm : ∀ k (γ : X.Γ), (X.χ (laS X k) γ.1)⁻¹ * qS X x0 k (lact γ.1 x0) = a γ ^ k`. Introduce `k γ`. Rewrite using `[hχk k γ.1 γ.2, inv_one, one_mul, qS_pow]`.

Establish `hsum : Summable fun γ : X.Γ => ‖a γ‖ ^ k0`. Establish `h` using `(hpo k0 le_rfl).1 x0 hx0`. Rewrite `h` using `[hterm k0, norm_pow]`. Conclude with `h`. Establish `hle : ∀ γ : X.Γ, ‖a γ‖ ≤ 1` using `fun γ => (GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).1`.

Establish `hlt : ∀ γ : X.Γ, γ ≠ 1 → ‖a γ‖ < 1`. Introduce `γ hne`. Use `lt_of_le_of_ne (hle γ) fun heq => hne (Subtype.ext ?_)` and prove the remaining obligations. Conclude with `GlobalTheory.T.eq_one_of_orthonormal_conj_block_upper_triangular E r X x0 ho γ.1 γ.2 ((GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).2 heq)`. Take `⟨k, hk, hne⟩` from `GlobalTheory.T.exists_ge_tsum_pow_ne_zero_of_single_unit a 1 k0 ha1 hle hlt hsum (max N (k0 + 1))`.

Establish `hk0k : k0 ≤ k` using `le_trans (by omega) hk`. Establish `hkpos : 0 < k` using `lt_of_lt_of_le (by omega) hk`. Choose the witnesses or unpack the hypotheses as in `⟨τ0⟩ : Nonempty X.Ψ := by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Distinguish the cases in `hτ : τ ∈ X.Ψ`.

Conclude with `⟨⟨τ, hτ⟩⟩`. Conclude with `⟨⟨_, not_not.mp ((X.cmType τ).not.mp hτ)⟩⟩`. Establish `hB` using `(hpo k hk0k).2.1`. Use `⟨2 * k, le_trans (le_max_left _ _) (le_trans hk (by omega)), by omega, even_two_mul k, ?_⟩` and prove the remaining obligations. Rewrite using `[hla k]`.

Use `⟨poin X (laS X k) (qS X x0 k), ?_, ?_⟩` and prove the remaining obligations. Use `cuspStatement_holds r X (laS X k) τ0 hp0 hpr (fun i j hij hjp => ?_) (fun i0 i1 h0 h1 => ?_) _ hB` and prove the remaining obligations. Apply the tactic sequence `simp only [laS] split_ifs with h1 h2 <;> omega`. Simplify using `only [laS]`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hB.1.2.1 x0 hx0 b hb]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Unfold `bchar`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (FrameDegreeData.bdiag_ne X hb τ i)`.

Unfold `poin`. Repeatedly rewrite using `[hterm k]`. Conclude with `hne`.
-/
theorem GlobalTheory.ScalarPoin.exists_cusp_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ y ∈ X.dom, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ y hy N
  obtain ⟨x0, ho, b, hb, rfl⟩ := ortho_holds r X y hy
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hx0 : x0 ∈ X.dom := KU.orth_dom X ho
  set bb : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hbbdef
  have hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb := by linarith
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.lintegral_potentialWeight_chart_lt_top E r X x0 ho
  obtain ⟨k0, hk0⟩ := exists_nat_ge ((s0 + bb) / 2)
  have hla : ∀ k : ℕ, (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then (((2 * k) / 2 : ℕ) : ℤ)
      else -(((2 * k) / 2 : ℕ) : ℤ)) = laS X k := by
    intro k; funext τ j; simp [laS]
  have hχk : ∀ k : ℕ, ∀ γ ∈ X.Γ, X.χ (laS X k) γ = 1 := by
    intro k γ hγ
    have := hχ (2 * k) (even_two_mul k) γ hγ
    rwa [hla k] at this
  have hIn : ∀ k : ℕ, k0 ≤ k →
      InAt X x0 (fun x => ENNReal.ofReal (Real.exp (-phla X (laS X k) x))) bb (fun _ => (1 : ℂ)) := by
    intro k hk
    have hs : s0 ≤ 2 * (k : ℝ) - bb := by
      have : ((s0 + bb) / 2 : ℝ) ≤ k := le_trans hk0 (by exact_mod_cast hk)
      linarith
    unfold InAt
    refine lt_of_le_of_lt (le_of_eq ?_) (hs0 _ hs)
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0)] with z hz
    rw [GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential E r X x0 ho k z hz]
    simp only [norm_one, one_pow, kaF]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  have hpo := fun k (hk : k0 ≤ k) => poin_holds r X x0 ho hPD (laS X k) _ bb (DivUpPf.metricW_exp X _)
    (DivUpPf.wLower_exp X _) hbb (fun _ => (1 : ℂ)) (qS X x0 k) (differentiableOn_const _) (hIn k hk)
    ⟨GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn E r X x0 ho k, fun x _ b hb => GlobalTheory.T.scalarPoincareDetRatioPower_rmul_borel E r X x0 k x b hb⟩ (fun z _ => qS_cpt X ho k z)
  set a : X.Γ → ℂ := fun γ => qS X x0 1 (lact γ.1 x0) with ha
  have ha1 : a 1 = 1 := by
    simp only [ha, OneMemClass.coe_one, KU.lact_one]
    exact qS_base X ho 1
  have hterm : ∀ k (γ : X.Γ), (X.χ (laS X k) γ.1)⁻¹ * qS X x0 k (lact γ.1 x0) = a γ ^ k := by
    intro k γ
    rw [hχk k γ.1 γ.2, inv_one, one_mul, qS_pow]
  have hsum : Summable fun γ : X.Γ => ‖a γ‖ ^ k0 := by
    have h := (hpo k0 le_rfl).1 x0 hx0
    simp_rw [hterm k0, norm_pow] at h
    exact h
  have hle : ∀ γ : X.Γ, ‖a γ‖ ≤ 1 := fun γ => (GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).1
  have hlt : ∀ γ : X.Γ, γ ≠ 1 → ‖a γ‖ < 1 := by
    intro γ hne
    refine lt_of_le_of_ne (hle γ) fun heq => hne (Subtype.ext ?_)
    exact GlobalTheory.T.eq_one_of_orthonormal_conj_block_upper_triangular E r X x0 ho γ.1 γ.2 ((GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one E r X x0 ho γ.1 γ.2).2 heq)
  obtain ⟨k, hk, hne⟩ := GlobalTheory.T.exists_ge_tsum_pow_ne_zero_of_single_unit a 1 k0 ha1 hle hlt hsum (max N (k0 + 1))
  have hk0k : k0 ≤ k := le_trans (by omega) hk
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  obtain ⟨τ0⟩ : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hτ : τ ∈ X.Ψ
    · exact ⟨⟨τ, hτ⟩⟩
    · exact ⟨⟨_, not_not.mp ((X.cmType τ).not.mp hτ)⟩⟩
  have hB := (hpo k hk0k).2.1
  refine ⟨2 * k, le_trans (le_max_left _ _) (le_trans hk (by omega)), by omega, even_two_mul k, ?_⟩
  rw [hla k]
  refine ⟨poin X (laS X k) (qS X x0 k), ?_, ?_⟩
  · refine cuspStatement_holds r X (laS X k) τ0 hp0 hpr (fun i j hij hjp => ?_) (fun i0 i1 h0 h1 => ?_) _ hB
    · simp only [laS]
      split_ifs with h1 h2 <;> omega
    · simp only [laS]
      rw [if_neg (by omega), if_pos (by omega)]
      omega
  · rw [hB.1.2.1 x0 hx0 b hb]
    refine mul_ne_zero ?_ ?_
    · unfold bchar
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
        zpow_ne_zero _ (FrameDegreeData.bdiag_ne X hb τ i)
    · unfold poin
      simp_rw [hterm k]
      exact hne
