import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormExistsBelowFrameBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBoundedOnFrames
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThinBerg

open MeasureTheory
open scoped ENNReal

/- English proof (translation)
Establish `hd : ∀ τ i, dmin X.Gm x τ i ≠ 0` using `fun τ i h => by`. Use `(hx τ).2 i` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`. Unfold `Data.pnorm`.

Conclude with `mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)`.
-/
theorem pnorm_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

/- English proof (translation)
Use `set A : ℝ≥0∞ := ENNReal.ofReal (ptN (modelWt U G) P ⟨y.1, y.2.1⟩) with hA`. Establish `hA0 : A ≠ 0` using `by rw [hA]; exact (ENNReal.ofReal_pos.2 hy).ne'`. Establish `hsup : supE U.X (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A`. Unfold `supE`. Use `iSup_le fun z => ?_` and prove the remaining obligations.

Rewrite using `[hA, ← ENNReal.ofReal_mul (inv_nonneg.2 he.le)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `h` using `hb z`. Rewrite using `[le_inv_mul_iff₀ he]`. Conclude with `h`.

Establish `hpet : petE V dict (muOn U V dict Z) (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A` using `(petE_le_supE V dict _ (muPart_univ_le V dict _) hd _ P).trans hsup`. Unfold `bergOn bergE`. Use `le_trans ?_ (le_iSup₂_of_le P hP le_rfl)` and prove the remaining obligations. Rewrite using `[ENNReal.le_div_iff_mul_le (Or.inr (pow_ne_zero 2 hA0)) (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_pow, ← mul_assoc, ENNReal.ofReal_mul (sq_nonneg e), ENNReal.ofReal_pow (inv_nonneg.2 he.le)]`. Use `_ = A ^ 2 := by`. Rewrite using `[← mul_pow, mul_inv_cancel₀ he.ne', one_pow, ENNReal.ofReal_one, one_mul]`.
-/
theorem le_bergOn_of_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (hd : ∀ g, (dict g).2 ∈ (U.X (dict g).1).dom)
    (Z : Comp Xo c) (G : WTZ E) (y : FPt U.X) (P : FDSec U.X) (hP : P ∈ holSub U.X (modelWt U G)) {e : ℝ}
    (he : 0 < e) (hy : 0 < ptN (modelWt U G) P ⟨y.1, y.2.1⟩)
    (hb : ∀ z : FPt U.X, e * ptN (modelWt U G) P ⟨z.1, z.2.1⟩ ≤ ptN (modelWt U G) P ⟨y.1, y.2.1⟩) :
    ENNReal.ofReal (e ^ 2) ≤ bergOn U V dict Z G y := by
  set A : ℝ≥0∞ := ENNReal.ofReal (ptN (modelWt U G) P ⟨y.1, y.2.1⟩) with hA
  have hA0 : A ≠ 0 := by rw [hA]; exact (ENNReal.ofReal_pos.2 hy).ne'
  have hsup : supE U.X (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A := by
    unfold supE
    refine iSup_le fun z => ?_
    rw [hA, ← ENNReal.ofReal_mul (inv_nonneg.2 he.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hb z
    rw [le_inv_mul_iff₀ he]
    exact h
  have hpet : petE V dict (muOn U V dict Z) (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A :=
    (petE_le_supE V dict _ (muPart_univ_le V dict _) hd _ P).trans hsup
  unfold bergOn bergE
  refine le_trans ?_ (le_iSup₂_of_le P hP le_rfl)
  rw [ENNReal.le_div_iff_mul_le (Or.inr (pow_ne_zero 2 hA0)) (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  calc ENNReal.ofReal (e ^ 2) * petE V dict (muOn U V dict Z) (modelWt U G) P ^ 2
      ≤ ENNReal.ofReal (e ^ 2) * (ENNReal.ofReal e⁻¹ * A) ^ 2 := by gcongr
    _ = ENNReal.ofReal (e ^ 2 * e⁻¹ ^ 2) * A ^ 2 := by
        rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (sq_nonneg e), ENNReal.ofReal_pow (inv_nonneg.2 he.le)]
    _ = A ^ 2 := by
        rw [← mul_pow, mul_inv_cancel₀ he.ne', one_pow, ENNReal.ofReal_one, one_mul]

end GlobalTheory.ThinBerg

namespace GlobalTheory.ThinBerg

open MeasureTheory

/- English proof (translation)
Introduce `h1 h2 h3 h4 h5`. Establish `hT` using `GlobalTheory.T.cusp_form_exists_below_frame_bound h1 h2 h3 h4 h5`. Establish `hW` using `GlobalTheory.T.cusp_form_bounded_on_frames h1 h2 h3 h4 h5`. Unfold `Covers Lifts at hT hW ⊢`. Use `Closed.imp (Closed.and hT hW) ?_` and prove the remaining obligations.

Introduce and unpack `eps Fm CH - ⟨⟨C1, hC1, a1, H1⟩, ⟨C2, hC2, a2, H2⟩⟩`. Use `⟨C1, hC1, max a1 a2, fun x hx hle ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hfy, hfb⟩` from `H1 x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth`. Take `⟨g, hg, K, hK, hgK⟩` from `H2 x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ f hf`. Take `⟨th, hr, -, hDU⟩` from `hY.1.dictU σ hσ`.

Establish `hd` using `Formalism.L2.Pj.dict_dom_of hDU`. Use `clear H1 H2`. Establish `he : ∀ φ : ℝ, Real.exp (-(φ / 625)) = Real.exp (-(φ / 1250)) ^ 2` using `fun φ => by`. Rewrite using `[sq, ← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Establish `hgW : g ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (dat p i) u1 0)` using `cuspOn_le _ _ _ hg`. Establish `hgS : g ∈ suppOn Z` using `(Submodule.mem_inf.1 hg).2`. Establish `hP` using `(mem_cuspW.1 hgW).2 σ hσ`.

Establish `hfy' : 0 < ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩` using `pnorm_pos' _ _ y.2.2 hfy`. Establish `hgy : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨y.1, y.2.1⟩ = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩` using `hgK _ hyZ`. Use `le_bergOn_of_ratio (Y.U σ) _ (Y.dict σ) hd Z _ y _ hP (Real.exp_pos _) ?_ ?_` and prove the remaining obligations. Rewrite using `[hgy]`. Conclude with `mul_pos hK hfy'`.

Introduce `z`. Distinguish the cases in `hz : (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z`. Rewrite using `[hgK _ hz, hgy]`. Use `hfb z hz` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `h0 : rdU (Y.U σ) g z.1 z.2.1 = 0` using `rdU_eq_zero (Y.U σ) hgS hz`. Establish `hz0 : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨z.1, z.2.1⟩ = 0`. Simplify using `only [ptN, Data.pnorm, h0, norm_zero, zero_mul]`. Rewrite using `[hz0, mul_zero]`. Conclude with `ptN_nonneg _ _ _`.
-/
theorem thin_bergOn : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ENNReal.ofReal (Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 625))) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro h1 h2 h3 h4 h5
  have hT := GlobalTheory.T.cusp_form_exists_below_frame_bound h1 h2 h3 h4 h5
  have hW := GlobalTheory.T.cusp_form_bounded_on_frames h1 h2 h3 h4 h5
  unfold Covers Lifts at hT hW ⊢
  refine Closed.imp (Closed.and hT hW) ?_
  rintro eps Fm CH - ⟨⟨C1, hC1, a1, H1⟩, ⟨C2, hC2, a2, H2⟩⟩
  refine ⟨C1, hC1, max a1 a2, fun x hx hle ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth => ?_⟩
  obtain ⟨f, hf, hfy, hfb⟩ := H1 x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ hth
  obtain ⟨g, hg, K, hK, hgK⟩ := H2 x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY u1 hu Z σ hσ y hyZ f hf
  obtain ⟨th, hr, -, hDU⟩ := hY.1.dictU σ hσ
  have hd := Formalism.L2.Pj.dict_dom_of hDU
  clear H1 H2
  have he : ∀ φ : ℝ, Real.exp (-(φ / 625)) = Real.exp (-(φ / 1250)) ^ 2 := fun φ => by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [he]
  have hgW : g ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (dat p i) u1 0) := cuspOn_le _ _ _ hg
  have hgS : g ∈ suppOn Z := (Submodule.mem_inf.1 hg).2
  have hP := (mem_cuspW.1 hgW).2 σ hσ
  have hfy' : 0 < ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ :=
    pnorm_pos' _ _ y.2.2 hfy
  have hgy : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨y.1, y.2.1⟩ =
      K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ := hgK _ hyZ
  refine le_bergOn_of_ratio (Y.U σ) _ (Y.dict σ) hd Z _ y _ hP (Real.exp_pos _) ?_ ?_
  · rw [hgy]; exact mul_pos hK hfy'
  · intro z
    by_cases hz : (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z
    · rw [hgK _ hz, hgy]
      have := hfb z hz
      nlinarith
    · have h0 : rdU (Y.U σ) g z.1 z.2.1 = 0 := rdU_eq_zero (Y.U σ) hgS hz
      have hz0 : ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) ⟨z.1, z.2.1⟩ = 0 := by
        simp only [ptN, Data.pnorm, h0, norm_zero, zero_mul]
      rw [hz0, mul_zero]
      exact ptN_nonneg _ _ _

end GlobalTheory.ThinBerg
