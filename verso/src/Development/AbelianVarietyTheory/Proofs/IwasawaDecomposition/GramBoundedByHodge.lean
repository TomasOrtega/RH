import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegLogCoordLeRadiusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordBoundLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogChartLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnLogChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormPositiveLogChartStatement

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShFam.MuLoc

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_sum, star_smul, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]`. Simplify using `only [dotProduct, mulVec, of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul, smul_eq_mul, RCLike.star_def]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_hermForm {g m : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin m → Fin g → ℂ) (v : Fin m → ℂ) :
    star v ⬝ᵥ (Matrix.of fun b b' => ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (W b') (W b)) *ᵥ v =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (∑ b, v b • W b) (∑ b, v b • W b) := by
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_sum, star_smul, mulVec_sum, mulVec_smul, dotProduct_sum,
    dotProduct_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  simp only [dotProduct, mulVec, of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul, smul_eq_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  ring

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D A N j S κ s x σ hσ y₀`. Establish `h1 : 1 ≤ S.Dw.p + S.Dw.q` using `by have := S.two_le; have := S.p_eq; have := S.rank_eq; omega`. Take `⟨n, gg, r, a, ch, ex, lam, ρ, hy₀, h0, hL⟩` from `GlobalTheory.T.exists_exponential_chart_at_point _ _ _ _ _ _ _ _ _ s.T σ hσ h1 y₀`. Take `⟨Ur, hUr, Cr, hCr, hr⟩` from `GlobalTheory.T.neg_log_coord_le_radius D A N j S κ s x σ n a ch hL.1.2.2.1 hL.2.1 y₀ hy₀`. Take `⟨Uh, hUh, Ch, hCh, hh⟩` from `GlobalTheory.T.exp_coord_bound_local D A N j S κ s x σ n gg ch ex hL.1 y₀ hy₀`.

Take `⟨M, hM⟩` from `GlobalTheory.T.log_chart_linear_independent D A N j S κ s x σ hσ n gg r a ch ex lam ρ hL`. Establish `hhol` using `GlobalTheory.T.differentiableOn_log_chart D A N j S κ s σ n gg r a ch ex lam ρ hL`. Set `Hm : (Fin n → ℂ) → Matrix (Fin gg) (Fin gg) ℂ` to `fun t => if ht : t ∈ logDom n a then (hM t ht).2.2.choose else 0`. Establish `hHm : ∀ t (ht : t ∈ logDom n a), Hm t = (hM t ht).2.2.choose` using `fun t ht => dif_pos ht`. Take `⟨Ca, ka, hCa, han⟩` from `GlobalTheory.T.hermitian_form_positive_log_chart n a gg r lam ρ M Hm hhol (fun t ht => by`.

Establish `hs` using `(hM t ht).2.2.choose_spec`. Rewrite using `[hHm t ht]`. Conclude with `⟨(hM t ht).1, (hM t ht).2.1, hs.1, hs.2.1, hs.2.2.1, (hL.2.2.2.1 t ht).2.2⟩) hL.2.2.2.2`. Use `set K : ℝ := Cr + Real.pi + 2 with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`.

Establish `hU : Ur ∩ Uh ∩ (ch.source ∩ ch ⁻¹' Metric.ball 0 (1 / 2)) ∈ 𝓝 y₀` using `Filter.inter_mem (Filter.inter_mem hUr hUh) (Filter.inter_mem (ch.open_source.mem_nhds hy₀) (ch.continuousAt hy₀ (by rw [h0]; exact Metric.ball_mem_nhds _ (by norm_num))))`. Use `⟨_, hU, (Ch * Ca / Real.pi + Real.pi * Ca * Ch) * K ^ ka, ka, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨⟨hyr, hyh⟩, hys, hyb⟩ hy g τ v`. Establish `hin : Inner y` using `hy`. Establish `hnz : ∀ i : Fin n, (i : ℕ) < a → ch y i ≠ 0` using `(hL.2.1 y hys).1 hin`.

Establish `hyb' : ‖ch y‖ < 1 / 2` using `by simpa using hyb`. Establish `hci : ∀ i, ‖ch y i‖ < 1 / 2` using `fun i => lt_of_le_of_lt (norm_le_pi_norm _ i) hyb'`. Establish `hre : Real.exp 1 ≤ x.r σ y` using `x.exp_le_r σ y`. Establish `hr1 : 1 ≤ x.r σ y` using `le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hre`. Choose the witnesses or unpack the hypotheses as in `⟨t, htD, hle, him, hts, hyt⟩ : ∃ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 ∧ (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) ∧ 1 + ‖t‖ ≤ K * x.r σ y ∧ ch.symm (logExp a t) = y := by`.

Set `t : Fin n → ℂ` to `fun i => if (i : ℕ) < a then Complex.log (ch y i) else ch y i`. Establish `hexp : logExp a t = ch y` using `funext fun i => by`. Simplify using `only [logExp, t]`. Use `split_ifs with hi`. Conclude with `Complex.exp_log (hnz i hi)`.

Both sides reduce to the same expression. Establish `htn : ‖t‖ ≤ Cr * x.r σ y + Real.pi + 1`. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `only [t, if_pos hi]`.

Establish `hl : Real.log ‖ch y i‖ < 0` using `Real.log_neg (norm_pos_iff.2 (hnz i hi)) (by linarith [hci i])`. Establish `h2` using `hr y hyr hin i hi`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.log_re, Complex.log_im, abs_of_neg hl]`. Conclude with `add_le_add h2 (Complex.abs_arg_le_pi _)`.

Use `_ ≤ _ := by linarith`. Simplify using `only [t, if_neg hi]`. Use `mul_nonneg hCr (le_trans zero_le_one hr1)` as an intermediate fact. Combine the linear relations using `[hci i, Real.pi_pos]`. Use `⟨t, fun i => ?_, by rw [hexp]; exact hyb'.le, fun i hi => ?_, ?_, by rw [hexp]; exact ch.left_inv hys⟩` and prove the remaining obligations.

Distinguish the cases in `hi : (i : ℕ) < a`. Simplify using `only [t, if_pos hi, Complex.log_re]`. Conclude with `Real.log_neg (norm_pos_iff.2 (hnz i hi)) (by linarith [hci i])`. Simplify using `only [t, if_neg hi]`. Combine the linear relations using `[hci i]`.

Simplify using `only [t, if_pos hi, Complex.log_im]`. Conclude with `Complex.abs_arg_le_pi _`. Use `mul_le_mul_of_nonneg_left hr1 (by positivity : (0 : ℝ) ≤ Real.pi + 2)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Substitute `hyt` using the available equality.

Establish `hT` using `(hL.1.2.2.2.2.2 _ hys).2`. Establish `hW : ∀ z : Letter S.Dw, ∃ w, IsDerivAt0 (fun u => (ex (ch.symm (logExp a t)) u).left) w (g.v z.1 z.2)` using `fun z => (hT _ (g.tan z.1 z.2)).exists`. Use `choose W hW using hW`. Establish `hD : Dirs (Z` using `s.T.Z) ⟨ch.symm (logExp a t), g⟩ (fun u => (ex (ch.symm (logExp a t)) u).left) W := hW`. Take `⟨hq1, hq2⟩` from `hh _ hyh g W hD τ v`.

Establish `hHt` using `(hM t htD).2.2.choose_spec`. Establish `hg` using `hHt.2.2.2 g W hD τ`. Rewrite `hg`, `hHt` using `[← hHm t htD]`. Use `set u : Fin gg → ℂ := ∑ b, v b • W ⟨τ, b⟩ with hu`. Establish `hq : (star v ⬝ᵥ (x.hodge σ).gram _ g τ *ᵥ v).re = Real.pi * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) u u).re`.

Rewrite using `[hg, Matrix.smul_mulVec, dotProduct_smul, quad_hermForm (W := fun b => W ⟨τ, b⟩), smul_eq_mul, Complex.re_ofReal_mul]`. Establish `hH0 : 0 ≤ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) u u).re`. Distinguish the cases in `h : u = 0`. Simplify using `[h, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]`. Conclude with `(hHt.2.1 u h).le`.

Establish `hh0 : 0 ≤ (star v ⬝ᵥ x.gram _ g τ *ᵥ v).re` using `(x.gram_posDef g τ).posSemidef.re_dotProduct_nonneg v`. Take `⟨hA1, hA2⟩` from `han t htD hle him u`. Establish `hPQ : (1 + ‖t‖) ^ ka ≤ K ^ ka * x.r σ (ch.symm (logExp a t)) ^ ka`. Rewrite using `[← mul_pow]; exact pow_le_pow_left₀ (by positivity) hts ka`. Use `set H := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) u u).re`.

Use `set h₀ := (star v ⬝ᵥ x.gram _ g τ *ᵥ v).re`. Use `set R := x.r σ (ch.symm (logExp a t)) ^ ka`. Establish `hR : 0 ≤ R` using `by positivity`. Establish `hpi` using `Real.pi_pos`. Rewrite using `[hq]`.

Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hodge_comparison_near : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ∃ U ∈ 𝓝 y₀, ∃ (C : ℝ) (k : ℕ), ∀ y ∈ U, ¬ LiesIn y (genBd s.T.Z) → ∀ (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ), (star v ⬝ᵥ x.gram y g τ *ᵥ v).re ≤ C * x.r σ y ^ k * (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ∧ (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ≤ C * x.r σ y ^ k * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re := by
  intro D A N j S κ s x σ hσ y₀
  have h1 : 1 ≤ S.Dw.p + S.Dw.q := by have := S.two_le; have := S.p_eq; have := S.rank_eq; omega
  obtain ⟨n, gg, r, a, ch, ex, lam, ρ, hy₀, h0, hL⟩ := GlobalTheory.T.exists_exponential_chart_at_point _ _ _ _ _ _ _ _ _ s.T σ hσ h1 y₀
  obtain ⟨Ur, hUr, Cr, hCr, hr⟩ := GlobalTheory.T.neg_log_coord_le_radius D A N j S κ s x σ n a ch hL.1.2.2.1 hL.2.1 y₀ hy₀
  obtain ⟨Uh, hUh, Ch, hCh, hh⟩ := GlobalTheory.T.exp_coord_bound_local D A N j S κ s x σ n gg ch ex hL.1 y₀ hy₀
  obtain ⟨M, hM⟩ := GlobalTheory.T.log_chart_linear_independent D A N j S κ s x σ hσ n gg r a ch ex lam ρ hL
  have hhol := GlobalTheory.T.differentiableOn_log_chart D A N j S κ s σ n gg r a ch ex lam ρ hL
  classical
  let Hm : (Fin n → ℂ) → Matrix (Fin gg) (Fin gg) ℂ := fun t =>
    if ht : t ∈ logDom n a then (hM t ht).2.2.choose else 0
  have hHm : ∀ t (ht : t ∈ logDom n a), Hm t = (hM t ht).2.2.choose := fun t ht => dif_pos ht
  obtain ⟨Ca, ka, hCa, han⟩ := GlobalTheory.T.hermitian_form_positive_log_chart n a gg r lam ρ M Hm hhol (fun t ht => by
    have hs := (hM t ht).2.2.choose_spec
    rw [hHm t ht]
    exact ⟨(hM t ht).1, (hM t ht).2.1, hs.1, hs.2.1, hs.2.2.1, (hL.2.2.2.1 t ht).2.2⟩) hL.2.2.2.2
  set K : ℝ := Cr + Real.pi + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hU : Ur ∩ Uh ∩ (ch.source ∩ ch ⁻¹' Metric.ball 0 (1 / 2)) ∈ 𝓝 y₀ :=
    Filter.inter_mem (Filter.inter_mem hUr hUh) (Filter.inter_mem (ch.open_source.mem_nhds hy₀)
      (ch.continuousAt hy₀ (by rw [h0]; exact Metric.ball_mem_nhds _ (by norm_num))))
  refine ⟨_, hU, (Ch * Ca / Real.pi + Real.pi * Ca * Ch) * K ^ ka, ka, ?_⟩
  rintro y ⟨⟨hyr, hyh⟩, hys, hyb⟩ hy g τ v
  have hin : Inner y := hy
  have hnz : ∀ i : Fin n, (i : ℕ) < a → ch y i ≠ 0 := (hL.2.1 y hys).1 hin
  have hyb' : ‖ch y‖ < 1 / 2 := by simpa using hyb
  have hci : ∀ i, ‖ch y i‖ < 1 / 2 := fun i => lt_of_le_of_lt (norm_le_pi_norm _ i) hyb'
  have hre : Real.exp 1 ≤ x.r σ y := x.exp_le_r σ y
  have hr1 : 1 ≤ x.r σ y := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hre
  obtain ⟨t, htD, hle, him, hts, hyt⟩ : ∃ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 ∧
      (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) ∧ 1 + ‖t‖ ≤ K * x.r σ y ∧ ch.symm (logExp a t) = y := by
    let t : Fin n → ℂ := fun i => if (i : ℕ) < a then Complex.log (ch y i) else ch y i
    have hexp : logExp a t = ch y := funext fun i => by
      simp only [logExp, t]
      split_ifs with hi
      · exact Complex.exp_log (hnz i hi)
      · rfl
    have htn : ‖t‖ ≤ Cr * x.r σ y + Real.pi + 1 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      by_cases hi : (i : ℕ) < a
      · simp only [t, if_pos hi]
        have hl : Real.log ‖ch y i‖ < 0 := Real.log_neg (norm_pos_iff.2 (hnz i hi)) (by linarith [hci i])
        have h2 := hr y hyr hin i hi
        calc ‖Complex.log (ch y i)‖ ≤ |(Complex.log (ch y i)).re| + |(Complex.log (ch y i)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
          _ ≤ Cr * x.r σ y + Real.pi := by
              rw [Complex.log_re, Complex.log_im, abs_of_neg hl]
              exact add_le_add h2 (Complex.abs_arg_le_pi _)
          _ ≤ _ := by linarith
      · simp only [t, if_neg hi]
        have := mul_nonneg hCr (le_trans zero_le_one hr1)
        linarith [hci i, Real.pi_pos]
    refine ⟨t, fun i => ?_, by rw [hexp]; exact hyb'.le, fun i hi => ?_, ?_, by rw [hexp]; exact ch.left_inv hys⟩
    · by_cases hi : (i : ℕ) < a
      · simp only [t, if_pos hi, Complex.log_re]
        exact Real.log_neg (norm_pos_iff.2 (hnz i hi)) (by linarith [hci i])
      · simp only [t, if_neg hi]
        linarith [hci i]
    · simp only [t, if_pos hi, Complex.log_im]
      exact Complex.abs_arg_le_pi _
    · have := mul_le_mul_of_nonneg_left hr1 (by positivity : (0 : ℝ) ≤ Real.pi + 2)
      nlinarith
  subst hyt
  have hT := (hL.1.2.2.2.2.2 _ hys).2
  have hW : ∀ z : Letter S.Dw, ∃ w, IsDerivAt0 (fun u => (ex (ch.symm (logExp a t)) u).left) w (g.v z.1 z.2) :=
    fun z => (hT _ (g.tan z.1 z.2)).exists
  choose W hW using hW
  have hD : Dirs (Z := s.T.Z) ⟨ch.symm (logExp a t), g⟩ (fun u => (ex (ch.symm (logExp a t)) u).left) W := hW
  obtain ⟨hq1, hq2⟩ := hh _ hyh g W hD τ v
  have hHt := (hM t htD).2.2.choose_spec
  have hg := hHt.2.2.2 g W hD τ
  rw [← hHm t htD] at hg hHt
  set u : Fin gg → ℂ := ∑ b, v b • W ⟨τ, b⟩ with hu
  have hq : (star v ⬝ᵥ (x.hodge σ).gram _ g τ *ᵥ v).re =
      Real.pi * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) u u).re := by
    rw [hg, Matrix.smul_mulVec, dotProduct_smul, quad_hermForm (W := fun b => W ⟨τ, b⟩), smul_eq_mul,
      Complex.re_ofReal_mul]
  have hH0 : 0 ≤ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) u u).re := by
    by_cases h : u = 0
    · simp [h, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
    · exact (hHt.2.1 u h).le
  have hh0 : 0 ≤ (star v ⬝ᵥ x.gram _ g τ *ᵥ v).re := (x.gram_posDef g τ).posSemidef.re_dotProduct_nonneg v
  obtain ⟨hA1, hA2⟩ := han t htD hle him u
  have hPQ : (1 + ‖t‖) ^ ka ≤ K ^ ka * x.r σ (ch.symm (logExp a t)) ^ ka := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hts ka
  set H := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) u u).re
  set h₀ := (star v ⬝ᵥ x.gram _ g τ *ᵥ v).re
  set R := x.r σ (ch.symm (logExp a t)) ^ ka
  have hR : 0 ≤ R := by positivity
  have hpi := Real.pi_pos
  rw [hq]
  constructor
  · calc h₀ ≤ Ch * ‖u‖ ^ 2 := hq2
      _ ≤ Ch * (Ca * (1 + ‖t‖) ^ ka * H) := mul_le_mul_of_nonneg_left hA2 hCh
      _ ≤ Ch * (Ca * (K ^ ka * R) * H) := by gcongr
      _ = (Ch * Ca / Real.pi) * K ^ ka * R * (Real.pi * H) := by field_simp
      _ ≤ (Ch * Ca / Real.pi + Real.pi * Ca * Ch) * K ^ ka * R * (Real.pi * H) := by
          gcongr; nlinarith [mul_nonneg hCa hCh]
  · calc Real.pi * H ≤ Real.pi * (Ca * (1 + ‖t‖) ^ ka * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hA1 hpi.le
      _ ≤ Real.pi * (Ca * (K ^ ka * R) * (Ch * h₀)) := by gcongr
      _ = (Real.pi * Ca * Ch) * K ^ ka * R * h₀ := by ring
      _ ≤ (Ch * Ca / Real.pi + Real.pi * Ca * Ch) * K ^ ka * R * h₀ := by
          gcongr; exact le_add_of_nonneg_left (by positivity)

end GlobalTheory.ShFam.MuLoc
