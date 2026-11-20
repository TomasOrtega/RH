import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PlaneIdealTwoOne
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetFormComparison

/- English proof (translation)
Unfold `hessC`. Rewrite using `[(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]`.
-/
theorem hessC_congr {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    hessC f y = hessC g y := by
  unfold hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

/- English proof (translation)
Establish `h : (HilbertSamuel.ProjFS.logPot (N` using `N)) = fun z => Real.log (1 + euclPot z) := rfl`. Rewrite using `[h]`. Conclude with `(contDiff_const.add (contDiff_euclPot N)).log fun z => by`. Establish `: 0 ≤ euclPot z` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem contDiff_logPot (N : ℕ) : ContDiff ℝ ∞ (HilbertSamuel.ProjFS.logPot (N := N)) := by
  have h : (HilbertSamuel.ProjFS.logPot (N := N)) = fun z => Real.log (1 + euclPot z) := rfl
  rw [h]
  exact (contDiff_const.add (contDiff_euclPot N)).log fun z => by
    have : 0 ≤ euclPot z := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith

/- English proof (translation)
Use `set m : ℝ := (1 + N) ^ 2 with hm`. Establish `h1 : ContDiffAt ℝ 2 (fun w => m * HilbertSamuel.ProjFS.logPot (N` using `N) w) z := contDiffAt_const.mul (((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)`. Establish `h2 : ContDiffAt ℝ 2 (fun w => (-1 : ℝ) * euclPot w) z` using `contDiffAt_const.mul (((contDiff_euclPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)`. Establish `e : (m : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N` using `N)) z - 1 = hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z := by`. Rewrite using `[ReciprocityTheory.AnForm.M.hessC_add' _ _ z h1 h2, ReciprocityTheory.AnForm.M.hessC_const_mul', ReciprocityTheory.AnForm.M.hessC_const_mul', TubeFormComparison.hessC_euclPot]`.

Simplify using `[sub_eq_add_neg]`. Rewrite using `[e]`. Use `ReciprocityTheory.AnForm.M.hessC_posSemidef _ z (h1.add h2) fun w => ?_` and prove the remaining obligations. Establish `hq` using `ReciprocityTheory.AnForm.M.re_star_dot_hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z (star w)`. Establish `hq' : levi (fun w => m * HilbertSamuel.ProjFS.logPot (N` using `N) w + (-1 : ℝ) * euclPot w) z w = (star (star w) ⬝ᵥ (hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z *ᵥ star w)).re := by rw [hq, star_star]`.

Rewrite using `[hq', ← e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, HilbertSamuel.ProjFS.hessC_logPot_eq_chernCoeff 0, Matrix.smul_mulVec, dotProduct_smul, CP.chernCoeff_quadForm, CP.star_dotProduct_self]`. Use `set a : ℝ := ∑ j, ‖(star w) j‖ ^ 2 with ha`. Use `set q : ℝ := 1 + normSqSum z with hqdef`. Establish `hS0 : 0 ≤ normSqSum z` using `normSqSum_nonneg z`. Establish `hSN : normSqSum z ≤ N`.

Establish `: ∀ j, ‖z j‖ ^ 2 ≤ 1` using `fun j => pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm z j).trans hz)`. Combine the equalities or inequalities in the displayed calculation. Establish `hCS` using `CP.norm_dotProduct_sq_le z (star w)`. Establish `ha0 : 0 ≤ a` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `hq1 : 1 ≤ q` using `by linarith`.

Establish `hpi` using `Real.pi_pos`. Establish `hval : ((m : ℂ) • (((2 * Real.pi : ℝ) : ℂ) • ((1 / (2 * Real.pi * q) * (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) : ℝ) : ℂ)) - (a : ℂ)).re = m * (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) / q - a`. Simplify using `only [smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hval]`.

Rewrite `hCS` using `[← ha]`. Establish `hd : q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 ≤ (1 - q⁻¹) * a`. Rewrite using `[inv_mul_le_iff₀ (by linarith)]`. Establish `: q * ((1 - q⁻¹) * a) = normSqSum z * a`. Rewrite using `[hqdef]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hCS`. Establish `hqm : q ^ 2 ≤ m`.

Rewrite using `[hm]`. Establish `: q ≤ 1 + N` using `by linarith`. Conclude with `pow_le_pow_left₀ (by linarith) this 2`. Establish `hqa : a / q ≤ a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2`. Establish `: a / q = q⁻¹ * a` using `by ring`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[sub_nonneg, le_div_iff₀ (by linarith)]`. Establish `h4 : q ^ 2 * (a / q) = q * a`. Clear the denominators using the available nonvanishing facts. Use polynomial arithmetic with `[h4, mul_le_mul_of_nonneg_left hqa (by positivity : (0 : ℝ) ≤ m), mul_le_mul_of_nonneg_right hqm (div_nonneg ha0 (by linarith : (0 : ℝ) ≤ q))]`.
-/
theorem posSemidef_hessC_logPot_sub {N : ℕ} {z : Fin N → ℂ} (hz : ‖z‖ ≤ 1) :
    ((((1 + N : ℝ) ^ 2 : ℝ) : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1).PosSemidef := by
  set m : ℝ := (1 + N) ^ 2 with hm
  have h1 : ContDiffAt ℝ 2 (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w) z :=
    contDiffAt_const.mul (((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have h2 : ContDiffAt ℝ 2 (fun w => (-1 : ℝ) * euclPot w) z :=
    contDiffAt_const.mul (((contDiff_euclPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have e : (m : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1 =
      hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z := by
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ z h1 h2, ReciprocityTheory.AnForm.M.hessC_const_mul',
      ReciprocityTheory.AnForm.M.hessC_const_mul', TubeFormComparison.hessC_euclPot]
    simp [sub_eq_add_neg]
  rw [e]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ z (h1.add h2) fun w => ?_
  have hq := ReciprocityTheory.AnForm.M.re_star_dot_hessC
    (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z (star w)
  have hq' : levi (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z w =
      (star (star w) ⬝ᵥ (hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z
        *ᵥ star w)).re := by rw [hq, star_star]
  rw [hq', ← e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, HilbertSamuel.ProjFS.hessC_logPot_eq_chernCoeff 0, Matrix.smul_mulVec,
    dotProduct_smul, CP.chernCoeff_quadForm, CP.star_dotProduct_self]
  set a : ℝ := ∑ j, ‖(star w) j‖ ^ 2 with ha
  set q : ℝ := 1 + normSqSum z with hqdef
  have hS0 : 0 ≤ normSqSum z := normSqSum_nonneg z
  have hSN : normSqSum z ≤ N := by
    have : ∀ j, ‖z j‖ ^ 2 ≤ 1 := fun j =>
      pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm z j).trans hz)
    calc normSqSum z = ∑ j, ‖z j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin N, (1 : ℝ) := Finset.sum_le_sum fun j _ => this j
      _ = N := by simp
  have hCS := CP.norm_dotProduct_sq_le z (star w)
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq1 : 1 ≤ q := by linarith
  have hpi := Real.pi_pos
  have hval : ((m : ℂ) • (((2 * Real.pi : ℝ) : ℂ) • ((1 / (2 * Real.pi * q) *
      (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) : ℝ) : ℂ)) - (a : ℂ)).re =
      m * (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) / q - a := by
    simp only [smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
    field_simp
  rw [hval]
  rw [← ha] at hCS
  have hd : q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 ≤ (1 - q⁻¹) * a := by
    rw [inv_mul_le_iff₀ (by linarith)]
    have : q * ((1 - q⁻¹) * a) = normSqSum z * a := by
      rw [hqdef]
      field_simp
      ring
    rw [this]
    exact hCS
  have hqm : q ^ 2 ≤ m := by
    rw [hm]
    have : q ≤ 1 + N := by linarith
    exact pow_le_pow_left₀ (by linarith) this 2
  have hqa : a / q ≤ a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 := by
    have : a / q = q⁻¹ * a := by ring
    nlinarith
  rw [sub_nonneg, le_div_iff₀ (by linarith)]
  have h4 : q ^ 2 * (a / q) = q * a := by
    field_simp
  nlinarith [h4, mul_le_mul_of_nonneg_left hqa (by positivity : (0 : ℝ) ≤ m),
    mul_le_mul_of_nonneg_right hqm (div_nonneg ha0 (by linarith : (0 : ℝ) ≤ q))]

/- English proof (translation)
Establish `hv : ContDiff ℝ ∞ (fun z : Fin N → ℂ => (Fin.insertNth i (1 : ℂ) z : Fin (N + 1) → ℂ))`. Use `contDiff_pi.2 fun b => ?_` and prove the remaining obligations. Take `rfl | ⟨j, rfl⟩` from `Fin.eq_self_or_eq_succAbove i b`. Simplify using `only [Fin.insertNth_apply_same]`. Conclude with `contDiff_const`.

Simplify using `only [Fin.insertNth_apply_succAbove]`. Conclude with `contDiff_apply ℝ ℂ j`. Use `contDiff_pi.2 fun a => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `ContDiff.sum fun b _ => contDiff_const.mul (contDiff_pi.1 hv b)`.
-/
theorem contDiff_mulVec_insertNth {N : ℕ} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (i : Fin (N + 1)) :
    ContDiff ℝ ∞ (fun z : Fin N → ℂ => T *ᵥ (Fin.insertNth i (1 : ℂ) z : Fin (N + 1) → ℂ)) := by
  have hv : ContDiff ℝ ∞ (fun z : Fin N → ℂ => (Fin.insertNth i (1 : ℂ) z : Fin (N + 1) → ℂ)) := by
    refine contDiff_pi.2 fun b => ?_
    obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i b
    · simp only [Fin.insertNth_apply_same]
      exact contDiff_const
    · simp only [Fin.insertNth_apply_succAbove]
      exact contDiff_apply ℝ ℂ j
  refine contDiff_pi.2 fun a => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun b _ => contDiff_const.mul (contDiff_pi.1 hv b)

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrArg (fun x => T⁻¹ *ᵥ x) h0`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hT, Matrix.one_mulVec, Matrix.mulVec_zero] at h1`. Establish `h2` using `congrFun h1 i`. Simplify using `at h2`.
-/
theorem mulVec_insertNth_ne_zero {N : ℕ} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hT : IsUnit T.det)
    (i : Fin (N + 1)) (z : Fin N → ℂ) : T *ᵥ (Fin.insertNth i (1 : ℂ) z : Fin (N + 1) → ℂ) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun x => T⁻¹ *ᵥ x) h0
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hT, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h1
  have h2 := congrFun h1 i
  simp at h2

end SheetFormComparison

open SheetFormComparison in

/- English proof (translation)
Introduce `n D h c ψ hdeg hψ`. Take `_ | N` from `n`. Conclude with `⟨0, fun s U y _ _ _ hsy => absurd (Subsingleton.elim _ _) hsy⟩`. Use `set T := h.matᵀ with hTdef`. Establish `hT : IsUnit T.det` using `by rw [hTdef, Matrix.det_transpose]; exact h.isUnit_det`.

Establish `hTinv : ∀ x, T *ᵥ (T⁻¹ *ᵥ x) = x` using `fun x => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hT, Matrix.one_mulVec]`. Use `set φ : Fin (N + 1) → Fin D → (Fin N → ℂ) → ℝ := fun i k z => ψ k (T *ᵥ (Fin.insertNth i (1 : ℂ) z : Fin (N + 1) → ℂ)) with hφdef`. Establish `hφs : ∀ i k, ContDiff ℝ 2 (φ i k)` using `fun i k => contDiff_iff_contDiffAt.2 fun z => (((hψ k).contDiffAt (isOpen_ne.mem_nhds (mulVec_insertNth_ne_zero hT i z))).of_le (WithTop.coe_le_coe.2 le_top)).comp z (((contDiff_mulVec_insertNth T i).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)`. Establish `hb : ∀ i, ∃ a : ℝ, 0 ≤ a ∧ ∀ k, ∀ z ∈ Metric.closedBall (0 : Fin N → ℂ) 1, (hessC (φ i k) z + (a : ℂ) • 1).PosSemidef ∧ (-hessC (φ i k) z + (a : ℂ) • 1).PosSemidef` using `fun i => TubeFormComparison.exists_hessC_bound (φ i) _ (isCompact_closedBall 0 1) (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.subset_univ _) (fun k => (hφs i k).contDiffOn)`.

Use `choose a ha0 ha using hb`. Use `set A : ℝ := ∑ i, a i with hAdef`. Establish `hA0 : 0 ≤ A` using `Finset.sum_nonneg fun i _ => ha0 i`. Use `set m : ℝ := (1 + N) ^ 2 with hm`. Use `set C0 : ℝ := ∑ k, |c k| + 2 * A * m with hC0`.

Establish `hm0 : 0 ≤ m` using `by positivity`. Establish `hC00 : 0 ≤ C0` using `by positivity`. Use `⟨3 ^ D * C0 ^ D, fun s U y hU hyU hsd hsy => ?_⟩` and prove the remaining obligations. Establish `hsa : AnalyticAt ℂ s y` using `analyticAt_pi_iff.2 fun b => ReciprocityTheory.AnForm.Osgood.osgood _ U (fun z => s z b) hU (differentiableOn_pi.1 hsd b) _ hyU`. Use `set v : (Fin D → ℂ) → Fin (N + 1) → ℂ := fun z => T⁻¹ *ᵥ s z with hvdef`.

Establish `hva : ∀ b, AnalyticAt ℂ (fun z => v z b) y` using `fun b => by`. Simplify using `only [hvdef, Matrix.mulVec, dotProduct]`. Conclude with `Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 hsa) j)`. Take `⟨i, -, hi⟩` from `Finset.exists_max_image Finset.univ (fun b => ‖v y b‖) Finset.univ_nonempty`. Establish `hvi : v y i ≠ 0`.

Introduce `h0`. Apply `hsy` to reduce the goal to its premises. Establish `hv0 : v y = 0` using `funext fun b => by`. Use `hi b (Finset.mem_univ b)` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `norm_le_zero_iff.1 this`. Rewrite using `[← hTinv (s y)]`. Express the relevant statement in the definitionally equal form `T *ᵥ v y = 0`. Rewrite using `[hv0, Matrix.mulVec_zero]`. Use `set τ : (Fin D → ℂ) → Fin N → ℂ := fun z j => v z (i.succAbove j) / v z i with hτdef`.

Establish `hτa : AnalyticAt ℂ τ y` using `analyticAt_pi_iff.2 fun j => (hva (i.succAbove j)).div (hva i) hvi`. Establish `hτK : τ y ∈ Metric.closedBall (0 : Fin N → ℂ) 1`. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]`. Introduce `j`. Simplify using `only [hτdef, norm_div]`.

Conclude with `div_le_one_of_le₀ (hi _ (Finset.mem_univ _)) (norm_nonneg _)`. Establish `hev : ∀ᶠ z in 𝓝 y, v z i ≠ 0` using `(hva i).continuousAt.eventually_ne hvi`. Establish `hins : ∀ z, v z i ≠ 0 → v z = v z i • (Fin.insertNth i (1 : ℂ) (τ z) : Fin (N + 1) → ℂ)` using `fun z hz => funext fun b => by`. Take `rfl | ⟨j, rfl⟩` from `Fin.eq_self_or_eq_succAbove i b`. Simplify using the standard rewrite rules.

Simplify using `only [Pi.smul_apply, Fin.insertNth_apply_succAbove, hτdef, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `hψs : ∀ k z, v z i ≠ 0 → ψ k (s z) = φ i k (τ z)` using `fun k z hz => by`. Establish `e : s z = v z i • (T *ᵥ (Fin.insertNth i (1 : ℂ) (τ z) : Fin (N + 1) → ℂ))`. Rewrite using `[← Matrix.mulVec_smul, ← hins z hz, hvdef, hTinv]`.

Rewrite using `[e, hdeg k _ _ hz]`. Establish `hLs : ∀ z, v z i ≠ 0 → Real.log (h.dualNorm (s z)) = (1 / 2) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ‖v z i‖` using `fun z hz => by`. Establish `hsum : ∑ b, ‖v z b‖ ^ 2 = ‖v z i‖ ^ 2 * (1 + normSqSum (τ z))`. Establish `hb : ∀ b, ‖v z b‖ ^ 2 = ‖v z i‖ ^ 2 * ‖(Fin.insertNth i (1 : ℂ) (τ z) : Fin (N + 1) → ℂ) b‖ ^ 2` using `fun b => by conv_lhs => rw [hins z hz]`. Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`.

Rewrite using `[Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]`. Rewrite using `[Fin.sum_univ_succAbove _ i]`. Simplify using `[normSqSum]`. Establish `hdn : h.dualNorm (s z) = Real.sqrt (∑ b, ‖v z b‖ ^ 2)` using `rfl`. Establish `hq : 0 < 1 + normSqSum (τ z)` using `one_add_normSqSum_pos _`.

Establish `hn : 0 < ‖v z i‖` using `norm_pos_iff.2 hz`. Rewrite using `[hdn, hsum, Real.log_sqrt (by positivity), Real.log_mul (by positivity) hq.ne', Real.log_pow]`. Unfold `HilbertSamuel.ProjFS.logPot`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `set G : (Fin N → ℂ) → ℝ := fun w => (1 / 2) * HilbertSamuel.ProjFS.logPot w with hGdef`. Use `set F : Fin D → (Fin N → ℂ) → ℝ := fun k w => c k * G w + φ i k w with hFdef`. Establish `hGc : ContDiff ℝ 2 G` using `contDiff_const.mul ((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top))`. Establish `hFc : ∀ k, ContDiff ℝ 2 (F k)` using `fun k => (contDiff_const.mul hGc).add (hφs i k)`. Establish `hτc : ContDiffAt ℝ 2 τ y` using `(hτa.contDiffAt (n := 2)).restrict_scalars ℝ`.

Establish `hvic : ContDiffAt ℝ 2 (fun z => v z i) y` using `((hva i).contDiffAt (n := 2)).restrict_scalars ℝ`. Establish `hlogc : ContDiffAt ℝ 2 (fun z => Real.log ‖v z i‖) y` using `(hvic.norm ℝ hvi).log (norm_ne_zero_iff.2 hvi)`. Establish `hlog0 : hessC (fun z => Real.log ‖v z i‖) y = 0` using `ReciprocityTheory.AnForm.A.hessC_log_norm (fun z => v z i) y (hva i) hvi`. Use `set Bm := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hBm`. Establish `hBJ : Bmᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ`.

Use extensionality with `a b`. Simplify using `[hBm]`. Establish `hL : hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y = Bmᴴ * hessC G (τ y) * Bm`. Establish `hg : ((fun x => Real.log (h.dualNorm x)) ∘ s) =ᶠ[𝓝 y] fun z => (G ∘ τ) z + Real.log ‖v z i‖` using `by filter_upwards [hev] with z hz`. Simplify using `only [Function.comp_apply, hGdef]`.

Conclude with `hLs z hz`. Rewrite using `[hessC_congr hg, ReciprocityTheory.AnForm.M.hessC_add' _ _ y (hGc.contDiffAt.comp y hτc) hlogc, hlog0, add_zero, hBJ]`. Conclude with `ReciprocityTheory.AnForm.A.hessC_comp G τ y hτa hGc.contDiffAt`. Establish `hη : ∀ k, hessC ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y = Bmᴴ * hessC (F k) (τ y) * Bm` using `fun k => by`. Establish `hg : ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) =ᶠ[𝓝 y] fun z => (F k ∘ τ) z + c k * Real.log ‖v z i‖` using `by filter_upwards [hev] with z hz`.

Simplify using `only [Function.comp_apply, hFdef, hGdef]`. Rewrite using `[hLs z hz, hψs k z hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hessC_congr hg, ReciprocityTheory.AnForm.M.hessC_add' _ _ y ((hFc k).contDiffAt.comp y hτc) (contDiffAt_const.mul hlogc), ReciprocityTheory.AnForm.M.hessC_const_mul', hlog0, smul_zero, add_zero, hBJ]`. Conclude with `ReciprocityTheory.AnForm.A.hessC_comp (F k) τ y hτa (hFc k).contDiffAt`.

Use `set H1 := hessC (HilbertSamuel.ProjFS.logPot (N := N)) (τ y) with hH1`. Establish `hHG : hessC G (τ y) = ((1 / 2 : ℝ) : ℂ) • H1` using `ReciprocityTheory.AnForm.M.hessC_const_mul' _ _ _`. Establish `hHF : ∀ k, hessC (F k) (τ y) = (c k : ℂ) • hessC G (τ y) + hessC (φ i k) (τ y)` using `fun k => by show hessC (fun w => c k * G w + φ i k w) (τ y) = _`. Rewrite using `[ReciprocityTheory.AnForm.M.hessC_add' _ _ _ (contDiffAt_const.mul hGc.contDiffAt) (hφs i k).contDiffAt, ReciprocityTheory.AnForm.M.hessC_const_mul']`. Establish `hH1p : H1.PosSemidef` using `ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ ((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt (fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w)`.

Establish `hGp : (((1 / 2 : ℝ) : ℂ) • H1).PosSemidef` using `hH1p.smul (Complex.zero_le_real.2 (by norm_num))`. Establish `hlow : ((m : ℂ) • H1 - 1).PosSemidef` using `posSemidef_hessC_logPot_sub (mem_closedBall_zero_iff.1 hτK)`. Establish `hai : a i ≤ A` using `Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)`. Establish `hmid : ∀ k, ((C0 : ℂ) • hessC G (τ y) - hessC (F k) (τ y)).PosSemidef ∧ (hessC (F k) (τ y) + (C0 : ℂ) • hessC G (τ y)).PosSemidef` using `fun k => by`. Establish `hck : |c k| ≤ ∑ k, |c k|` using `Finset.single_le_sum (f := fun k => |c k|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)`.

Establish `h1 : 0 ≤ C0 - c k - 2 * A * m` using `by rw [hC0]; linarith [le_abs_self (c k)]`. Establish `h2 : 0 ≤ C0 + c k - 2 * A * m` using `by rw [hC0]; linarith [neg_abs_le (c k)]`. Take `⟨hP1, hP2⟩` from `ha i k (τ y) hτK`. Use `set P := hessC (φ i k) (τ y) with hP`. Establish `hAi : (0 : ℂ) ≤ ((A - a i : ℝ) : ℂ)` using `Complex.zero_le_real.2 (by linarith)`.

Establish `hPA1 : (P + (A : ℂ) • 1).PosSemidef`. Establish `e : P + (A : ℂ) • 1 = (P + (a i : ℂ) • 1) + ((A - a i : ℝ) : ℂ) • 1`. Use `push_cast`. Use `module`. Rewrite using `[e]`.

Conclude with `hP1.add (Matrix.PosSemidef.one.smul hAi)`. Establish `hPA2 : (-P + (A : ℂ) • 1).PosSemidef`. Establish `e : -P + (A : ℂ) • 1 = (-P + (a i : ℂ) • 1) + ((A - a i : ℝ) : ℂ) • 1`. Use `push_cast`. Use `module`.

Rewrite using `[e]`. Conclude with `hP2.add (Matrix.PosSemidef.one.smul hAi)`. Rewrite using `[hHF k, hHG]`. Prove the components needed by the constructor for the conclusion. Establish `e : (C0 : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) - ((c k : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + P) = ((C0 - c k - 2 * A * m : ℝ) : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + (A : ℂ) • ((m : ℂ) • H1 - 1) + (-P + (A : ℂ) • 1)`.

Use `push_cast`. Use `module`. Rewrite using `[e]`. Conclude with `((hGp.smul (Complex.zero_le_real.2 h1)).add (hlow.smul (Complex.zero_le_real.2 hA0))).add hPA2`. Establish `e : (c k : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + P + (C0 : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) = ((C0 + c k - 2 * A * m : ℝ) : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + (A : ℂ) • ((m : ℂ) • H1 - 1) + (P + (A : ℂ) • 1)`.

Use `push_cast`. Use `module`. Rewrite using `[e]`. Conclude with `((hGp.smul (Complex.zero_le_real.2 h2)).add (hlow.smul (Complex.zero_le_real.2 hA0))).add hPA1`. Establish `hmain` using `ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le (fun k => hessC ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y) (fun _ => (C0 : ℂ) • hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y) (fun k => by`.

Rewrite using `[hL, hη k, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]`. Conclude with `(hmid k).1.conjTranspose_mul_mul_same Bm)`. Use the proof step `(fun k => by`. Rewrite using `[hL, hη k, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]`. Conclude with `(hmid k).2.conjTranspose_mul_mul_same Bm)`.

Establish `hs : mdisc (fun _ : Fin D => (C0 : ℂ) • hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y) = (C0 : ℂ) ^ D * mdisc (fun _ : Fin D => hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y)` using `IndefiniteRowSideFullHecke.ComplexSets.mdisc_const_smul _ _`. Rewrite `hmain` using `[hs, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Establish `hmd : ∀ Φ : Fin D → (Fin D → ℂ) → ℝ, maDens Φ y = (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (Φ k) y).re` using `fun Φ => rfl`. Rewrite using `[hmd, hmd, abs_mul]`. Establish `hK0 : 0 ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D` using `by positivity`.

Rewrite using `[abs_of_nonneg hK0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem SheetFormCompare.proof : SheetFormCompare.Statement := by
  intro n D h c ψ hdeg hψ
  obtain _ | N := n
  · exact ⟨0, fun s U y _ _ _ hsy => absurd (Subsingleton.elim _ _) hsy⟩
  set T := h.matᵀ with hTdef
  have hT : IsUnit T.det := by rw [hTdef, Matrix.det_transpose]; exact h.isUnit_det
  have hTinv : ∀ x, T *ᵥ (T⁻¹ *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hT, Matrix.one_mulVec]
  set φ : Fin (N + 1) → Fin D → (Fin N → ℂ) → ℝ :=
    fun i k z => ψ k (T *ᵥ (Fin.insertNth i (1 : ℂ) z : Fin (N + 1) → ℂ)) with hφdef
  have hφs : ∀ i k, ContDiff ℝ 2 (φ i k) := fun i k =>
    contDiff_iff_contDiffAt.2 fun z =>
      (((hψ k).contDiffAt (isOpen_ne.mem_nhds (mulVec_insertNth_ne_zero hT i z))).of_le
        (WithTop.coe_le_coe.2 le_top)).comp z
        (((contDiff_mulVec_insertNth T i).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have hb : ∀ i, ∃ a : ℝ, 0 ≤ a ∧ ∀ k, ∀ z ∈ Metric.closedBall (0 : Fin N → ℂ) 1,
      (hessC (φ i k) z + (a : ℂ) • 1).PosSemidef ∧ (-hessC (φ i k) z + (a : ℂ) • 1).PosSemidef :=
    fun i => TubeFormComparison.exists_hessC_bound (φ i) _ (isCompact_closedBall 0 1) (fun _ => Set.univ)
      (fun _ => isOpen_univ) (fun _ => Set.subset_univ _) (fun k => (hφs i k).contDiffOn)
  choose a ha0 ha using hb
  set A : ℝ := ∑ i, a i with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha0 i
  set m : ℝ := (1 + N) ^ 2 with hm
  set C0 : ℝ := ∑ k, |c k| + 2 * A * m with hC0
  have hm0 : 0 ≤ m := by positivity
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨3 ^ D * C0 ^ D, fun s U y hU hyU hsd hsy => ?_⟩

  have hsa : AnalyticAt ℂ s y := analyticAt_pi_iff.2 fun b =>
    ReciprocityTheory.AnForm.Osgood.osgood _ U (fun z => s z b) hU (differentiableOn_pi.1 hsd b) _ hyU
  set v : (Fin D → ℂ) → Fin (N + 1) → ℂ := fun z => T⁻¹ *ᵥ s z with hvdef
  have hva : ∀ b, AnalyticAt ℂ (fun z => v z b) y := fun b => by
    simp only [hvdef, Matrix.mulVec, dotProduct]
    exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 hsa) j)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun b => ‖v y b‖) Finset.univ_nonempty
  have hvi : v y i ≠ 0 := by
    intro h0
    apply hsy
    have hv0 : v y = 0 := funext fun b => by
      have := hi b (Finset.mem_univ b)
      rw [h0, norm_zero] at this
      exact norm_le_zero_iff.1 this
    rw [← hTinv (s y)]
    change T *ᵥ v y = 0
    rw [hv0, Matrix.mulVec_zero]
  set τ : (Fin D → ℂ) → Fin N → ℂ := fun z j => v z (i.succAbove j) / v z i with hτdef
  have hτa : AnalyticAt ℂ τ y :=
    analyticAt_pi_iff.2 fun j => (hva (i.succAbove j)).div (hva i) hvi
  have hτK : τ y ∈ Metric.closedBall (0 : Fin N → ℂ) 1 := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    simp only [hτdef, norm_div]
    exact div_le_one_of_le₀ (hi _ (Finset.mem_univ _)) (norm_nonneg _)
  have hev : ∀ᶠ z in 𝓝 y, v z i ≠ 0 := (hva i).continuousAt.eventually_ne hvi
  have hins : ∀ z, v z i ≠ 0 → v z = v z i • (Fin.insertNth i (1 : ℂ) (τ z) : Fin (N + 1) → ℂ) :=
    fun z hz => funext fun b => by
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i b
      · simp
      · simp only [Pi.smul_apply, Fin.insertNth_apply_succAbove, hτdef, smul_eq_mul]
        field_simp
  have hψs : ∀ k z, v z i ≠ 0 → ψ k (s z) = φ i k (τ z) := fun k z hz => by
    have e : s z = v z i • (T *ᵥ (Fin.insertNth i (1 : ℂ) (τ z) : Fin (N + 1) → ℂ)) := by
      rw [← Matrix.mulVec_smul, ← hins z hz, hvdef, hTinv]
    rw [e, hdeg k _ _ hz]
  have hLs : ∀ z, v z i ≠ 0 → Real.log (h.dualNorm (s z)) =
      (1 / 2) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ‖v z i‖ := fun z hz => by
    have hsum : ∑ b, ‖v z b‖ ^ 2 = ‖v z i‖ ^ 2 * (1 + normSqSum (τ z)) := by
      have hb : ∀ b, ‖v z b‖ ^ 2 = ‖v z i‖ ^ 2 * ‖(Fin.insertNth i (1 : ℂ) (τ z) : Fin (N + 1) → ℂ) b‖ ^ 2 :=
        fun b => by
          conv_lhs => rw [hins z hz]
          rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
      rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
      rw [Fin.sum_univ_succAbove _ i]
      simp [normSqSum]
    have hdn : h.dualNorm (s z) = Real.sqrt (∑ b, ‖v z b‖ ^ 2) := rfl
    have hq : 0 < 1 + normSqSum (τ z) := one_add_normSqSum_pos _
    have hn : 0 < ‖v z i‖ := norm_pos_iff.2 hz
    rw [hdn, hsum, Real.log_sqrt (by positivity), Real.log_mul (by positivity) hq.ne', Real.log_pow]
    unfold HilbertSamuel.ProjFS.logPot
    push_cast
    ring

  set G : (Fin N → ℂ) → ℝ := fun w => (1 / 2) * HilbertSamuel.ProjFS.logPot w with hGdef
  set F : Fin D → (Fin N → ℂ) → ℝ := fun k w => c k * G w + φ i k w with hFdef
  have hGc : ContDiff ℝ 2 G :=
    contDiff_const.mul ((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top))
  have hFc : ∀ k, ContDiff ℝ 2 (F k) := fun k => (contDiff_const.mul hGc).add (hφs i k)
  have hτc : ContDiffAt ℝ 2 τ y := (hτa.contDiffAt (n := 2)).restrict_scalars ℝ
  have hvic : ContDiffAt ℝ 2 (fun z => v z i) y := ((hva i).contDiffAt (n := 2)).restrict_scalars ℝ
  have hlogc : ContDiffAt ℝ 2 (fun z => Real.log ‖v z i‖) y :=
    (hvic.norm ℝ hvi).log (norm_ne_zero_iff.2 hvi)
  have hlog0 : hessC (fun z => Real.log ‖v z i‖) y = 0 :=
    ReciprocityTheory.AnForm.A.hessC_log_norm (fun z => v z i) y (hva i) hvi
  set Bm := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hBm
  have hBJ : Bmᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ := by
    ext a b
    simp [hBm]

  have hL : hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y = Bmᴴ * hessC G (τ y) * Bm := by
    have hg : ((fun x => Real.log (h.dualNorm x)) ∘ s) =ᶠ[𝓝 y]
        fun z => (G ∘ τ) z + Real.log ‖v z i‖ := by
      filter_upwards [hev] with z hz
      simp only [Function.comp_apply, hGdef]
      exact hLs z hz
    rw [hessC_congr hg, ReciprocityTheory.AnForm.M.hessC_add' _ _ y (hGc.contDiffAt.comp y hτc) hlogc, hlog0,
      add_zero, hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp G τ y hτa hGc.contDiffAt
  have hη : ∀ k, hessC ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y =
      Bmᴴ * hessC (F k) (τ y) * Bm := fun k => by
    have hg : ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) =ᶠ[𝓝 y]
        fun z => (F k ∘ τ) z + c k * Real.log ‖v z i‖ := by
      filter_upwards [hev] with z hz
      simp only [Function.comp_apply, hFdef, hGdef]
      rw [hLs z hz, hψs k z hz]
      ring
    rw [hessC_congr hg, ReciprocityTheory.AnForm.M.hessC_add' _ _ y ((hFc k).contDiffAt.comp y hτc)
      (contDiffAt_const.mul hlogc), ReciprocityTheory.AnForm.M.hessC_const_mul', hlog0, smul_zero, add_zero, hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp (F k) τ y hτa (hFc k).contDiffAt

  set H1 := hessC (HilbertSamuel.ProjFS.logPot (N := N)) (τ y) with hH1
  have hHG : hessC G (τ y) = ((1 / 2 : ℝ) : ℂ) • H1 := ReciprocityTheory.AnForm.M.hessC_const_mul' _ _ _
  have hHF : ∀ k, hessC (F k) (τ y) = (c k : ℂ) • hessC G (τ y) + hessC (φ i k) (τ y) := fun k => by
    show hessC (fun w => c k * G w + φ i k w) (τ y) = _
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ _ (contDiffAt_const.mul hGc.contDiffAt) (hφs i k).contDiffAt,
      ReciprocityTheory.AnForm.M.hessC_const_mul']
  have hH1p : H1.PosSemidef := ReciprocityTheory.AnForm.M.hessC_posSemidef _ _
    ((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
    (fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w)
  have hGp : (((1 / 2 : ℝ) : ℂ) • H1).PosSemidef := hH1p.smul (Complex.zero_le_real.2 (by norm_num))
  have hlow : ((m : ℂ) • H1 - 1).PosSemidef :=
    posSemidef_hessC_logPot_sub (mem_closedBall_zero_iff.1 hτK)
  have hai : a i ≤ A := Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)
  have hmid : ∀ k, ((C0 : ℂ) • hessC G (τ y) - hessC (F k) (τ y)).PosSemidef ∧
      (hessC (F k) (τ y) + (C0 : ℂ) • hessC G (τ y)).PosSemidef := fun k => by
    have hck : |c k| ≤ ∑ k, |c k| :=
      Finset.single_le_sum (f := fun k => |c k|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)
    have h1 : 0 ≤ C0 - c k - 2 * A * m := by rw [hC0]; linarith [le_abs_self (c k)]
    have h2 : 0 ≤ C0 + c k - 2 * A * m := by rw [hC0]; linarith [neg_abs_le (c k)]
    obtain ⟨hP1, hP2⟩ := ha i k (τ y) hτK
    set P := hessC (φ i k) (τ y) with hP
    have hAi : (0 : ℂ) ≤ ((A - a i : ℝ) : ℂ) := Complex.zero_le_real.2 (by linarith)
    have hPA1 : (P + (A : ℂ) • 1).PosSemidef := by
      have e : P + (A : ℂ) • 1 = (P + (a i : ℂ) • 1) + ((A - a i : ℝ) : ℂ) • 1 := by
        push_cast
        module
      rw [e]
      exact hP1.add (Matrix.PosSemidef.one.smul hAi)
    have hPA2 : (-P + (A : ℂ) • 1).PosSemidef := by
      have e : -P + (A : ℂ) • 1 = (-P + (a i : ℂ) • 1) + ((A - a i : ℝ) : ℂ) • 1 := by
        push_cast
        module
      rw [e]
      exact hP2.add (Matrix.PosSemidef.one.smul hAi)
    rw [hHF k, hHG]
    constructor
    · have e : (C0 : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) - ((c k : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + P) =
          ((C0 - c k - 2 * A * m : ℝ) : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + (A : ℂ) • ((m : ℂ) • H1 - 1) +
            (-P + (A : ℂ) • 1) := by
        push_cast
        module
      rw [e]
      exact ((hGp.smul (Complex.zero_le_real.2 h1)).add (hlow.smul (Complex.zero_le_real.2 hA0))).add hPA2
    · have e : (c k : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + P + (C0 : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) =
          ((C0 + c k - 2 * A * m : ℝ) : ℂ) • (((1 / 2 : ℝ) : ℂ) • H1) + (A : ℂ) • ((m : ℂ) • H1 - 1) +
            (P + (A : ℂ) • 1) := by
        push_cast
        module
      rw [e]
      exact ((hGp.smul (Complex.zero_le_real.2 h2)).add (hlow.smul (Complex.zero_le_real.2 hA0))).add hPA1

  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le
    (fun k => hessC ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y)
    (fun _ => (C0 : ℂ) • hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y)
    (fun k => by
      rw [hL, hη k, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub]
      exact (hmid k).1.conjTranspose_mul_mul_same Bm)
    (fun k => by
      rw [hL, hη k, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]
      exact (hmid k).2.conjTranspose_mul_mul_same Bm)
  have hs : mdisc (fun _ : Fin D => (C0 : ℂ) • hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y) =
      (C0 : ℂ) ^ D * mdisc (fun _ : Fin D => hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y) :=
    IndefiniteRowSideFullHecke.ComplexSets.mdisc_const_smul _ _
  rw [hs, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmain
  have hmd : ∀ Φ : Fin D → (Fin D → ℂ) → ℝ, maDens Φ y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (Φ k) y).re := fun Φ => rfl
  rw [hmd, hmd, abs_mul]
  have hK0 : 0 ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D := by positivity
  rw [abs_of_nonneg hK0]
  calc (D.factorial : ℝ) * (2 / Real.pi) ^ D *
        |(mdisc fun k => hessC ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y).re|
      ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D *
          ‖mdisc fun k => hessC ((fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hK0
    _ ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D * (3 ^ D * (C0 ^ D *
          (mdisc fun _ => hessC ((fun x => Real.log (h.dualNorm x)) ∘ s) y).re)) :=
        mul_le_mul_of_nonneg_left hmain hK0
    _ = _ := by ring

end

end GroundTheory.Heights₂.Heights
