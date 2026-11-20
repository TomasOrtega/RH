import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Topology Metric

noncomputable section
namespace GlobalTheory.AdaptedChart

variable {D : ℕ} {Y : Type} [TopologicalSpace Y]

/- English proof (translation)
Introduce `y hy`. Take `⟨j, hj⟩` from `A.cover y`. Establish `hT : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)` using `(A.chart j).isOpen_inter_preimage_symm hU`. Establish `hmem : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U` using `⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩`. Establish `h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j y)` using `(hf j).continuousAt (hT.mem_nhds hmem)`.

Establish `h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) y` using `h1.comp ((A.chart j).continuousAt hj)`. Establish `h3 : (f ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[𝓝 y] f` using `by filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz`. Simplify using `[(A.chart j).left_inv hz]`. Conclude with `(h2.congr h3).continuousWithinAt`.
-/
theorem continuousOn_of_charts {E : Type} [TopologicalSpace E] (A : FinHolAtlas D Y) {U : Set Y}
    (hU : IsOpen U) {f : Y → E}
    (hf : ∀ j, ContinuousOn (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn f U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hT : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hmem : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j y) :=
    (hf j).continuousAt (hT.mem_nhds hmem)
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) y :=
    h1.comp ((A.chart j).continuousAt hj)
  have h3 : (f ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[𝓝 y] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [(A.chart j).left_inv hz]
  exact (h2.congr h3).continuousWithinAt

def aff (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) : (Fin D → ℂ) ≃ₜ (Fin D → ℂ) :=
  (Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero ((δ : ℂ)⁻¹) (by simpa using hδ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem aff_apply (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) (z : Fin D → ℂ) :
    aff c δ hδ z = (δ : ℂ)⁻¹ • (z - c) := rfl

/- English proof (translation)
Simplify using `[aff, Homeomorph.smulOfNeZero, Units.smul_def]`.
-/
theorem aff_symm_apply (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) (w : Fin D → ℂ) :
    (aff c δ hδ).symm w = (δ : ℂ) • w + c := by
  simp [aff, Homeomorph.smulOfNeZero, Units.smul_def]

def rescale (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) (δ : ℝ) (hδ : δ ≠ 0) :
    OpenPartialHomeomorph Y (Fin D → ℂ) :=
  ((ψ.trans (aff c δ hδ).toOpenPartialHomeomorph).symm.restrOpen (ball 0 1) isOpen_ball).symm

/- English proof (translation)
Simplify using `[rescale, aff_apply]`.
-/
theorem rescale_apply (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) (δ : ℝ)
    (hδ : δ ≠ 0) (y : Y) : rescale ψ c δ hδ y = (δ : ℂ)⁻¹ • (ψ y - c) := by
  simp [rescale, aff_apply]

/- English proof (translation)
Simplify using `[rescale, aff_symm_apply]`.
-/
theorem rescale_symm_apply (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) (δ : ℝ)
    (hδ : δ ≠ 0) (w : Fin D → ℂ) : (rescale ψ c δ hδ).symm w = ψ.symm ((δ : ℂ) • w + c) := by
  simp [rescale, aff_symm_apply]

/- English proof (translation)
Rewrite using `[mem_ball, mem_ball, dist_zero_right, dist_eq_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, inv_mul_lt_iff₀ hδ, mul_one]`.
-/
theorem mem_ball_aff {c z : Fin D → ℂ} {δ : ℝ} (hδ : 0 < δ) :
    (δ : ℂ)⁻¹ • (z - c) ∈ ball (0 : Fin D → ℂ) 1 ↔ z ∈ ball c δ := by
  rw [mem_ball, mem_ball, dist_zero_right, dist_eq_norm, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hδ, inv_mul_lt_iff₀ hδ, mul_one]

/- English proof (translation)
Use extensionality with `y`. Establish `: y ∈ (rescale ψ c δ hδ.ne').source ↔ y ∈ ψ.source ∧ (δ : ℂ)⁻¹ • (ψ y - c) ∈ ball 0 1`. Simplify using `[rescale, aff_apply]`. Rewrite using `[this, mem_ball_aff hδ]`. Both sides reduce to the same expression.
-/
theorem rescale_source (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) {δ : ℝ}
    (hδ : 0 < δ) : (rescale ψ c δ hδ.ne').source = ψ.source ∩ ψ ⁻¹' ball c δ := by
  ext y
  have : y ∈ (rescale ψ c δ hδ.ne').source ↔ y ∈ ψ.source ∧ (δ : ℂ)⁻¹ • (ψ y - c) ∈ ball 0 1 := by
    simp [rescale, aff_apply]
  rw [this, mem_ball_aff hδ]; rfl

/- English proof (translation)
Use extensionality with `w`. Establish `: w ∈ (rescale ψ c δ hδ.ne').target ↔ (δ : ℂ) • w + c ∈ ψ.target ∧ w ∈ ball 0 1`. Simplify using `[rescale, aff_symm_apply]`. Rewrite using `[this]`. Use `⟨fun h => h.2, fun h => ⟨hsub ?_, h⟩⟩` and prove the remaining obligations.

Establish `hw : (δ : ℂ)⁻¹ • (((δ : ℂ) • w + c) - c) = w`. Rewrite using `[add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hδ.ne'), one_smul]`. Rewrite using `[← mem_ball_aff hδ, hw]`. Conclude with `h`.
-/
theorem rescale_target (ψ : OpenPartialHomeomorph Y (Fin D → ℂ)) (c : Fin D → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hsub : ball c δ ⊆ ψ.target) : (rescale ψ c δ hδ.ne').target = ball 0 1 := by
  ext w
  have : w ∈ (rescale ψ c δ hδ.ne').target ↔ (δ : ℂ) • w + c ∈ ψ.target ∧ w ∈ ball 0 1 := by
    simp [rescale, aff_symm_apply]
  rw [this]
  refine ⟨fun h => h.2, fun h => ⟨hsub ?_, h⟩⟩
  have hw : (δ : ℂ)⁻¹ • (((δ : ℂ) • w + c) - c) = w := by
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hδ.ne'), one_smul]
  rw [← mem_ball_aff hδ, hw]; exact h

/- English proof (translation)
Use `fun_prop`.
-/
theorem analyticAt_aff (c : Fin D → ℂ) (a : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun z : Fin D → ℂ => a • (z - c)) w := by
  fun_prop

/- English proof (translation)
Use `fun_prop`.
-/
theorem analyticAt_aff' (c : Fin D → ℂ) (a : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun z : Fin D → ℂ => a • z + c) w := by
  fun_prop

open GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic in

/- English proof (translation)
Introduce `D Y _ _ _ A L s m W hB y₀ N hN hy₀N`. Establish `hrad` using `fun y => exp_one_le_rad hB y`. Take `⟨hPot, hSec, hSNC, -⟩` from `hB`. Take `⟨ψ, hψc, hy₀ψ, hψU, σ, hσinj, -, u, hu, hu0, hsu⟩` from `hSNC y₀`. Use `set c := ψ y₀ with hc`.

Set `fac : Fin m → Y → ℂ` to `fun k y => (σ k).elim 1 (fun i => ψ y i)`. Establish `hfac_some : ∀ k i y, σ k = some i → fac k y = ψ y i`. Introduce `k i y h`. Simplify using `[fac, h]`. Establish `hfac_ne : ∀ k y, fac k y ≠ 0 ↔ ∀ i, σ k = some i → ψ y i ≠ 0`.

Introduce `k y`. Break down `h : σ k with _ | i` into its components or cases. Simplify using `[fac, h]`. Simplify using `[fac, h]`. Establish `hsu' : ∀ y ∈ ψ.source, s y₀ y = u y * ∏ k, fac k y`.

Introduce `y hy`. Rewrite using `[hsu y hy]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases h : σ k with _ | i <;> simp [fac, h]`.

Use `set V : Set (Fin D → ℂ) := {z | ∀ i, c i ≠ 0 → z i ≠ 0} with hVdef`. Establish `hV : IsOpen V`. Establish `: V = ⋂ i, {z : Fin D → ℂ | c i ≠ 0 → z i ≠ 0}` using `by ext z; simp [V]`. Rewrite using `[this]`. Use `isOpen_iInter_of_finite fun i => ?_` and prove the remaining obligations.

Distinguish the cases in `hci : c i = 0`. Simplify using `[hci]`. Simplify `isOpen_ne_fun (continuous_apply i) continuous_const` using `[hci]`. Use `set T := ψ.target ∩ ψ.symm ⁻¹' N ∩ V with hTdef`. Establish `hT : IsOpen T` using `(ψ.isOpen_inter_preimage_symm hN).inter hV`.

Establish `hcT : c ∈ T` using `⟨⟨ψ.map_source hy₀ψ, by simp [c, ψ.left_inv hy₀ψ, hy₀N]⟩, fun i h => h⟩`. Take `⟨ε, hε, hεT⟩` from `Metric.isOpen_iff.1 hT c hcT`. Use `set δ := ε / 2 with hδdef`. Establish `hδ : 0 < δ` using `by positivity`. Establish `hδT : closedBall c δ ⊆ T` using `(closedBall_subset_ball (by linarith)).trans hεT`.

Establish `hballT : ball c δ ⊆ ψ.target` using `fun z hz => (hδT (ball_subset_closedBall hz)).1.1`. Use `set Φ := rescale ψ c δ hδ.ne' with hΦdef`. Establish `hΦapp : ∀ y, Φ y = (δ : ℂ)⁻¹ • (ψ y - c)` using `rescale_apply ψ c δ hδ.ne'`. Establish `hΦsymm : ∀ w, Φ.symm w = ψ.symm ((δ : ℂ) • w + c)` using `rescale_symm_apply ψ c δ hδ.ne'`. Establish `hΦsrc : Φ.source = ψ.source ∩ ψ ⁻¹' ball c δ` using `rescale_source ψ c hδ`.

Establish `hΦtgt : Φ.target = ball 0 1` using `rescale_target ψ c hδ hballT`. Establish `hδC : (δ : ℂ) ≠ 0` using `by exact_mod_cast hδ.ne'`. Establish `hΦS : ∀ y i, c i = 0 → Φ y i = (δ : ℂ)⁻¹ * ψ y i`. Introduce `y i hci`. Rewrite using `[hΦapp]`.

Simplify using `[hci]`. Use `set K := ψ.symm '' closedBall c δ with hKdef`. Establish `hKψ : K ⊆ ψ.source`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `ψ.map_target (hδT hz).1.1`.

Establish `hKV : ∀ y ∈ K, ψ y ∈ V`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[ψ.right_inv (hδT hz).1.1]`. Conclude with `(hδT hz).2`. Establish `hK : IsCompact K` using `(isCompact_closedBall c δ).image_of_continuousOn (ψ.continuousOn_symm.mono fun z hz => (hδT hz).1.1)`.

Establish `hsrcK : Φ.source ⊆ K`. Introduce `y hy`. Rewrite `hy` using `[hΦsrc]`. Conclude with `⟨ψ y, ball_subset_closedBall hy.2, ψ.left_inv hy.1⟩`. Establish `hsrcψ : ∀ y ∈ Φ.source, y ∈ ψ.source` using `fun y hy => by rw [hΦsrc] at hy; exact hy.1`.

Use `set S : Finset (Fin D) := Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ c i = 0) with hSdef`. Establish `hnz : ∀ y ∈ ψ.source, (s y y ≠ 0 ↔ s y₀ y ≠ 0)`. Introduce `y hy`. Establish `hn` using `hSec.2 y₀ y y ⟨hψU hy, L.mem_U y⟩`. Establish `e1` using `Real.exp_pos (-L.φ y y)`.

Establish `e2` using `Real.exp_pos (-L.φ y₀ y)`. Rewrite using `[ne_eq, ne_eq, ← norm_eq_zero, ← norm_eq_zero (a := s y₀ y)]`. Prove the components needed by the constructor for the conclusion. Introduce `h h0`. Apply `h` to reduce the goal to its premises.

Establish `: ‖s y y‖ * Real.exp (-L.φ y y) = 0` using `by rw [← hn, h0, zero_mul]`. Conclude with `(mul_eq_zero.1 this).resolve_right e1.ne'`. Introduce `h h0`. Apply `h` to reduce the goal to its premises. Establish `: ‖s y₀ y‖ * Real.exp (-L.φ y₀ y) = 0` using `by rw [hn, h0, zero_mul]`.

Conclude with `(mul_eq_zero.1 this).resolve_right e2.ne'`. Establish `hopn : ∀ y ∈ ψ.source, (y ∈ opn s ↔ ∀ k, fac k y ≠ 0)`. Introduce `y hy`. Express the relevant statement in the definitionally equal form `s y y ≠ 0 ↔ _`. Rewrite using `[hnz y hy, hsu' y hy, mul_ne_zero_iff, Finset.prod_ne_zero_iff]`.

Simplify using `[hu0 y hy]`. Establish `hdiv : ∀ y ∈ Φ.source, (y ∈ opn s ↔ Φ y ∉ ReciprocityTheory.AnForm.A.coordDiv S)`. Introduce `y hy`. Establish `hyψ` using `hsrcψ y hy`. Establish `hyV : ψ y ∈ V` using `hKV y (hsrcK hy)`.

Rewrite using `[hopn y hyψ]`. Simplify using `only [ReciprocityTheory.AnForm.A.coordDiv, Set.mem_setOf_eq, not_exists, not_and]`. Prove the components needed by the constructor for the conclusion. Introduce `h i hi h0`. Take `⟨k, hk, hci⟩` from `(Finset.mem_filter.1 hi).2`.

Rewrite `h0` using `[hΦS y i hci, mul_eq_zero]`. Break down `h0 with h0 | h0` into its components or cases. Conclude with `inv_ne_zero hδC h0`. Conclude with `(hfac_ne k y).1 (h k) i hk h0`. Introduce `h k`.

Rewrite using `[hfac_ne]`. Introduce `i hk`. Distinguish the cases in `hci : c i = 0`. Establish `hiS : i ∈ S` using `Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hk, hci⟩`. Introduce `h0`.

Apply `h i hiS` to reduce the goal to its premises. Rewrite using `[hΦS y i hci, h0, mul_zero]`. Conclude with `hyV i hci`. Establish `hcompat : IsCompatChart A Φ`. Introduce `j`.

Prove the components needed by the constructor for the conclusion. Introduce `z hz`. Establish `hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source` using `⟨hz.1, hsrcψ _ hz.2⟩`. Establish `h1` using `(hψc j).1 z hz'`. Establish `: Φ ∘ (A.chart j).symm = (fun w : Fin D → ℂ => (δ : ℂ)⁻¹ • (w - c)) ∘ (ψ ∘ (A.chart j).symm)`.

Use function extensionality and compare the values at `w`. Simplify using `[hΦapp]`. Rewrite using `[this]`. Conclude with `(analyticAt_aff c _ _).comp h1`. Introduce `w hw`.

Establish `hwb : w ∈ ball (0 : Fin D → ℂ) 1` using `hΦtgt ▸ hw.1`. Establish `hmem : (δ : ℂ) • w + c ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source`. Use `⟨hballT ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_ball_aff hδ, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hδC, one_smul]`. Conclude with `hwb`.

Use `hw.2` as an intermediate fact. Simplify using `only [Set.mem_preimage, hΦsymm] at this`. Conclude with `this`. Establish `h2` using `(hψc j).2 _ hmem`. Establish `: A.chart j ∘ Φ.symm = (A.chart j ∘ ψ.symm) ∘ (fun w : Fin D → ℂ => (δ : ℂ) • w + c)`.

Use function extensionality and compare the values at `w`. Simplify using `[hΦsymm]`. Rewrite using `[this]`. Conclude with `AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := fun w : Fin D → ℂ => (δ : ℂ) • w + c) h2 (analyticAt_aff' c _ w)`. Establish `huc : ContinuousOn u ψ.source` using `continuousOn_of_charts A ψ.open_source fun j => (hu j).continuousOn`.

Establish `hφc : ContinuousOn (L.φ y₀) (L.U y₀)` using `continuousOn_of_charts A (L.isOpen_U y₀) fun j => (hPot.1 y₀ j).continuousOn`. Establish `hfacc : ∀ k, ContinuousOn (fac k) ψ.source`. Introduce `k`. Break down `h : σ k with _ | i` into its components or cases. Simplify using `only [fac, h, Option.elim]`.

Conclude with `continuousOn_const`. Simplify using `only [fac, h, Option.elim]`. Conclude with `(continuous_apply i).comp_continuousOn ψ.continuousOn`. Use `set kS : Finset (Fin m) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0) with hkS`. Use `set kN : Finset (Fin m) := Finset.univ.filter (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0) with hkN`.

Set `F : Y → ℝ` to `fun y => -2 * Real.log ‖u y‖ + 2 * L.φ y₀ y - 2 * ∑ k ∈ kN, Real.log ‖fac k y‖`. Establish `hFc : ContinuousOn F K`. Use `((continuousOn_const.mul ((huc.mono hKψ).norm.log fun y hy => norm_ne_zero_iff.2 (hu0 y (hKψ hy)))).add (continuousOn_const.mul (hφc.mono fun y hy => hψU (hKψ hy)))).sub (continuousOn_const.mul (continuousOn_finset_sum _ fun k hk => ((hfacc k).mono hKψ).norm.log fun y hy => ?_))` and prove the remaining obligations. Rewrite using `[ne_eq, norm_eq_zero, ← ne_eq, hfac_ne]`. Introduce `i hi`.

Establish `hci : c i ≠ 0` using `fun h0 => (Finset.mem_filter.1 hk).2 ⟨i, hi, h0⟩`. Conclude with `hKV y hy i hci`. Take `⟨B, hBd⟩` from `hK.exists_bound_of_continuousOn hFc`. Use `set B' := max 0 (B - 2 * (S.card * Real.log δ)) with hB'def`. Establish `hB'0 : 0 ≤ B'` using `le_max_left _ _`.

Establish `hB'1 : B - 2 * (S.card * Real.log δ) ≤ B'` using `le_max_right _ _`. Establish `he : (1 : ℝ) ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `hlog2 : 0 ≤ Real.log (2 + B')` using `Real.log_nonneg (by linarith)`. Use `⟨Φ, S, K, Real.log (2 + B') + 1, hcompat, ?_, ?_, hΦtgt, hK, hsrcK, ?_, hdiv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦsrc]; exact ⟨hy₀ψ, by simp [c, hδ]⟩`.

Rewrite using `[hΦapp]`. Simplify using `[c]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `(hδT hz).1.2`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `y hy hyo`. Establish `hyψ` using `hsrcψ y hy`. Establish `hfk : ∀ k, fac k y ≠ 0` using `(hopn y hyψ).1 hyo`. Establish `hsy : s y₀ y ≠ 0` using `(hnz y hyψ).1 hyo`. Establish `hn` using `hSec.2 y₀ y y ⟨hψU hyψ, L.mem_U y⟩`.

Establish `hlog : logNormSec L s y = Real.log ‖u y‖ + ∑ k, Real.log ‖fac k y‖ - L.φ y₀ y`. Unfold `logNormSec`. Rewrite using `[← hn, Real.log_mul (norm_ne_zero_iff.2 hsy) (Real.exp_pos _).ne', Real.log_exp, hsu' y hyψ, norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.2 (hu0 y hyψ)) (Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hfk k)), Real.log_prod (fun k _ => norm_ne_zero_iff.2 (hfk k)) …`. Expand and normalize the polynomial expressions, which then agree. Establish `hsplit : ∑ k ∈ kS, Real.log ‖fac k y‖ + ∑ k ∈ kN, Real.log ‖fac k y‖ = ∑ k, Real.log ‖fac k y‖` using `Finset.sum_filter_add_sum_filter_not _ _ _`.

Establish `hval : ∀ i, c i = 0 → ψ y i ≠ 0 → Real.log ‖ψ y i‖ = Real.log δ - Real.log ‖Φ y i‖⁻¹`. Introduce `i hci hne`. Establish `h1 : ψ y i = (δ : ℂ) * Φ y i`. Rewrite using `[hΦS y i hci, ← mul_assoc, mul_inv_cancel₀ hδC, one_mul]`. Establish `hΦne : Φ y i ≠ 0` using `by rw [hΦS y i hci]; exact mul_ne_zero (inv_ne_zero hδC) hne`.

Rewrite using `[h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, Real.log_mul hδ.ne' (norm_ne_zero_iff.2 hΦne), Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ k ∈ kS, Real.log ‖fac k y‖ = ∑ i ∈ S, (Real.log δ - Real.log ‖Φ y i‖⁻¹)`. Use `Finset.sum_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `k hk`.

Take `⟨h1, h2⟩` from `Classical.choose_spec (Finset.mem_filter.1 hk).2`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, k, h1, h2⟩`. Introduce `k₁ hk₁ k₂ hk₂ h`. Establish `e1` using `(Classical.choose_spec (Finset.mem_filter.1 hk₁).2).1`. Establish `e2` using `(Classical.choose_spec (Finset.mem_filter.1 hk₂).2).1`.

Rewrite `e1` using `[h]`. Conclude with `hσinj k₁ k₂ _ e1 e2`. Introduce `i hi`. Take `⟨k, hk, hci⟩` from `(Finset.mem_filter.1 hi).2`. Establish `hkmem : k ∈ kS` using `Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, hci⟩`.

Use `⟨k, hkmem, ?_⟩` and prove the remaining obligations. Establish `e1` using `(Classical.choose_spec (Finset.mem_filter.1 hkmem).2).1`. Conclude with `(Option.some_injective _ (hk.symm.trans e1)).symm`. Introduce `k hk`. Take `⟨h1, h2⟩` from `Classical.choose_spec (Finset.mem_filter.1 hk).2`.

Rewrite using `[hfac_some k _ y h1]`. Conclude with `hval _ h2 ((hfac_ne k y).1 (hfk k) _ h1)`. Establish `hFy : F y ≤ B` using `le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hBd y (hsrcK hy))`. Use `set Λ := ∑ i ∈ S, Real.log ‖Φ y i‖⁻¹ with hΛdef`. Establish `hradeq : rad L s y = Real.exp 1 + F y - 2 * (S.card * Real.log δ) + 2 * Λ`.

Unfold `rad`. Rewrite using `[hlog, ← hsplit, hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`. Simplify using `only [F]`. Expand and normalize the polynomial expressions, which then agree. Establish `hΦball : ‖Φ y‖ < 1`.

Use `Φ.map_source hy` as an intermediate fact. Rewrite `this` using `[hΦtgt, mem_ball, dist_zero_right]`. Then use the resulting hypothesis. Establish `hΛ : 0 ≤ Λ` using `Finset.sum_nonneg fun i _ => by`. Establish `hlt : ‖Φ y i‖ < 1` using `lt_of_le_of_lt (norm_le_pi_norm (Φ y) i) hΦball`. Rewrite using `[Real.log_inv]`.

Combine the linear relations using `[Real.log_nonpos (norm_nonneg (Φ y i)) hlt.le]`. Establish `hT1 : Real.exp 1 ≤ Real.exp 1 + Λ` using `by linarith`. Establish `hlogT : 1 ≤ Real.log (Real.exp 1 + Λ)`. Use `Real.log_le_log (Real.exp_pos 1) hT1` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `hr_le : rad L s y ≤ (2 + B') * (Real.exp 1 + Λ)`. Rewrite using `[hradeq]`. Use polynomial arithmetic with `[mul_nonneg hB'0 (sub_nonneg.2 he), mul_nonneg hB'0 hΛ]`. Establish `hrpos : 0 < rad L s y` using `lt_of_lt_of_le (Real.exp_pos 1) (hrad y)`. Combine the equalities or inequalities in the displayed calculation.

Use polynomial arithmetic with `[mul_nonneg hlog2 (sub_nonneg.2 hlogT)]`.
-/
theorem exists_adapted : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (L : ReciprocityTheory.AnForm.M.LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary A L s W → ∀ (y₀ : Y) (N : Set Y), IsOpen N → y₀ ∈ N → ∃ (Φ : OpenPartialHomeomorph Y (Fin D → ℂ)) (S : Finset (Fin D)) (K : Set Y) (a : ℝ), ReciprocityTheory.AnForm.M.IsCompatChart A Φ ∧ y₀ ∈ Φ.source ∧ Φ y₀ = 0 ∧ Φ.target = Metric.ball 0 1 ∧ IsCompact K ∧ Φ.source ⊆ K ∧ K ⊆ N ∧ (∀ y ∈ Φ.source, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s ↔ Φ y ∉ ReciprocityTheory.AnForm.A.coordDiv S) ∧ 0 ≤ a ∧ ∀ y ∈ Φ.source, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s → Real.log (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.rad L s y) ≤ a * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖Φ y i‖⁻¹) := by
  intro D Y _ _ _ A L s m W hB y₀ N hN hy₀N
  classical
  have hrad := fun y => exp_one_le_rad hB y
  obtain ⟨hPot, hSec, hSNC, -⟩ := hB
  obtain ⟨ψ, hψc, hy₀ψ, hψU, σ, hσinj, -, u, hu, hu0, hsu⟩ := hSNC y₀
  set c := ψ y₀ with hc
  let fac : Fin m → Y → ℂ := fun k y => (σ k).elim 1 (fun i => ψ y i)
  have hfac_some : ∀ k i y, σ k = some i → fac k y = ψ y i := by
    intro k i y h; simp [fac, h]
  have hfac_ne : ∀ k y, fac k y ≠ 0 ↔ ∀ i, σ k = some i → ψ y i ≠ 0 := by
    intro k y
    rcases h : σ k with _ | i
    · simp [fac, h]
    · simp [fac, h]
  have hsu' : ∀ y ∈ ψ.source, s y₀ y = u y * ∏ k, fac k y := by
    intro y hy
    rw [hsu y hy]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases h : σ k with _ | i <;> simp [fac, h]

  set V : Set (Fin D → ℂ) := {z | ∀ i, c i ≠ 0 → z i ≠ 0} with hVdef
  have hV : IsOpen V := by
    have : V = ⋂ i, {z : Fin D → ℂ | c i ≠ 0 → z i ≠ 0} := by ext z; simp [V]
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hci : c i = 0
    · simp [hci]
    · simpa [hci] using isOpen_ne_fun (continuous_apply i) continuous_const
  set T := ψ.target ∩ ψ.symm ⁻¹' N ∩ V with hTdef
  have hT : IsOpen T := (ψ.isOpen_inter_preimage_symm hN).inter hV
  have hcT : c ∈ T := ⟨⟨ψ.map_source hy₀ψ, by simp [c, ψ.left_inv hy₀ψ, hy₀N]⟩, fun i h => h⟩
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 hT c hcT
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδT : closedBall c δ ⊆ T := (closedBall_subset_ball (by linarith)).trans hεT
  have hballT : ball c δ ⊆ ψ.target :=
    fun z hz => (hδT (ball_subset_closedBall hz)).1.1
  set Φ := rescale ψ c δ hδ.ne' with hΦdef
  have hΦapp : ∀ y, Φ y = (δ : ℂ)⁻¹ • (ψ y - c) := rescale_apply ψ c δ hδ.ne'
  have hΦsymm : ∀ w, Φ.symm w = ψ.symm ((δ : ℂ) • w + c) := rescale_symm_apply ψ c δ hδ.ne'
  have hΦsrc : Φ.source = ψ.source ∩ ψ ⁻¹' ball c δ := rescale_source ψ c hδ
  have hΦtgt : Φ.target = ball 0 1 := rescale_target ψ c hδ hballT
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hΦS : ∀ y i, c i = 0 → Φ y i = (δ : ℂ)⁻¹ * ψ y i := by
    intro y i hci; rw [hΦapp]; simp [hci]
  set K := ψ.symm '' closedBall c δ with hKdef
  have hKψ : K ⊆ ψ.source := by
    rintro _ ⟨z, hz, rfl⟩; exact ψ.map_target (hδT hz).1.1
  have hKV : ∀ y ∈ K, ψ y ∈ V := by
    rintro _ ⟨z, hz, rfl⟩; rw [ψ.right_inv (hδT hz).1.1]; exact (hδT hz).2
  have hK : IsCompact K :=
    (isCompact_closedBall c δ).image_of_continuousOn
      (ψ.continuousOn_symm.mono fun z hz => (hδT hz).1.1)
  have hsrcK : Φ.source ⊆ K := by
    intro y hy
    rw [hΦsrc] at hy
    exact ⟨ψ y, ball_subset_closedBall hy.2, ψ.left_inv hy.1⟩
  have hsrcψ : ∀ y ∈ Φ.source, y ∈ ψ.source := fun y hy => by rw [hΦsrc] at hy; exact hy.1

  set S : Finset (Fin D) := Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ c i = 0) with hSdef

  have hnz : ∀ y ∈ ψ.source, (s y y ≠ 0 ↔ s y₀ y ≠ 0) := by
    intro y hy
    have hn := hSec.2 y₀ y y ⟨hψU hy, L.mem_U y⟩
    have e1 := Real.exp_pos (-L.φ y y)
    have e2 := Real.exp_pos (-L.φ y₀ y)
    rw [ne_eq, ne_eq, ← norm_eq_zero, ← norm_eq_zero (a := s y₀ y)]
    constructor
    · intro h h0; apply h
      have : ‖s y y‖ * Real.exp (-L.φ y y) = 0 := by rw [← hn, h0, zero_mul]
      exact (mul_eq_zero.1 this).resolve_right e1.ne'
    · intro h h0; apply h
      have : ‖s y₀ y‖ * Real.exp (-L.φ y₀ y) = 0 := by rw [hn, h0, zero_mul]
      exact (mul_eq_zero.1 this).resolve_right e2.ne'
  have hopn : ∀ y ∈ ψ.source, (y ∈ opn s ↔ ∀ k, fac k y ≠ 0) := by
    intro y hy
    change s y y ≠ 0 ↔ _
    rw [hnz y hy, hsu' y hy, mul_ne_zero_iff, Finset.prod_ne_zero_iff]
    simp [hu0 y hy]
  have hdiv : ∀ y ∈ Φ.source, (y ∈ opn s ↔ Φ y ∉ ReciprocityTheory.AnForm.A.coordDiv S) := by
    intro y hy
    have hyψ := hsrcψ y hy
    have hyV : ψ y ∈ V := hKV y (hsrcK hy)
    rw [hopn y hyψ]
    simp only [ReciprocityTheory.AnForm.A.coordDiv, Set.mem_setOf_eq, not_exists, not_and]
    constructor
    · intro h i hi h0
      obtain ⟨k, hk, hci⟩ := (Finset.mem_filter.1 hi).2
      rw [hΦS y i hci, mul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact inv_ne_zero hδC h0
      · exact (hfac_ne k y).1 (h k) i hk h0
    · intro h k
      rw [hfac_ne]
      intro i hk
      by_cases hci : c i = 0
      · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hk, hci⟩
        intro h0; apply h i hiS; rw [hΦS y i hci, h0, mul_zero]
      · exact hyV i hci

  have hcompat : IsCompatChart A Φ := by
    intro j
    constructor
    · intro z hz
      have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := ⟨hz.1, hsrcψ _ hz.2⟩
      have h1 := (hψc j).1 z hz'
      have : Φ ∘ (A.chart j).symm =
          (fun w : Fin D → ℂ => (δ : ℂ)⁻¹ • (w - c)) ∘ (ψ ∘ (A.chart j).symm) := by
        funext w; simp [hΦapp]
      rw [this]
      exact (analyticAt_aff c _ _).comp h1
    · intro w hw
      have hwb : w ∈ ball (0 : Fin D → ℂ) 1 := hΦtgt ▸ hw.1
      have hmem : (δ : ℂ) • w + c ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source := by
        refine ⟨hballT ?_, ?_⟩
        · rw [← mem_ball_aff hδ, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hδC, one_smul]
          exact hwb
        · have := hw.2
          simp only [Set.mem_preimage, hΦsymm] at this
          exact this
      have h2 := (hψc j).2 _ hmem
      have : A.chart j ∘ Φ.symm =
          (A.chart j ∘ ψ.symm) ∘ (fun w : Fin D → ℂ => (δ : ℂ) • w + c) := by
        funext w; simp [hΦsymm]
      rw [this]
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := fun w : Fin D → ℂ => (δ : ℂ) • w + c) h2
        (analyticAt_aff' c _ w)
  have huc : ContinuousOn u ψ.source :=
    continuousOn_of_charts A ψ.open_source fun j => (hu j).continuousOn
  have hφc : ContinuousOn (L.φ y₀) (L.U y₀) :=
    continuousOn_of_charts A (L.isOpen_U y₀) fun j => (hPot.1 y₀ j).continuousOn
  have hfacc : ∀ k, ContinuousOn (fac k) ψ.source := by
    intro k
    rcases h : σ k with _ | i
    · simp only [fac, h, Option.elim]; exact continuousOn_const
    · simp only [fac, h, Option.elim]; exact (continuous_apply i).comp_continuousOn ψ.continuousOn
  set kS : Finset (Fin m) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0) with hkS
  set kN : Finset (Fin m) := Finset.univ.filter (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0) with hkN
  let F : Y → ℝ := fun y =>
    -2 * Real.log ‖u y‖ + 2 * L.φ y₀ y - 2 * ∑ k ∈ kN, Real.log ‖fac k y‖
  have hFc : ContinuousOn F K := by
    refine ((continuousOn_const.mul ((huc.mono hKψ).norm.log fun y hy =>
      norm_ne_zero_iff.2 (hu0 y (hKψ hy)))).add
      (continuousOn_const.mul (hφc.mono fun y hy => hψU (hKψ hy)))).sub
      (continuousOn_const.mul (continuousOn_finset_sum _ fun k hk =>
        ((hfacc k).mono hKψ).norm.log fun y hy => ?_))
    rw [ne_eq, norm_eq_zero, ← ne_eq, hfac_ne]
    intro i hi
    have hci : c i ≠ 0 := fun h0 => (Finset.mem_filter.1 hk).2 ⟨i, hi, h0⟩
    exact hKV y hy i hci
  obtain ⟨B, hBd⟩ := hK.exists_bound_of_continuousOn hFc
  set B' := max 0 (B - 2 * (S.card * Real.log δ)) with hB'def
  have hB'0 : 0 ≤ B' := le_max_left _ _
  have hB'1 : B - 2 * (S.card * Real.log δ) ≤ B' := le_max_right _ _
  have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog2 : 0 ≤ Real.log (2 + B') := Real.log_nonneg (by linarith)
  refine ⟨Φ, S, K, Real.log (2 + B') + 1, hcompat, ?_, ?_, hΦtgt, hK, hsrcK, ?_, hdiv, ?_, ?_⟩
  · rw [hΦsrc]; exact ⟨hy₀ψ, by simp [c, hδ]⟩
  · rw [hΦapp]; simp [c]
  · rintro _ ⟨z, hz, rfl⟩; exact (hδT hz).1.2
  · linarith
  · intro y hy hyo
    have hyψ := hsrcψ y hy
    have hfk : ∀ k, fac k y ≠ 0 := (hopn y hyψ).1 hyo
    have hsy : s y₀ y ≠ 0 := (hnz y hyψ).1 hyo
    have hn := hSec.2 y₀ y y ⟨hψU hyψ, L.mem_U y⟩
    have hlog : logNormSec L s y = Real.log ‖u y‖ + ∑ k, Real.log ‖fac k y‖ - L.φ y₀ y := by
      unfold logNormSec
      rw [← hn, Real.log_mul (norm_ne_zero_iff.2 hsy) (Real.exp_pos _).ne', Real.log_exp,
        hsu' y hyψ, norm_mul, norm_prod,
        Real.log_mul (norm_ne_zero_iff.2 (hu0 y hyψ))
          (Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hfk k)),
        Real.log_prod (fun k _ => norm_ne_zero_iff.2 (hfk k))]
      ring
    have hsplit : ∑ k ∈ kS, Real.log ‖fac k y‖ + ∑ k ∈ kN, Real.log ‖fac k y‖ =
        ∑ k, Real.log ‖fac k y‖ := Finset.sum_filter_add_sum_filter_not _ _ _
    have hval : ∀ i, c i = 0 → ψ y i ≠ 0 →
        Real.log ‖ψ y i‖ = Real.log δ - Real.log ‖Φ y i‖⁻¹ := by
      intro i hci hne
      have h1 : ψ y i = (δ : ℂ) * Φ y i := by
        rw [hΦS y i hci, ← mul_assoc, mul_inv_cancel₀ hδC, one_mul]
      have hΦne : Φ y i ≠ 0 := by rw [hΦS y i hci]; exact mul_ne_zero (inv_ne_zero hδC) hne
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
        Real.log_mul hδ.ne' (norm_ne_zero_iff.2 hΦne), Real.log_inv]
      ring
    have hsum : ∑ k ∈ kS, Real.log ‖fac k y‖ = ∑ i ∈ S, (Real.log δ - Real.log ‖Φ y i‖⁻¹) := by
      refine Finset.sum_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨h1, h2⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, k, h1, h2⟩
      · intro k₁ hk₁ k₂ hk₂ h
        have e1 := (Classical.choose_spec (Finset.mem_filter.1 hk₁).2).1
        have e2 := (Classical.choose_spec (Finset.mem_filter.1 hk₂).2).1
        rw [h] at e1
        exact hσinj k₁ k₂ _ e1 e2
      · intro i hi
        obtain ⟨k, hk, hci⟩ := (Finset.mem_filter.1 hi).2
        have hkmem : k ∈ kS := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, hci⟩
        refine ⟨k, hkmem, ?_⟩
        have e1 := (Classical.choose_spec (Finset.mem_filter.1 hkmem).2).1
        exact (Option.some_injective _ (hk.symm.trans e1)).symm
      · intro k hk
        obtain ⟨h1, h2⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
        rw [hfac_some k _ y h1]
        exact hval _ h2 ((hfac_ne k y).1 (hfk k) _ h1)
    have hFy : F y ≤ B := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hBd y (hsrcK hy))
    set Λ := ∑ i ∈ S, Real.log ‖Φ y i‖⁻¹ with hΛdef
    have hradeq : rad L s y = Real.exp 1 + F y - 2 * (S.card * Real.log δ) + 2 * Λ := by
      unfold rad
      rw [hlog, ← hsplit, hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      simp only [F]
      ring
    have hΦball : ‖Φ y‖ < 1 := by
      have := Φ.map_source hy
      rwa [hΦtgt, mem_ball, dist_zero_right] at this
    have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun i _ => by
      have hlt : ‖Φ y i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm (Φ y) i) hΦball
      rw [Real.log_inv]
      linarith [Real.log_nonpos (norm_nonneg (Φ y i)) hlt.le]
    have hT1 : Real.exp 1 ≤ Real.exp 1 + Λ := by linarith
    have hlogT : 1 ≤ Real.log (Real.exp 1 + Λ) := by
      have := Real.log_le_log (Real.exp_pos 1) hT1
      rwa [Real.log_exp] at this
    have hr_le : rad L s y ≤ (2 + B') * (Real.exp 1 + Λ) := by
      rw [hradeq]
      nlinarith [mul_nonneg hB'0 (sub_nonneg.2 he), mul_nonneg hB'0 hΛ]
    have hrpos : 0 < rad L s y := lt_of_lt_of_le (Real.exp_pos 1) (hrad y)
    calc Real.log (rad L s y) ≤ Real.log ((2 + B') * (Real.exp 1 + Λ)) :=
          Real.log_le_log hrpos hr_le
      _ = Real.log (2 + B') + Real.log (Real.exp 1 + Λ) :=
          Real.log_mul (by linarith) (by linarith [Real.exp_pos 1])
      _ ≤ (Real.log (2 + B') + 1) * Real.log (Real.exp 1 + Λ) := by
          nlinarith [mul_nonneg hlog2 (sub_nonneg.2 hlogT)]

end GlobalTheory.AdaptedChart
