import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.SumGood

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}

def GoodFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set V) (f : ι → V → E) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (f i) U) ∧
  ∀ L : Set V, IsCompact L → L ⊆ U → ∀ k : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ L, ‖iteratedFDeriv ℝ k (f i) z‖ ≤ u i

/- English proof (translation)
Take `⟨r, hr, hrU⟩` from `Metric.isOpen_iff.1 hU z hz`. Establish `hsub : Metric.closedBall z (r / 2) ⊆ U` using `(Metric.closedBall_subset_ball (by linarith)).trans hrU`. Establish `hK : IsCompact (Metric.closedBall z (r / 2))` using `isCompact_closedBall z (r / 2)`. Take `⟨u1, hu1, hb1⟩` from `hf.2 _ hK hsub 1`. Take `⟨u0, hu0, hb0⟩` from `hf.2 _ hK hsub 0`.

Establish `hzb : z ∈ Metric.ball z (r / 2)` using `Metric.mem_ball_self (by linarith)`. Use `hasFDerivAt_tsum_of_isPreconnected hu1 Metric.isOpen_ball (convex_ball z (r / 2)).isPreconnected (fun i y hy => ?_) (fun i y hy => ?_) hzb ?_ hzb` and prove the remaining obligations. Establish `hyU : y ∈ U` using `hsub (Metric.ball_subset_closedBall hy)`. Conclude with `(((hf.1 i).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).hasFDerivAt`. Use `hb1 i y (Metric.ball_subset_closedBall hy)` as an intermediate fact.

Rewrite `this` using `[norm_iteratedFDeriv_one]`. Then use the resulting hypothesis. Use `Summable.of_norm_bounded hu0 (fun i => ?_)` and prove the remaining obligations. Use `hb0 i z (Metric.mem_closedBall_self (by linarith))` as an intermediate fact. Rewrite `this` using `[norm_iteratedFDeriv_zero]`. Then use the resulting hypothesis.
-/
theorem hasFDerivAt_tsum {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) {z : V} (hz : z ∈ U) :
    HasFDerivAt (fun y => ∑' i, f i y) (∑' i, fderiv ℝ (f i) z) z := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
  have hsub : Metric.closedBall z (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrU
  have hK : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z (r / 2)
  obtain ⟨u1, hu1, hb1⟩ := hf.2 _ hK hsub 1
  obtain ⟨u0, hu0, hb0⟩ := hf.2 _ hK hsub 0
  have hzb : z ∈ Metric.ball z (r / 2) := Metric.mem_ball_self (by linarith)
  refine hasFDerivAt_tsum_of_isPreconnected hu1 Metric.isOpen_ball
    (convex_ball z (r / 2)).isPreconnected (fun i y hy => ?_) (fun i y hy => ?_) hzb ?_ hzb
  · have hyU : y ∈ U := hsub (Metric.ball_subset_closedBall hy)
    exact (((hf.1 i).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).hasFDerivAt
  · have := hb1 i y (Metric.ball_subset_closedBall hy)
    rwa [norm_iteratedFDeriv_one] at this
  · refine Summable.of_norm_bounded hu0 (fun i => ?_)
    have := hb0 i z (Metric.mem_closedBall_self (by linarith))
    rwa [norm_iteratedFDeriv_zero] at this

/- English proof (translation)
Use `⟨fun i => (hf.1 i).fderiv_of_isOpen hU (by simp), fun L hL hLU k => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hb⟩` from `hf.2 L hL hLU (k + 1)`. Conclude with `⟨u, hu, fun i z hz => by rw [norm_iteratedFDeriv_fderiv]; exact hb i z hz⟩`.
-/
theorem goodFam_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) :
    GoodFam U (fun i => fderiv ℝ (f i)) := by
  refine ⟨fun i => (hf.1 i).fderiv_of_isOpen hU (by simp), fun L hL hLU k => ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.2 L hL hLU (k + 1)
  exact ⟨u, hu, fun i z hz => by rw [norm_iteratedFDeriv_fderiv]; exact hb i z hz⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `E _ _ _ f hf`. Rewrite using `[Nat.cast_zero, contDiffOn_zero]`. Conclude with `fun z hz => (hasFDerivAt_tsum hU hf hz).continuousAt.continuousWithinAt`.

Consider the case `succ n ih`. Introduce `E _ _ _ f hf`. Rewrite using `[Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]`. Use `⟨fun z hz => (hasFDerivAt_tsum hU hf hz).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩` and prove the remaining obligations. Conclude with `(ih (goodFam_fderiv hU hf)).congr fun z hz => (hasFDerivAt_tsum hU hf hz).fderiv`.
-/
theorem contDiffOn_tsum {U : Set V} (hU : IsOpen U) (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ι → V → E},
      GoodFam U f → ContDiffOn ℝ n (fun y => ∑' i, f i y) U := by
  induction n with
  | zero =>
    intro E _ _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun z hz => (hasFDerivAt_tsum hU hf hz).continuousAt.continuousWithinAt
  | succ n ih =>
    intro E _ _ _ f hf
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun z hz => (hasFDerivAt_tsum hU hf hz).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    exact (ih (goodFam_fderiv hU hf)).congr fun z hz => (hasFDerivAt_tsum hU hf hz).fderiv

/- English proof (translation)
The claim follows from `contDiffOn_infty.2 fun n => contDiffOn_tsum hU n hf`.
-/
theorem contDiffOn_tsum_infty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) :
    ContDiffOn ℝ ∞ (fun y => ∑' i, f i y) U :=
  contDiffOn_infty.2 fun n => contDiffOn_tsum hU n hf

end General

section Wirtinger

variable {Φ : Type} [Fintype Φ] {ι : Type}

/- English proof (translation)
Use `⟨(1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ 1) + (ContinuousLinearMap.mul ℝ ℂ (if b then I else -I)).comp (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ I))), fun h z => ?_⟩` and prove the remaining obligations. Simplify using `only [wirt, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_eq_clm (τ : Φ) (b : Bool) :
    ∃ Λ : ((Φ → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ, ∀ (h : (Φ → ℂ) → ℂ) (z : Φ → ℂ),
      wirt τ b h z = Λ (fderiv ℝ h z) := by
  classical
  refine ⟨(1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ 1) +
    (ContinuousLinearMap.mul ℝ ℂ (if b then I else -I)).comp
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ I))), fun h z => ?_⟩
  simp only [wirt, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    Complex.real_smul]
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h`. Consider the case `cons a w ih => exact GoodAdd.wirt_congr hU ih a.1 a.2`.
-/
theorem wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool))
    {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons a w ih => exact GoodAdd.wirt_congr hU ih a.1 a.2

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact ⟨1, zero_le_one, fun h _ k z _ => by simp [wirtWord_nil]⟩`. Consider the case `cons a w ih`. Take `⟨C, hC0, hC⟩` from `ih`. Take `⟨Λ, hΛ⟩` from `wirt_eq_clm a.1 a.2`.

Use `⟨‖Λ‖ * C, mul_nonneg (norm_nonneg _) hC0, fun h hh k z hz => ?_⟩` and prove the remaining obligations. Establish `e : wirtWord (a :: w) h = Λ ∘ fderiv ℝ (wirtWord w h)`. Rewrite using `[wirtWord_cons]`. Use function extensionality and compare the values at `y`. Conclude with `hΛ _ y`.

Establish `hs : ContDiffOn ℝ ∞ (wirtWord w h) U` using `GoodAdd.wirtWord_contDiffOn hU w hh`. Establish `hd : ContDiffAt ℝ ∞ (fderiv ℝ (wirtWord w h)) z` using `(hs.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hz)`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[List.length_cons, show k + 1 + w.length = k + (w.length + 1) by ring]; ring`.
-/
theorem norm_iteratedFDeriv_wirtWord {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : (Φ → ℂ) → ℂ, ContDiffOn ℝ ∞ h U → ∀ k : ℕ, ∀ z ∈ U,
      ‖iteratedFDeriv ℝ k (wirtWord w h) z‖ ≤ C * ‖iteratedFDeriv ℝ (k + w.length) h z‖ := by
  induction w with
  | nil => exact ⟨1, zero_le_one, fun h _ k z _ => by simp [wirtWord_nil]⟩
  | cons a w ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨Λ, hΛ⟩ := wirt_eq_clm a.1 a.2
    refine ⟨‖Λ‖ * C, mul_nonneg (norm_nonneg _) hC0, fun h hh k z hz => ?_⟩
    have e : wirtWord (a :: w) h = Λ ∘ fderiv ℝ (wirtWord w h) := by
      rw [wirtWord_cons]; funext y; exact hΛ _ y
    have hs : ContDiffOn ℝ ∞ (wirtWord w h) U := GoodAdd.wirtWord_contDiffOn hU w hh
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ (wirtWord w h)) z :=
      (hs.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hz)
    rw [e]
    calc ‖iteratedFDeriv ℝ k (Λ ∘ fderiv ℝ (wirtWord w h)) z‖
        ≤ ‖Λ‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ (wirtWord w h)) z‖ :=
          Λ.norm_iteratedFDeriv_comp_left hd (by exact_mod_cast le_top)
      _ = ‖Λ‖ * ‖iteratedFDeriv ℝ (k + 1) (wirtWord w h) z‖ := by rw [norm_iteratedFDeriv_fderiv]
      _ ≤ ‖Λ‖ * (C * ‖iteratedFDeriv ℝ (k + 1 + w.length) h z‖) :=
          mul_le_mul_of_nonneg_left (hC h hh (k + 1) z hz) (norm_nonneg _)
      _ = ‖Λ‖ * C * ‖iteratedFDeriv ℝ (k + (a :: w).length) h z‖ := by
          rw [List.length_cons, show k + 1 + w.length = k + (w.length + 1) by ring]; ring

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `norm_iteratedFDeriv_wirtWord hU w`. Use `⟨fun i => GoodAdd.wirtWord_contDiffOn hU w (hf.1 i), fun L hL hLU k => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hb⟩` from `hf.2 L hL hLU (k + w.length)`. Use `⟨fun i => C * u i, hu.mul_left C, fun i z hz => ?_⟩` and prove the remaining obligations. Conclude with `(hC (f i) (hf.1 i) k z (hLU hz)).trans (mul_le_mul_of_nonneg_left (hb i z hz) hC0)`.
-/
theorem goodFam_wirtWord {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : ι → (Φ → ℂ) → ℂ}
    (hf : GoodFam U f) (w : List (Φ × Bool)) : GoodFam U (fun i => wirtWord w (f i)) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_wirtWord hU w
  refine ⟨fun i => GoodAdd.wirtWord_contDiffOn hU w (hf.1 i), fun L hL hLU k => ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.2 L hL hLU (k + w.length)
  refine ⟨fun i => C * u i, hu.mul_left C, fun i z hz => ?_⟩
  exact (hC (f i) (hf.1 i) k z (hLU hz)).trans (mul_le_mul_of_nonneg_left (hb i z hz) hC0)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro z _`. Both sides reduce to the same expression. Consider the case `cons a w ih`. Introduce `z hz`.

Take `⟨Λ, hΛ⟩` from `wirt_eq_clm a.1 a.2`. Establish `hg` using `goodFam_wirtWord hU hf w`. Establish `hsum : Summable (fun i => fderiv ℝ (wirtWord w (f i)) z)`. Take `⟨u, hu, hb⟩` from `hg.2 {z} isCompact_singleton (Set.singleton_subset_iff.2 hz) 1`. Conclude with `Summable.of_norm_bounded hu fun i => by`.

Simplify `hb i z (Set.mem_singleton z)` using `[norm_iteratedFDeriv_one]`. Rewrite using `[wirtWord_cons, GoodAdd.wirt_congr hU ih a.1 a.2 hz, hΛ, (hasFDerivAt_tsum hU hg hz).fderiv, Λ.map_tsum hsum]`. Simplify using `only [wirtWord_cons, hΛ]`.
-/
theorem wirtWord_tsum {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : ι → (Φ → ℂ) → ℂ}
    (hf : GoodFam U f) (w : List (Φ × Bool)) :
    Set.EqOn (wirtWord w (fun y => ∑' i, f i y)) (fun y => ∑' i, wirtWord w (f i) y) U := by
  induction w with
  | nil => intro z _; rfl
  | cons a w ih =>
    intro z hz
    obtain ⟨Λ, hΛ⟩ := wirt_eq_clm a.1 a.2
    have hg := goodFam_wirtWord hU hf w
    have hsum : Summable (fun i => fderiv ℝ (wirtWord w (f i)) z) := by
      obtain ⟨u, hu, hb⟩ := hg.2 {z} isCompact_singleton (Set.singleton_subset_iff.2 hz) 1
      exact Summable.of_norm_bounded hu fun i => by
        simpa [norm_iteratedFDeriv_one] using hb i z (Set.mem_singleton z)
    rw [wirtWord_cons, GoodAdd.wirt_congr hU ih a.1 a.2 hz, hΛ, (hasFDerivAt_tsum hU hg hz).fderiv,
      Λ.map_tsum hsum]
    simp only [wirtWord_cons, hΛ]

end Wirtinger

end GlobalTheory.HeckeTwo.SumGood

open GlobalTheory.HeckeTwo.SumGood in

/- English proof (translation)
Introduce `F _ _ ι g P h1 h2 h3 h4`. Establish `hU` using `GoodAdd.upperHalf_isOpen F`. Establish `hfam : ∀ σ ∈ halfPlane, GoodFam (upperHalf F) (fun i => g i σ)` using `fun σ hσ => ⟨fun i => h1 i σ hσ, fun L hL hLU k => by`. Take `⟨u, hu, hb⟩` from `h3 {σ} isCompact_singleton (Set.singleton_subset_iff.2 hσ) L hL hLU k`. Conclude with `⟨u, hu, fun i z hz => hb i σ rfl z hz⟩⟩`.

Establish `hPeq : ∀ σ ∈ halfPlane, Set.EqOn (P σ) (fun z => ∑' i, g i σ z) (upperHalf F)` using `fun σ hσ z hz => h4 σ hσ z hz`. Use `⟨fun σ hσ => (contDiffOn_tsum_infty hU (hfam σ hσ)).congr (hPeq σ hσ), fun w z hz => ?_⟩` and prove the remaining obligations. Establish `heq : ∀ σ ∈ halfPlane, wirtWord w (P σ) z = ∑' i, wirtWord w (g i σ) z` using `fun σ hσ => by`. Rewrite using `[wirtWord_congr hU w (hPeq σ hσ) hz]`. Conclude with `wirtWord_tsum hU (hfam σ hσ) w hz`.

Take `⟨C, hC0, hC⟩` from `norm_iteratedFDeriv_wirtWord hU w`. Establish `hHo : IsOpen (halfPlane : Set ℂ)` using `isOpen_lt continuous_const Complex.continuous_re`. Use `DifferentiableOn.congr ?_ heq` and prove the remaining obligations. Introduce `σ₀ hσ₀`. Take `⟨r, hr, hrU⟩` from `Metric.isOpen_iff.1 hHo σ₀ hσ₀`.

Establish `hsub : Metric.closedBall σ₀ (r / 2) ⊆ halfPlane` using `(Metric.closedBall_subset_ball (by linarith)).trans hrU`. Take `⟨u, hu, hb⟩` from `h3 _ (isCompact_closedBall σ₀ (r / 2)) hsub {z} isCompact_singleton (Set.singleton_subset_iff.2 hz) w.length`. Establish `hd : DifferentiableOn ℂ (fun σ => ∑' i, wirtWord w (g i σ) z) (Metric.ball σ₀ (r / 2))`. Use `differentiableOn_tsum_of_summable_norm (hu.mul_left C) (fun i => (h2 i w z hz).mono (Metric.ball_subset_closedBall.trans hsub)) Metric.isOpen_ball ?_` and prove the remaining obligations. Introduce `i σ hσ`.

Use `hC (g i σ) (h1 i σ (hsub (Metric.ball_subset_closedBall hσ))) 0 z hz` as an intermediate fact. Rewrite `this` using `[norm_iteratedFDeriv_zero, Nat.zero_add]`. Conclude with `this.trans (mul_le_mul_of_nonneg_left (hb i σ (Metric.ball_subset_closedBall hσ) z rfl) hC0)`. Conclude with `(hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith)))).differentiableWithinAt`.
-/
theorem GlobalTheory.HeckeTwo.isGood_of_tsum : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
    (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
    (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
      DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F →
      ∀ n : ℕ, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
    (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
    IsGood P := by
  intro F _ _ ι g P h1 h2 h3 h4
  have hU := GoodAdd.upperHalf_isOpen F
  have hfam : ∀ σ ∈ halfPlane, GoodFam (upperHalf F) (fun i => g i σ) := fun σ hσ =>
    ⟨fun i => h1 i σ hσ, fun L hL hLU k => by
      obtain ⟨u, hu, hb⟩ := h3 {σ} isCompact_singleton (Set.singleton_subset_iff.2 hσ) L hL hLU k
      exact ⟨u, hu, fun i z hz => hb i σ rfl z hz⟩⟩
  have hPeq : ∀ σ ∈ halfPlane, Set.EqOn (P σ) (fun z => ∑' i, g i σ z) (upperHalf F) :=
    fun σ hσ z hz => h4 σ hσ z hz
  refine ⟨fun σ hσ => (contDiffOn_tsum_infty hU (hfam σ hσ)).congr (hPeq σ hσ), fun w z hz => ?_⟩
  have heq : ∀ σ ∈ halfPlane, wirtWord w (P σ) z = ∑' i, wirtWord w (g i σ) z := fun σ hσ => by
    rw [wirtWord_congr hU w (hPeq σ hσ) hz]
    exact wirtWord_tsum hU (hfam σ hσ) w hz
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_wirtWord hU w
  have hHo : IsOpen (halfPlane : Set ℂ) := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.congr ?_ heq
  intro σ₀ hσ₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hHo σ₀ hσ₀
  have hsub : Metric.closedBall σ₀ (r / 2) ⊆ halfPlane :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrU
  obtain ⟨u, hu, hb⟩ := h3 _ (isCompact_closedBall σ₀ (r / 2)) hsub {z} isCompact_singleton
    (Set.singleton_subset_iff.2 hz) w.length
  have hd : DifferentiableOn ℂ (fun σ => ∑' i, wirtWord w (g i σ) z) (Metric.ball σ₀ (r / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (hu.mul_left C)
      (fun i => (h2 i w z hz).mono (Metric.ball_subset_closedBall.trans hsub)) Metric.isOpen_ball ?_
    intro i σ hσ
    have := hC (g i σ) (h1 i σ (hsub (Metric.ball_subset_closedBall hσ))) 0 z hz
    rw [norm_iteratedFDeriv_zero, Nat.zero_add] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hb i σ (Metric.ball_subset_closedBall hσ) z rfl) hC0)
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith)))).differentiableWithinAt
