import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StLogCoverDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

namespace LogCoverDescent

variable {n a : ℕ} (h : a ≤ n)

/- English proof (translation)
Simplify using `only [logCover, Set.mem_ofPred_eq, Pi.add_apply, Complex.add_re, hre, add_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun k hk => ?_⟩` and prove the remaining obligations. Simplify `h2 k hk` using `[hz k hk]`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun k hk => ?_⟩` and prove the remaining obligations. Simplify `h2 k hk` using `[hz k hk]`.
-/
lemma add_mem_logCover_iff {v : Fin n → ℂ} (hre : ∀ k : Fin n, (v k).re = 0)
    (hz : ∀ k : Fin n, a ≤ k.val → v k = 0) (w : Fin n → ℂ) :
    w + v ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_ofPred_eq, Pi.add_apply, Complex.add_re, hre, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk

def periods (φ : (Fin n → ℂ) → ℂ) : AddSubgroup (Fin n → ℂ) where
  carrier := {v | ∀ w, (w + v ∈ logCover h ↔ w ∈ logCover h) ∧ (w ∈ logCover h → φ (w + v) = φ w)}
  zero_mem' := fun w => by simp
  add_mem' := by
    intro u v hu hv w
    simp only [Set.mem_ofPred_eq] at hu hv
    have e : w + (u + v) = (w + u) + v := (add_assoc _ _ _).symm
    refine ⟨?_, fun hw => ?_⟩
    · rw [e, (hv _).1, (hu _).1]
    · rw [e, (hv _).2 ((hu w).1.2 hw), (hu w).2 hw]
  neg_mem' := by
    intro v hv w
    simp only [Set.mem_ofPred_eq] at hv
    have e : (w + -v) + v = w := by abel
    have key : w + -v ∈ logCover h ↔ w ∈ logCover h := by
      rw [← (hv (w + -v)).1, e]
    refine ⟨key, fun hw => ?_⟩
    have := (hv (w + -v)).2 (key.2 hw)
    rw [e] at this
    exact this.symm

variable {h}

/- English proof (translation)
Establish `hkk : Fin.castLE h ⟨k.val, hk⟩ = k` using `Fin.ext rfl`. Introduce `w`. Use `⟨add_mem_logCover_iff h (fun j => ?_) (fun j hj => ?_) w, fun hw => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hj]`. Establish `: j ≠ k` using `fun e => by subst e; omega`. Simplify using `[this]`. Use `hφ ⟨k.val, hk⟩ w hw` as an intermediate fact.

Rewrite `this` using `[hkk]`. Then use the resulting hypothesis.
-/
lemma single_mem_periods {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w)
    (k : Fin n) (hk : k.val < a) : Pi.single k (2 * Real.pi * Complex.I) ∈ periods h φ := by
  have hkk : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
  intro w
  refine ⟨add_mem_logCover_iff h (fun j => ?_) (fun j hj => ?_) w, fun hw => ?_⟩
  · by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  · have : j ≠ k := fun e => by subst e; omega
    simp [this]
  · have := hφ ⟨k.val, hk⟩ w hw
    rwa [hkk] at this

/- English proof (translation)
Rewrite using `[← Finset.univ_sum_single v]`. Use `AddSubgroup.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k.val < a`. Take `⟨m, hm⟩` from `(hv k).1 hk`. Establish `e : Pi.single k (v k) = m • (Pi.single k (2 * Real.pi * Complex.I) : Fin n → ℂ)`.

Use extensionality with `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using `[hm, zsmul_eq_mul]`. Simplify using `[hj]`.

Rewrite using `[e]`. Conclude with `AddSubgroup.zsmul_mem _ (single_mem_periods hφ k hk) m`. Rewrite using `[(hv k).2 (by omega), Pi.single_zero]`. Conclude with `AddSubgroup.zero_mem _`.
-/
lemma mem_periods_of {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {v : Fin n → ℂ}
    (hv : ∀ k : Fin n, (k.val < a → ∃ m : ℤ, v k = m * (2 * Real.pi * Complex.I)) ∧
      (a ≤ k.val → v k = 0)) :
    v ∈ periods h φ := by
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  by_cases hk : k.val < a
  · obtain ⟨m, hm⟩ := (hv k).1 hk
    have e : Pi.single k (v k) = m • (Pi.single k (2 * Real.pi * Complex.I) : Fin n → ℂ) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp [hm, zsmul_eq_mul]
      · simp [hj]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (single_mem_periods hφ k hk) m
  · rw [(hv k).2 (by omega), Pi.single_zero]
    exact AddSubgroup.zero_mem _

/- English proof (translation)
Establish `hv : w' - w ∈ periods h φ` using `mem_periods_of hφ fun k => by`. Use `⟨fun hk => ?_, fun hk => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `Complex.exp_eq_exp_iff_exists_int.1 ((hd k).1 hk)`. Conclude with `⟨m, by simp [hm]⟩`. Simplify using `[(hd k).2 hk]`.

Use `(hv w).2 hw` as an intermediate fact. Establish `e : w + (w' - w) = w'` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
lemma eq_of_exp_eq {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {w w' : Fin n → ℂ}
    (hw : w ∈ logCover h)
    (hd : ∀ k : Fin n, (k.val < a → Complex.exp (w' k) = Complex.exp (w k)) ∧
      (a ≤ k.val → w' k = w k)) :
    φ w' = φ w := by
  have hv : w' - w ∈ periods h φ := mem_periods_of hφ fun k => by
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hd k).1 hk)
      exact ⟨m, by simp [hm]⟩
    · simp [(hd k).2 hk]
  have := (hv w).2 hw
  have e : w + (w' - w) = w' := by abel
  rwa [e] at this

def branchLift (a : ℕ) (z0 z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if k.val < a then Complex.log (z k / z0 k) + Complex.log (z0 k) else z k

omit h in
/- English proof (translation)
The claim follows from `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt z`.
-/
lemma analyticAt_eval (k : Fin n) (z : Fin n → ℂ) : AnalyticAt ℂ (fun z : Fin n → ℂ => z k) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt z

/- English proof (translation)
Use `hz.2 ⟨k.val, hk⟩` as an intermediate fact. Unfold `cuspCoord at this`. Rewrite `this` using `[show Fin.castLE h ⟨k.val, hk⟩ = k from Fin.ext rfl]`. Then use the resulting hypothesis.
-/
lemma ne_zero_of_mem {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n)
    (hk : k.val < a) : z k ≠ 0 := by
  have := hz.2 ⟨k.val, hk⟩
  unfold cuspCoord at this
  rwa [show Fin.castLE h ⟨k.val, hk⟩ = k from Fin.ext rfl] at this

/- English proof (translation)
The claim follows from `(norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz.1)`.
-/
lemma norm_lt_one_of_mem {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n) :
    ‖z k‖ < 1 :=
  (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz.1)

omit h in
/- English proof (translation)
Simplify using `only [branchLift, if_pos hk]`. Rewrite using `[Complex.exp_add, Complex.exp_log (div_ne_zero hz h0), Complex.exp_log h0, div_mul_cancel₀ _ h0]`.
-/
lemma exp_branchLift {z0 z : Fin n → ℂ} {k : Fin n} (hk : k.val < a) (h0 : z0 k ≠ 0)
    (hz : z k ≠ 0) : Complex.exp (branchLift a z0 z k) = z k := by
  simp only [branchLift, if_pos hk]
  rw [Complex.exp_add, Complex.exp_log (div_ne_zero hz h0), Complex.exp_log h0,
    div_mul_cancel₀ _ h0]

/- English proof (translation)
Use `⟨fun i => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hi : (Fin.castLE h i).val < a` using `i.2`. Establish `e` using `exp_branchLift hi (ne_zero_of_mem h0 _ hi) (ne_zero_of_mem hz _ hi)`. Establish `hn` using `norm_lt_one_of_mem hz (Fin.castLE h i)`. Rewrite `hn` using `[← e, Complex.norm_exp]`.

Conclude with `Real.exp_lt_one_iff.1 hn`. Simplify using `only [branchLift, if_neg (by omega : ¬ k.val < a)]`. Conclude with `norm_lt_one_of_mem hz k`.
-/
lemma branchLift_mem {z0 z : Fin n → ℂ} (h0 : z0 ∈ puncturedChart h (ball 0 1))
    (hz : z ∈ puncturedChart h (ball 0 1)) : branchLift a z0 z ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    have e := exp_branchLift hi (ne_zero_of_mem h0 _ hi) (ne_zero_of_mem hz _ hi)
    have hn := norm_lt_one_of_mem hz (Fin.castLE h i)
    rw [← e, Complex.norm_exp] at hn
    exact Real.exp_lt_one_iff.1 hn
  · simp only [branchLift, if_neg (by omega : ¬ k.val < a)]
    exact norm_lt_one_of_mem hz k

omit h in
/- English proof (translation)
Use `AnalyticAt.pi (f := fun k z => branchLift a z0 z k) fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k.val < a`. Simplify using `only [branchLift, if_pos hk]`. Use `AnalyticAt.add (AnalyticAt.clog ?_ ?_) analyticAt_const` and prove the remaining obligations. Conclude with `(analyticAt_eval k z0).div analyticAt_const (h0 k hk)`.

Rewrite using `[div_self (h0 k hk)]`. Conclude with `Complex.one_mem_slitPlane`. Simplify using `only [branchLift, if_neg hk]`. Conclude with `analyticAt_eval k z0`.
-/
lemma analyticAt_branchLift {z0 : Fin n → ℂ} (h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0) :
    AnalyticAt ℂ (branchLift a z0) z0 := by
  refine AnalyticAt.pi (f := fun k z => branchLift a z0 z k) fun k => ?_
  by_cases hk : k.val < a
  · simp only [branchLift, if_pos hk]
    refine AnalyticAt.add (AnalyticAt.clog ?_ ?_) analyticAt_const
    · exact (analyticAt_eval k z0).div analyticAt_const (h0 k hk)
    · rw [div_self (h0 k hk)]
      exact Complex.one_mem_slitPlane
  · simp only [branchLift, if_neg hk]
    exact analyticAt_eval k z0

/- English proof (translation)
Establish `: puncturedChart h (ball (0 : Fin n → ℂ) 1) = ball 0 1 ∩ ⋂ j : Fin a, {z | z (Fin.castLE h j) ≠ 0}`. Use extensionality with `z`. Simplify using `[puncturedChart, cuspCoord]`. Rewrite using `[this]`. Conclude with `isOpen_ball.inter (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)`.
-/
lemma isOpen_puncturedChart : IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by
  have : puncturedChart h (ball (0 : Fin n → ℂ) 1) =
      ball 0 1 ∩ ⋂ j : Fin a, {z | z (Fin.castLE h j) ≠ 0} := by
    ext z; simp [puncturedChart, cuspCoord]
  rw [this]
  exact isOpen_ball.inter
    (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)

end LogCoverDescent

open LogCoverDescent in

/- English proof (translation)
Introduce `n a h φ hφa hφ`. Use `⟨fun z0 hz0 => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0` using `ne_zero_of_mem hz0`. Establish `hc : AnalyticAt ℂ (fun z => φ (branchLift a z0 z)) z0` using `(hφa _ (branchLift_mem hz0 hz0)).comp (analyticAt_branchLift h0)`. Use `hc.congr ?_` and prove the remaining obligations.

Use `filter_upwards [(isOpen_puncturedChart (h := h)).mem_nhds hz0] with z hz`. Use `symm`. Use `eq_of_exp_eq hφ (branchLift_mem hz0 hz) fun k => ⟨fun hk => ?_, fun hk => ?_⟩` and prove the remaining obligations. Rewrite using `[exp_branchLift hk (h0 k hk) (ne_zero_of_mem hz k hk)]`. Simplify using `only [logLift, if_pos hk]`.

Conclude with `Complex.exp_log (ne_zero_of_mem hz k hk)`. Simplify using `only [logLift, branchLift, if_neg (by omega : ¬ k.val < a)]`. Use `eq_of_exp_eq hφ hw fun k => ⟨fun hk => ?_, fun hk => ?_⟩` and prove the remaining obligations. Simplify using `only [logLift, expCover, if_pos hk]`. Conclude with `Complex.exp_log (Complex.exp_ne_zero _)`.

Simplify using `only [logLift, expCover, if_neg (by omega : ¬ k.val < a)]`.
-/
theorem LogCoverDescent.proof : LogCoverDescent.Statement := by
  intro n a h φ hφa hφ
  refine ⟨fun z0 hz0 => ?_, fun w hw => ?_⟩
  · have h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0 := ne_zero_of_mem hz0
    have hc : AnalyticAt ℂ (fun z => φ (branchLift a z0 z)) z0 :=
      (hφa _ (branchLift_mem hz0 hz0)).comp (analyticAt_branchLift h0)
    refine hc.congr ?_
    filter_upwards [(isOpen_puncturedChart (h := h)).mem_nhds hz0] with z hz
    symm
    refine eq_of_exp_eq hφ (branchLift_mem hz0 hz) fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [exp_branchLift hk (h0 k hk) (ne_zero_of_mem hz k hk)]
      simp only [logLift, if_pos hk]
      exact Complex.exp_log (ne_zero_of_mem hz k hk)
    · simp only [logLift, branchLift, if_neg (by omega : ¬ k.val < a)]
  · refine eq_of_exp_eq hφ hw fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · simp only [logLift, expCover, if_pos hk]
      exact Complex.exp_log (Complex.exp_ne_zero _)
    · simp only [logLift, expCover, if_neg (by omega : ¬ k.val < a)]

end

end GroundTheory.Heights₂.Heights.Regular
