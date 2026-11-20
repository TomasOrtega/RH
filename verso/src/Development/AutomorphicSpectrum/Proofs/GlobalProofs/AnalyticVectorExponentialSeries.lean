import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Establish `h0 : HasDerivAt (fun t : ℝ => 1 - t) (-1) s`. Simplify using `using (hasDerivAt_id s).const_sub 1`. Establish `h1 : HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1)) (((N + 1 : ℕ) : ℝ) * (1 - s) ^ (N + 1 - 1) * (-1)) s` using `h0.pow (N + 1)`. Use `(h1.div_const ((N + 1).factorial : ℝ)).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Nat.add_sub_cancel, Nat.factorial_succ]`.

Use `push_cast`. Establish `: (N.factorial : ℝ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
private theorem hasDerivAt_one_sub_pow_succ_div_factorial (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ))
      (-((1 - s) ^ N / (N.factorial : ℝ))) s := by
  have h0 : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1)) (((N + 1 : ℕ) : ℝ) * (1 - s) ^ (N + 1 - 1) * (-1)) s :=
    h0.pow (N + 1)
  refine (h1.div_const ((N + 1).factorial : ℝ)).congr_deriv ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using hf 0 s`. Consider the case `succ N ih`. Establish `h2` using `ih.add ((hasDerivAt_one_sub_pow_succ_div_factorial N s).smul (hf (N + 1) s))`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Conclude with `Finset.sum_range_succ _ _`. Rewrite using `[neg_smul]`. Normalize the expressions using the abelian group laws.
-/
private theorem hasDerivAt_sum_one_sub_pow_div_factorial_smul {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s)
    (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t)
      (((1 - s) ^ N / (N.factorial : ℝ)) • f (N + 1) s) s := by
  induction N with
  | zero => simpa using hf 0 s
  | succ N ih =>
    have h2 := ih.add ((hasDerivAt_one_sub_pow_succ_div_factorial N s).smul (hf (N + 1) s))
    convert h2 using 1
    · funext t
      exact Finset.sum_range_succ _ _
    · rw [neg_smul]
      abel

/- English proof (translation)
Set `F : ℝ → E` to `fun t => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t`. Establish `hF1 : F 1 = f 0 1`. Simplify using `[F, Finset.sum_range_succ']`. Establish `hF0 : F 0 = ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0`. Simplify using `[F]`.

Establish `hD : ∀ t, HasDerivAt F (((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t) t` using `fun t => hasDerivAt_sum_one_sub_pow_div_factorial_smul hf N t`. Establish `key` using `image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t => F t - F 0) (a := 0) (b := 1) (f' := fun t => ((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t) (B := fun t => A / ((N + 1).factorial : ℝ) - A * ((1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ))) (B' := fun t => A * ((1 …`. Establish `hc : 0 ≤ (1 - t) ^ N / (N.factorial : ℝ)`. Establish `: 0 ≤ 1 - t` using `by linarith [ht.2]`. Check the signs of the components of the expression.

Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_comm A]`. Conclude with `mul_le_mul_of_nonneg_left (hA t ⟨ht.1, ht.2.le⟩) hc)`. Establish `h1` using `key (x := 1) ⟨zero_le_one, le_rfl⟩`. Simplify using `only [hF1, hF0, sub_self, zero_pow (Nat.succ_ne_zero N), zero_div, mul_zero, sub_zero] at h1`. Conclude with `h1`.
-/
theorem norm_chain_sub_partial_le {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) (N : ℕ) {A : ℝ}
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f (N + 1) s‖ ≤ A) :
    ‖f 0 1 - ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0‖ ≤ A / ((N + 1).factorial : ℝ) := by
  let F : ℝ → E := fun t => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t
  have hF1 : F 1 = f 0 1 := by
    simp [F, Finset.sum_range_succ']
  have hF0 : F 0 = ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0 := by
    simp [F]
  have hD : ∀ t, HasDerivAt F (((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t) t :=
    fun t => hasDerivAt_sum_one_sub_pow_div_factorial_smul hf N t
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t => F t - F 0) (a := 0) (b := 1)
    (f' := fun t => ((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t)
    (B := fun t => A / ((N + 1).factorial : ℝ) - A * ((1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ)))
    (B' := fun t => A * ((1 - t) ^ N / (N.factorial : ℝ)))
    (fun t _ => ((hD t).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun t _ => ((hD t).sub_const (F 0)).hasDerivWithinAt)
    (by simp [div_eq_mul_inv])
    (fun t => (((hasDerivAt_one_sub_pow_succ_div_factorial N t).const_mul A).const_sub
      (A / ((N + 1).factorial : ℝ))).congr_deriv (by ring))
    (fun t ht => by
      have hc : 0 ≤ (1 - t) ^ N / (N.factorial : ℝ) := by
        have : 0 ≤ 1 - t := by linarith [ht.2]
        positivity
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_comm A]
      exact mul_le_mul_of_nonneg_left (hA t ⟨ht.1, ht.2.le⟩) hc)
  have h1 := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simp only [hF1, hF0, sub_self, zero_pow (Nat.succ_ne_zero N), zero_div, mul_zero, sub_zero] at h1
  exact h1

/- English proof (translation)
Establish `hn : Summable fun m : ℕ => ‖((m.factorial : ℝ)⁻¹) • f m 0‖`. Use `Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hs` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]`. Conclude with `mul_le_mul_of_nonneg_left (ha m 0 ⟨le_rfl, zero_le_one⟩) (by positivity)`. Rewrite using `[hasSum_iff_tendsto_nat_of_summable_norm hn, tendsto_iff_norm_sub_tendsto_zero]`.

Use `squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hs.tendsto_atTop_zero` and prove the remaining obligations. Use `Filter.eventually_atTop.mpr ⟨1, fun n hn1 => ?_⟩` and prove the remaining obligations. Take `⟨N, rfl⟩ : ∃ N, n = N + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[norm_sub_rev]`. Conclude with `norm_chain_sub_partial_le hf N (ha (N + 1))`.
-/
theorem hasSum_chain {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) {a : ℕ → ℝ}
    (ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m)
    (hs : Summable fun m : ℕ => a m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => ((m.factorial : ℝ)⁻¹) • f m 0) (f 0 1) := by
  have hn : Summable fun m : ℕ => ‖((m.factorial : ℝ)⁻¹) • f m 0‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (ha m 0 ⟨le_rfl, zero_le_one⟩) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hn, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hs.tendsto_atTop_zero
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn1 => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [norm_sub_rev]
  exact norm_chain_sub_partial_le hf N (ha (N + 1))

end Chain

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Conclude with `NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)`.
-/
theorem continuous_exp_smul_real {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end Exp

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}

/- English proof (translation)
Rewrite using `[add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right h)`.
-/
theorem exp_add_smul_real (X : Matrix (Fin n) (Fin n) ℂ) (s h : ℝ) :
    NormedSpace.exp ((s + h) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (h • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right h)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact hs`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `(hasDerivAt_dRep_and_isSmoothVec hG hrep ih hX).2`.
-/
theorem isSmoothVec_iterate_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H}
    (hs : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => exact hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih hX).2

/- English proof (translation)
Establish `hd` using `(hasDerivAt_dRep_and_isSmoothVec hG hrep hu hX).1`. Establish `hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G` using `hX`. Establish `heq : (fun t : ℝ => π (NormedSpace.exp (t • X)) u) = fun t => π (NormedSpace.exp (s • X)) (π (NormedSpace.exp ((t - s) • X)) u)`. Use function extensionality and compare the values at `t`. Establish `h1 : NormedSpace.exp (t • X) = NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X)`.

Rewrite using `[← exp_add_smul_real, add_sub_cancel]`. Rewrite using `[h1, hrep.2 _ (hmem s) _ (hmem (t - s))]`. Both sides reduce to the same expression. Rewrite using `[heq]`. Establish `hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (dRep π X u) (s - s)`.

Rewrite using `[sub_self]`. Conclude with `hd`. Establish `hc` using `hd'.comp_sub_const s s`. Conclude with `((π (NormedSpace.exp (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hc`.
-/
theorem hasDerivAt_orbit_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H}
    (hu : IsSmoothVec G π u) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (π (NormedSpace.exp (s • X)) (dRep π X u)) s := by
  have hd := (hasDerivAt_dRep_and_isSmoothVec hG hrep hu hX).1
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := hX
  have heq : (fun t : ℝ => π (NormedSpace.exp (t • X)) u) =
      fun t => π (NormedSpace.exp (s • X)) (π (NormedSpace.exp ((t - s) • X)) u) := by
    funext t
    have h1 : NormedSpace.exp (t • X) = NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X) := by
      rw [← exp_add_smul_real, add_sub_cancel]
    rw [h1, hrep.2 _ (hmem s) _ (hmem (t - s))]
    rfl
  rw [heq]
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (dRep π X u) (s - s) := by
    rw [sub_self]
    exact hd
  have hc := hd'.comp_sub_const s s
  exact ((π (NormedSpace.exp (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hc

/- English proof (translation)
Establish `hcont : ∀ w, ContinuousOn (fun s : ℝ => π (NormedSpace.exp (s • X)) w) (Set.Icc 0 1)`. Introduce `w`. Conclude with `(hc w).comp (continuous_exp_smul_real X).continuousOn (fun s _ => hX s)`. Establish `hb : ∀ w, ∃ C, ∀ i : Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp ((i : ℝ) • X)) w‖ ≤ C`. Introduce `w`.

Take `⟨C, hC⟩` from `isCompact_Icc.exists_bound_of_continuousOn (hcont w)`. Conclude with `⟨C, fun i => hC i i.2⟩`. Take `⟨B, hB⟩` from `banach_steinhaus (g := fun i : Set.Icc (0 : ℝ) 1 => π (NormedSpace.exp ((i : ℝ) • X))) hb`. Conclude with `⟨B, fun s hs => hB ⟨s, hs⟩⟩`.
-/
theorem exists_bound_orbit_Icc [CompleteSpace H] (hc : ∀ v, ContinuousOn (fun g => π g v) G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp (s • X))‖ ≤ B := by
  have hcont : ∀ w, ContinuousOn (fun s : ℝ => π (NormedSpace.exp (s • X)) w) (Set.Icc 0 1) := by
    intro w
    exact (hc w).comp (continuous_exp_smul_real X).continuousOn (fun s _ => hX s)
  have hb : ∀ w, ∃ C, ∀ i : Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp ((i : ℝ) • X)) w‖ ≤ C := by
    intro w
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont w)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨B, hB⟩ := banach_steinhaus (g := fun i : Set.Icc (0 : ℝ) 1 => π (NormedSpace.exp ((i : ℝ) • X))) hb
  exact ⟨B, fun s hs => hB ⟨s, hs⟩⟩

/- English proof (translation)
Establish `hfold : ∀ k, List.foldr (dRep π) v (List.replicate k X) = (dRep π X)^[k] v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']`.

Establish `h` using `hb (List.replicate m X) (fun Y hY => by rw [List.eq_of_mem_replicate hY]; exact hX)`. Rewrite `h` using `[hfold, List.length_replicate, List.map_replicate, List.prod_replicate]`. Conclude with `h`.
-/
theorem norm_iterate_dRep_le {C : ℝ}
    (hb : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ HCSS.lieOf G) →
      ‖l.foldr (dRep π) v‖ ≤ C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    ‖(dRep π X)^[m] v‖ ≤ C ^ (m + 1) * m.factorial * mnorm X ^ m := by
  have hfold : ∀ k, List.foldr (dRep π) v (List.replicate k X) = (dRep π X)^[k] v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']
  have h := hb (List.replicate m X) (fun Y hY => by rw [List.eq_of_mem_replicate hY]; exact hX)
  rw [hfold, List.length_replicate, List.map_replicate, List.prod_replicate] at h
  exact h

/- English proof (translation)
Unfold `mnorm`. Conclude with `Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _`.
-/
theorem mnorm_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X := by
  unfold mnorm
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _

/- English proof (translation)
Introduce `n G H _ _ _ π hG hrep hc v hs hw`. Take `⟨C, hC0, hC⟩` from `hw`. Use `⟨C⁻¹, inv_pos.mpr hC0, fun X hX hXr => ?_⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `exists_bound_orbit_Icc hc hX`. Set `f : ℕ → ℝ → H` to `fun m s => π (NormedSpace.exp (s • X)) ((dRep π X)^[m] v)`.

Establish `hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s`. Introduce `m s`. Use `hasDerivAt_orbit_smooth hG hrep (isSmoothVec_iterate_dRep hG hrep hs hX m) hX s` as an intermediate fact. Simplify `this` using `only [f, Function.iterate_succ_apply']`. Establish `hB0 : 0 ≤ B` using `le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)`.

Establish `hmX` using `mnorm_nonneg' X`. Set `a : ℕ → ℝ` to `fun m => B * (C ^ (m + 1) * m.factorial * mnorm X ^ m)`. Establish `ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m`. Introduce `m s hs'`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum : Summable fun m : ℕ => a m / (m.factorial : ℝ)`. Establish `heq : (fun m : ℕ => a m / (m.factorial : ℝ)) = fun m => (B * C) * (C * mnorm X) ^ m`. Use function extensionality and compare the values at `m`. Establish `: (m.factorial : ℝ) ≠ 0` using `by positivity`. Simplify using `only [a]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `Summable.mul_left _ (summable_geometric_of_lt_one (mul_nonneg hC0.le hmX) ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `key` using `hasSum_chain hf ha hsum`. Establish `h1 : f 0 1 = π (NormedSpace.exp X) v`. Simplify using `[f]`. Establish `h2 : ∀ m, f m 0 = (dRep π X)^[m] v`. Introduce `m`.

Simplify using `[f, hrep.1]`. Rewrite `key` using `[h1]`. Simplify using `only [h2] at key`. Use `key using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`.

Rewrite using `[show ((m.factorial : ℂ)⁻¹) = (((m.factorial : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.coe_smul]`.
-/
theorem hasSum_orbit_of_wordBound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) {v : H} (hs : IsSmoothVec G π v)
    (hw : WordBound G π v), ∃ r : ℝ, 0 < r ∧ ∀ X ∈ HCSS.lieOf G, mnorm X < r →
      HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (dRep π X)^[m] v) (π (NormedSpace.exp X) v) := by
  intro n G H _ _ _ π hG hrep hc v hs hw
  obtain ⟨C, hC0, hC⟩ := hw
  refine ⟨C⁻¹, inv_pos.mpr hC0, fun X hX hXr => ?_⟩
  obtain ⟨B, hB⟩ := exists_bound_orbit_Icc hc hX
  let f : ℕ → ℝ → H := fun m s => π (NormedSpace.exp (s • X)) ((dRep π X)^[m] v)
  have hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s := by
    intro m s
    have := hasDerivAt_orbit_smooth hG hrep (isSmoothVec_iterate_dRep hG hrep hs hX m) hX s
    simpa only [f, Function.iterate_succ_apply'] using this
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hmX := mnorm_nonneg' X
  let a : ℕ → ℝ := fun m => B * (C ^ (m + 1) * m.factorial * mnorm X ^ m)
  have ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m := by
    intro m s hs'
    calc ‖f m s‖ ≤ ‖π (NormedSpace.exp (s • X))‖ * ‖(dRep π X)^[m] v‖ := (π _).le_opNorm _
      _ ≤ B * (C ^ (m + 1) * m.factorial * mnorm X ^ m) :=
        mul_le_mul (hB s hs') (norm_iterate_dRep_le hC hX m) (norm_nonneg _) hB0
  have hsum : Summable fun m : ℕ => a m / (m.factorial : ℝ) := by
    have heq : (fun m : ℕ => a m / (m.factorial : ℝ)) = fun m => (B * C) * (C * mnorm X) ^ m := by
      funext m
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      simp only [a]
      field_simp
      ring
    rw [heq]
    refine Summable.mul_left _ (summable_geometric_of_lt_one (mul_nonneg hC0.le hmX) ?_)
    calc C * mnorm X < C * C⁻¹ := mul_lt_mul_of_pos_left hXr hC0
      _ = 1 := mul_inv_cancel₀ hC0.ne'
  have key := hasSum_chain hf ha hsum
  have h1 : f 0 1 = π (NormedSpace.exp X) v := by
    simp [f]
  have h2 : ∀ m, f m 0 = (dRep π X)^[m] v := by
    intro m
    simp [f, hrep.1]
  rw [h1] at key
  simp only [h2] at key
  convert key using 1
  funext m
  rw [show ((m.factorial : ℂ)⁻¹) = (((m.factorial : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.coe_smul]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
