import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.ContinuousSecondMatrix

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

namespace CurveContinuity

open Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Der

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
variable {u : Fin k → ℝ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
  {c : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)}

/- English proof (translation)
Establish `hm` using `aesm_int hP hB hx ξ G hG 1 (one_inUJ ε)`. Simplify using `only [Matrix.mul_one] at hm`. Use `Integrable.mono' ((int_bound hP hB hx a hb).const_mul (|CG| * ‖ξ‖)) hm ?_` and prove the remaining obligations. Use `filter_upwards [ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2] with p hp`. Rewrite using `[norm_smul, chi_norm hB hp.1]`.

Establish `hJ` using `inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)`. Establish `h1` using `hCG _ hJ`. Use `set y := frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a) with hy`. Establish `h2 : 0 ≤ y` using `Real.rpow_nonneg (frob_nonneg _) _`. Establish `h3 : CG * y ≤ |CG| * y` using `mul_le_mul_of_nonneg_right (le_abs_self CG) h2`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem int_of_bound {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (ξ : Vp) (a : ℝ)
    (hb : S0.bS k r < a - 1) (G : Mat k r → ℂ) (hG : ContinuousOn G (UJset ε)) (CG : ℝ)
    (hCG : ∀ g ∈ UJset ε, ‖G g‖ ≤ CG * frob g ^ (1 - a)) :
    Integrable (fun p : Mt k r × Mt k r => G (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) := by
  have hm := aesm_int hP hB hx ξ G hG 1 (one_inUJ ε)
  simp only [Matrix.mul_one] at hm
  refine Integrable.mono' ((int_bound hP hB hx a hb).const_mul (|CG| * ‖ξ‖)) hm ?_
  filter_upwards [ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2] with p hp
  rw [norm_smul, chi_norm hB hp.1]
  have hJ := inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)
  have h1 := hCG _ hJ
  set y := frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a) with hy
  have h2 : 0 ≤ y := Real.rpow_nonneg (frob_nonneg _) _
  have h3 : CG * y ≤ |CG| * y := mul_le_mul_of_nonneg_right (le_abs_self CG) h2
  calc ‖G (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)‖ * ‖ξ‖ ≤ (|CG| * y) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right (h1.trans h3) (norm_nonneg _)
    _ = |CG| * ‖ξ‖ * y := by ring_nf

/- English proof (translation)
Establish `hFc` using `smooth_contOn hF`. Establish `hRc` using `smooth_contOn (Formalism.REAL.rdSmooth _ ε F X hF hX)`. Establish `h0 : ∀ g : Mat k r, g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g` using `fun g => by`. Simplify using `[NormedSpace.exp_zero]`. Take `⟨M, hM⟩` from `(isCompact_closedBall (0 : ℝ) 1).exists_bound_of_continuousOn ((frob_cont.comp ((curve_cont X).comp (continuous_const.sub continuous_id))).continuousOn (s := Metric.closedBall (0 : ℝ) 1))`.

Use `set M' := max M 1 with hM'def`. Establish `hM' : ∀ t ∈ Metric.ball (0 : ℝ) 1, frob (NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) ≤ M'`. Introduce `t ht`. Use `hM t (Metric.ball_subset_closedBall ht)` as an intermediate fact. Simplify using `only [Function.comp] at this`.

Rewrite `this` using `[Real.norm_of_nonneg (frob_nonneg _)]`. Conclude with `this.trans (le_max_left _ _)`. Establish `hM'0 : 0 < M'` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Establish `ha1 : 1 ≤ a` using `by linarith [bS_nonneg (k := k) (r := r)]`. Establish `hn : 0 < 2 * r + k + 1` using `by omega`.

Establish `hsupp` using `ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μW.prod μN) (x₀ := (0 : ℝ)) (F := fun (t : ℝ) (p : Mt k r × Mt k r) => F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) • chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Mat …`. Simplify using `only [h0] at key`. Conclude with `key`. Use `filter_upwards [hsupp] with p hp t ht set g := P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ with hg`.

Establish `hJ : Formalism.REAL.inUJ ε g` using `inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)`. Establish `hJt : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((t : ℂ) • X))` using `Formalism.REAL.indefinite_unitary_mul_mem ε hJ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t)`. Rewrite using `[norm_smul, chi_norm hB hp.1]`. Establish `hg0 : 0 < frob g` using `frob_pos _ (ne_zero_of_inUJ hn hJ)`. Establish `hprod : g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X) = g`.

Rewrite using `[Matrix.mul_assoc, ← exp_shift X t 0]`. Simplify using `[NormedSpace.exp_zero]`. Establish `hle0 : frob g ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * M'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hprod]`.

Use `_ ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * frob (NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) := frob_mul_le _ _`. Use `_ ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * M' := mul_le_mul_of_nonneg_left (hM' t ht) (frob_nonneg _)`. Establish `hle : frob g / M' ≤ frob (g * NormedSpace.exp ((t : ℂ) • X))`. Rewrite using `[div_le_iff₀ hM'0]`. Conclude with `hle0`.

Establish `hpow : frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) ≤ M' ^ (a - 1) * frob g ^ (1 - a)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.div_rpow hg0.le hM'0.le, div_eq_mul_inv, ← Real.rpow_neg hM'0.le, neg_sub, mul_comm]`. Establish `h1` using `hCX _ hJt`. Use `set y := frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) with hy`.

Establish `h2 : 0 ≤ y` using `Real.rpow_nonneg (frob_nonneg _) _`. Establish `h3 : CX * y ≤ |CX| * y` using `mul_le_mul_of_nonneg_right (le_abs_self CX) h2`. Establish `h4 : |CX| * y ≤ |CX| * (M' ^ (a - 1) * frob g ^ (1 - a))` using `mul_le_mul_of_nonneg_left hpow (abs_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Use `filter_upwards [hsupp] with p hp t _`.

Establish `hJ : Formalism.REAL.inUJ ε (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)` using `inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)`. Conclude with `(hasDeriv_curve_at hF hJ hX t).smul_const _`.
-/
theorem deriv_int {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (ξ : Vp) (a : ℝ)
    (hb : S0.bS k r < a - 1) (F : Mat k r → ℂ) (hF : Formalism.REAL.SmoothOnG ε F) (C0 : ℝ)
    (hC0 : ∀ g ∈ UJset ε, ‖F g‖ ≤ C0 * frob g ^ (1 - a))
    (X : Mat k r) (hX : Formalism.REAL.inG ε X) (CX : ℝ)
    (hCX : ∀ g ∈ UJset ε, ‖Formalism.REAL.Rd X F g‖ ≤ CX * frob g ^ (1 - a)) :
    Integrable (fun p : Mt k r × Mt k r => Formalism.REAL.Rd X F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) ∧
    HasDerivAt (fun t : ℝ => ∫ p : Mt k r × Mt k r,
        F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN))
      (∫ p : Mt k r × Mt k r, Formalism.REAL.Rd X F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN)) 0 := by
  have hFc := smooth_contOn hF
  have hRc := smooth_contOn (Formalism.REAL.rdSmooth _ ε F X hF hX)
  have h0 : ∀ g : Mat k r, g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := fun g => by
    simp [NormedSpace.exp_zero]
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ) 1).exists_bound_of_continuousOn
    ((frob_cont.comp ((curve_cont X).comp (continuous_const.sub continuous_id))).continuousOn
      (s := Metric.closedBall (0 : ℝ) 1))
  set M' := max M 1 with hM'def
  have hM' : ∀ t ∈ Metric.ball (0 : ℝ) 1, frob (NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) ≤ M' := by
    intro t ht
    have := hM t (Metric.ball_subset_closedBall ht)
    simp only [Function.comp] at this
    rw [Real.norm_of_nonneg (frob_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have ha1 : 1 ≤ a := by linarith [bS_nonneg (k := k) (r := r)]
  have hn : 0 < 2 * r + k + 1 := by omega
  have hsupp := ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μW.prod μN) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) (p : Mt k r × Mt k r) =>
      F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
    (F' := fun (t : ℝ) (p : Mt k r × Mt k r) =>
      Formalism.REAL.Rd X F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
    (bound := fun p => (|CX| * ‖ξ‖ * M' ^ (a - 1)) * frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun t => aesm_int hP hB hx ξ F hFc _ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t))
    (by simp only [h0]; exact int_of_bound hP hB hx ξ a hb F hFc C0 hC0)
    (aesm_int hP hB hx ξ _ hRc _ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX 0))
    ?_ ((int_bound hP hB hx a hb).const_mul _) ?_
  · simp only [h0] at key
    exact key
  · filter_upwards [hsupp] with p hp t ht
    set g := P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ with hg
    have hJ : Formalism.REAL.inUJ ε g := inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)
    have hJt : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) :=
      Formalism.REAL.indefinite_unitary_mul_mem ε hJ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t)
    rw [norm_smul, chi_norm hB hp.1]
    have hg0 : 0 < frob g := frob_pos _ (ne_zero_of_inUJ hn hJ)
    have hprod : g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X) = g := by
      rw [Matrix.mul_assoc, ← exp_shift X t 0]
      simp [NormedSpace.exp_zero]
    have hle0 : frob g ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * M' := by
      calc frob g = frob (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) := by
            rw [hprod]
        _ ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * frob (NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) :=
            frob_mul_le _ _
        _ ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * M' :=
            mul_le_mul_of_nonneg_left (hM' t ht) (frob_nonneg _)
    have hle : frob g / M' ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) := by
      rw [div_le_iff₀ hM'0]; exact hle0
    have hpow : frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) ≤ M' ^ (a - 1) * frob g ^ (1 - a) := by
      calc frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) ≤ (frob g / M') ^ (1 - a) :=
            Real.rpow_le_rpow_of_nonpos (div_pos hg0 hM'0) hle (by linarith)
        _ = M' ^ (a - 1) * frob g ^ (1 - a) := by
            rw [Real.div_rpow hg0.le hM'0.le, div_eq_mul_inv, ← Real.rpow_neg hM'0.le, neg_sub, mul_comm]
    have h1 := hCX _ hJt
    set y := frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) with hy
    have h2 : 0 ≤ y := Real.rpow_nonneg (frob_nonneg _) _
    have h3 : CX * y ≤ |CX| * y := mul_le_mul_of_nonneg_right (le_abs_self CX) h2
    have h4 : |CX| * y ≤ |CX| * (M' ^ (a - 1) * frob g ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    calc ‖Formalism.REAL.Rd X F (g * NormedSpace.exp ((t : ℂ) • X))‖ * ‖ξ‖
        ≤ (|CX| * (M' ^ (a - 1) * frob g ^ (1 - a))) * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right ((h1.trans h3).trans h4) (norm_nonneg _)
      _ = |CX| * ‖ξ‖ * M' ^ (a - 1) * frob g ^ (1 - a) := by ring_nf
  · filter_upwards [hsupp] with p hp t _
    have hJ : Formalism.REAL.inUJ ε (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
      inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)
    exact (hasDeriv_curve_at hF hJ hX t).smul_const _

end Der

def sg {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℝ := (if ε a then 1 else -1) * (if ε b then 1 else -1)

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> push_cast <;> ring_nf`.
-/
theorem sg_sq {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ((sg ε a b : ℝ) : ℂ) * (sg ε a b : ℂ) = 1 := by
  unfold sg; split_ifs <;> push_cast <;> ring_nf

/- English proof (translation)
Unfold `sg`. Put the polynomial expressions in normal form.
-/
theorem sg_comm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : sg ε b a = sg ε a b := by
  unfold sg; ring_nf

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> simp`.
-/
theorem sg_norm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ‖((sg ε a b : ℝ) : ℂ)‖ = 1 := by
  unfold sg; split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.conjTranspose_single, star_one, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]`. Distinguish the cases in `h : b = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `h`.

Rewrite using `[Matrix.single_apply_same]`. Unfold `sg`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring_nf`. Simplify using `only [Matrix.single_apply, if_neg h, mul_zero, zero_mul]`.
-/
theorem jsj {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm ε = ((sg ε a b : ℝ) : ℂ) • Matrix.single b a 1 := by
  ext i j
  unfold Formalism.REAL.Jm
  rw [Matrix.conjTranspose_single, star_one, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same]
    unfold sg
    split_ifs <;> push_cast <;> ring_nf
  · simp only [Matrix.single_apply, if_neg h, mul_zero, zero_mul]

/- English proof (translation)
Unfold `Formalism.REAL.cpart1`. Rewrite using `[jsj ε b a, jsj ε a b, sg_comm]`. Establish `hs` using `sg_sq ε a b`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`.

Use `push_cast`. Take the linear combination `(-(1 / 2) * (Matrix.single b a (1 : ℂ) i j)) * hs`.
-/
theorem cpart1_rel {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.cpart1 ε (Matrix.single b a 1) = ((-sg ε a b : ℝ) : ℂ) • Formalism.REAL.cpart1 ε (Matrix.single a b 1) := by
  unfold Formalism.REAL.cpart1
  rw [jsj ε b a, jsj ε a b, sg_comm]
  have hs := sg_sq ε a b
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  push_cast
  linear_combination (-(1 / 2) * (Matrix.single b a (1 : ℂ) i j)) * hs

/- English proof (translation)
Unfold `Formalism.REAL.cpart2`. Rewrite using `[jsj ε b a, jsj ε a b, sg_comm]`. Establish `hs` using `sg_sq ε a b`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]`.

Take the linear combination `(-(1 / (2 * Complex.I)) * (Matrix.single b a (1 : ℂ) i j)) * hs`.
-/
theorem cpart2_rel {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.cpart2 ε (Matrix.single b a 1) = ((sg ε a b : ℝ) : ℂ) • Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
  unfold Formalism.REAL.cpart2
  rw [jsj ε b a, jsj ε a b, sg_comm]
  have hs := sg_sq ε a b
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  linear_combination (-(1 / (2 * Complex.I)) * (Matrix.single b a (1 : ℂ) i j)) * hs

/- English proof (translation)
Use `set R1 := Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F g`. Use `set R2 := Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F g`. Use `set s : ℂ := ((sg ε a b : ℝ) : ℂ) with hsdef`. Establish `hs` using `sg_sq ε a b`. Establish `hE1 : Formalism.REAL.Eab ε a b F g = R1 + Complex.I * R2` using `rfl`.

Establish `hE2 : Formalism.REAL.Eab ε b a F g = -s * R1 + Complex.I * (s * R2)` using `by show Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single b a 1)) F g + Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single b a 1)) F g = _`. Rewrite using `[cpart1_rel, cpart2_rel, rd_smul, rd_smul]`. Simplify using `only [R1, R2, s]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hR1 : 2 * R1 = Formalism.REAL.Eab ε a b F g - s * Formalism.REAL.Eab ε b a F g`. Rewrite using `[hE1, hE2]`. Take the linear combination `(Complex.I * R2 - R1) * hs`. Establish `hR2 : (2 * Complex.I) * R2 = Formalism.REAL.Eab ε a b F g + s * Formalism.REAL.Eab ε b a F g`. Rewrite using `[hE1, hE2]`.

Take the linear combination `(R1 - Complex.I * R2) * hs`. Establish `hsn : ‖s‖ = 1` using `sg_norm ε a b`. Prove the components needed by the constructor for the conclusion. Establish `h` using `congrArg norm hR1`. Rewrite `h` using `[norm_mul, Complex.norm_ofNat]`.

Use `norm_sub_le (Formalism.REAL.Eab ε a b F g) (s * Formalism.REAL.Eab ε b a F g)` as an intermediate fact. Rewrite `this` using `[norm_mul, hsn, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `congrArg norm hR2`. Rewrite `h` using `[norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]`.

Use `norm_add_le (Formalism.REAL.Eab ε a b F g) (s * Formalism.REAL.Eab ε b a F g)` as an intermediate fact. Rewrite `this` using `[norm_mul, hsn, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rd_bounds {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F g‖ ≤
              (‖Formalism.REAL.Eab ε a b F g‖ + ‖Formalism.REAL.Eab ε b a F g‖) / 2 ∧
      ‖Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F g‖ ≤
        (‖Formalism.REAL.Eab ε a b F g‖ + ‖Formalism.REAL.Eab ε b a F g‖) / 2 := by
  set R1 := Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F g
  set R2 := Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F g
  set s : ℂ := ((sg ε a b : ℝ) : ℂ) with hsdef
  have hs := sg_sq ε a b
  have hE1 : Formalism.REAL.Eab ε a b F g = R1 + Complex.I * R2 := rfl
  have hE2 : Formalism.REAL.Eab ε b a F g = -s * R1 + Complex.I * (s * R2) := by
    show Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single b a 1)) F g +
      Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single b a 1)) F g = _
    rw [cpart1_rel, cpart2_rel, rd_smul, rd_smul]
    simp only [R1, R2, s]
    push_cast
    ring
  have hR1 : 2 * R1 = Formalism.REAL.Eab ε a b F g - s * Formalism.REAL.Eab ε b a F g := by
    rw [hE1, hE2]; linear_combination (Complex.I * R2 - R1) * hs
  have hR2 : (2 * Complex.I) * R2 = Formalism.REAL.Eab ε a b F g + s * Formalism.REAL.Eab ε b a F g := by
    rw [hE1, hE2]; linear_combination (R1 - Complex.I * R2) * hs
  have hsn : ‖s‖ = 1 := sg_norm ε a b
  constructor
  · have h := congrArg norm hR1
    rw [norm_mul, Complex.norm_ofNat] at h
    have := norm_sub_le (Formalism.REAL.Eab ε a b F g) (s * Formalism.REAL.Eab ε b a F g)
    rw [norm_mul, hsn, one_mul] at this
    linarith
  · have h := congrArg norm hR2
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one] at h
    have := norm_add_le (Formalism.REAL.Eab ε a b F g) (s * Formalism.REAL.Eab ε b a F g)
    rw [norm_mul, hsn, one_mul] at this
    linarith

/- English proof (translation)
Establish `h2` using `hgap.2`. Establish `hq0 : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ)` using `by unfold S7.q0; norm_cast`. Establish `hB0 : S0.bS k r = 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `rfl`. Establish `hle : 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)` using `le_max_right _ _`. Establish `h0 : 0 ≤ 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`.

Unfold `aExp`. Rewrite using `[hq0, hB0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem per_gap {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hgap : StepGap ε r h) :
    S0.bS k r < aExp ε h - 1 := by
  have h2 := hgap.2
  have hq0 : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ) := by unfold S7.q0; norm_cast
  have hB0 : S0.bS k r = 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := rfl
  have hle : 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤
      max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) :=
    le_max_right _ _
  have h0 : 0 ≤ 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  unfold aExp
  rw [hq0, hB0]
  linarith

end CurveContinuity

open CurveContinuity in
/- English proof (translation)
Introduce `k r ε u h z c Vp _ _ _ π μW μN P hP hB _ _ hgap`. Establish `hb` using `per_gap hgap`. Use `⟨fun F C hFc hFb x hx ξ => int_of_bound hP hB hx ξ (aExp ε h) hb F hFc C hFb, ?_⟩` and prove the remaining obligations. Introduce `F hF hW a b x hx ξ`. Take `⟨C0, hC0⟩` from `hW []`.

Take `⟨C1, hC1⟩` from `hW [(a, b)]`. Take `⟨C2, hC2⟩` from `hW [(b, a)]`. Establish `hC1' : ∀ g ∈ UJset ε, ‖Formalism.REAL.Eab ε a b F g‖ ≤ C1 * frob g ^ (1 - aExp ε h)` using `hC1`. Establish `hC2' : ∀ g ∈ UJset ε, ‖Formalism.REAL.Eab ε b a F g‖ ≤ C2 * frob g ^ (1 - aExp ε h)` using `hC2`. Establish `hC0' : ∀ g ∈ UJset ε, ‖F g‖ ≤ C0 * frob g ^ (1 - aExp ε h)` using `hC0`.

Establish `hcm` using `Formalism.REAL.cpartMem _ ε (Matrix.single a b 1)`. Establish `hR : ∀ i : Fin 2, ∀ g ∈ UJset ε, ‖Formalism.REAL.Rd ((if i = 0 then Formalism.REAL.cpart1 else Formalism.REAL.cpart2) ε (Matrix.single a b 1)) F g‖ ≤ ((C1 + C2) / 2) * frob g ^ (1 - aExp ε h)`. Introduce `i g hg`. Establish `hrb` using `rd_bounds ε a b F g`. Establish `h1` using `hC1' g hg`.

Establish `h2` using `hC2' g hg`. Establish `: (‖Formalism.REAL.Eab ε a b F g‖ + ‖Formalism.REAL.Eab ε b a F g‖) / 2 ≤ ((C1 + C2) / 2) * frob g ^ (1 - aExp ε h)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `fin_cases i`. Conclude with `hrb.1.trans this`.

Conclude with `hrb.2.trans this`. Take `⟨hi1, hd1⟩` from `deriv_int hP hB hx ξ (aExp ε h) hb F hF C0 hC0' _ hcm.1 _ (hR 0)`. Take `⟨hi2, hd2⟩` from `deriv_int hP hB hx ξ (aExp ε h) hb F hF C0 hC0' _ hcm.2.1 _ (hR 1)`. Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP.1`. Establish `hΦ : ∀ (X : Mat k r) (t : ℝ), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P) = ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ …`.

Introduce `X t`. Unfold `per sInt`. Use `integral_congr_ae (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `only`. Use `congr 2`.

Simplify using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv _ hd]`. Use `show (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, (Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) + Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a …`. Simplify using `only [hΦ]`. Rewrite using `[hd1.deriv, hd2.deriv, ← integral_smul, ← integral_add hi1 ?hI2]`. Use `integral_congr_ae (Eventually.of_forall fun p => ?_)` and prove the remaining obligations.

Simplify using `only [add_smul, mul_smul]`. Conclude with `hi2.smul Complex.I`.
-/
theorem per_spec : PerStatement := by
  intro k r ε u h z c Vp _ _ _ π μW μN P hP hB _ _ hgap
  have hb := per_gap hgap
  refine ⟨fun F C hFc hFb x hx ξ => int_of_bound hP hB hx ξ (aExp ε h) hb F hFc C hFb, ?_⟩
  intro F hF hW a b x hx ξ
  obtain ⟨C0, hC0⟩ := hW []
  obtain ⟨C1, hC1⟩ := hW [(a, b)]
  obtain ⟨C2, hC2⟩ := hW [(b, a)]
  have hC1' : ∀ g ∈ UJset ε, ‖Formalism.REAL.Eab ε a b F g‖ ≤ C1 * frob g ^ (1 - aExp ε h) := hC1
  have hC2' : ∀ g ∈ UJset ε, ‖Formalism.REAL.Eab ε b a F g‖ ≤ C2 * frob g ^ (1 - aExp ε h) := hC2
  have hC0' : ∀ g ∈ UJset ε, ‖F g‖ ≤ C0 * frob g ^ (1 - aExp ε h) := hC0
  have hcm := Formalism.REAL.cpartMem _ ε (Matrix.single a b 1)
  have hR : ∀ i : Fin 2, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Rd ((if i = 0 then Formalism.REAL.cpart1 else Formalism.REAL.cpart2) ε (Matrix.single a b 1)) F g‖ ≤
        ((C1 + C2) / 2) * frob g ^ (1 - aExp ε h) := by
    intro i g hg
    have hrb := rd_bounds ε a b F g
    have h1 := hC1' g hg
    have h2 := hC2' g hg
    have : (‖Formalism.REAL.Eab ε a b F g‖ + ‖Formalism.REAL.Eab ε b a F g‖) / 2 ≤ ((C1 + C2) / 2) * frob g ^ (1 - aExp ε h) := by
      linarith
    fin_cases i
    · exact hrb.1.trans this
    · exact hrb.2.trans this
  obtain ⟨hi1, hd1⟩ := deriv_int hP hB hx ξ (aExp ε h) hb F hF C0 hC0' _ hcm.1 _ (hR 0)
  obtain ⟨hi2, hd2⟩ := deriv_int hP hB hx ξ (aExp ε h) hb F hF C0 hC0' _ hcm.2.1 _ (hR 1)
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hΦ : ∀ (X : Mat k r) (t : ℝ),
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P) =
        ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
          F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
            chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN) := by
    intro X t
    unfold per sInt
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    congr 2
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv _ hd]
  show (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) +
        Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F
          (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN)) =
    deriv (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ
        (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • Formalism.REAL.cpart1 ε (Matrix.single a b 1))) * P)) 0 +
      Complex.I • deriv (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ
        (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • Formalism.REAL.cpart2 ε (Matrix.single a b 1))) * P)) 0
  simp only [hΦ]
  rw [hd1.deriv, hd2.deriv, ← integral_smul, ← integral_add hi1 ?hI2]
  · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [add_smul, mul_smul]
  · exact hi2.smul Complex.I

end ReciprocityTheory.ChartRestriction.DS.Lap
