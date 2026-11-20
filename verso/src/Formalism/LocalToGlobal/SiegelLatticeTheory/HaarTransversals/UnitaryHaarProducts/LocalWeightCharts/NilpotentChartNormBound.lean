import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartRightInverse

open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace WlocSk.NB

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `norm_nonneg _`.
-/
theorem opn_nonneg' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.L2.SG.WuDecay.opn M :=
  norm_nonneg _

/- English proof (translation)
Unfold `Formalism.L2.SG.WuDecay.opn`. Establish `h1` using `(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M).le_opNorm (EuclideanSpace.single j (1 : ℂ))`. Rewrite `h1` using `[PiLp.norm_single, norm_one, mul_one]`. Use `le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h1)` and prove the remaining obligations. Rewrite using `[← EuclideanSpace.toLp_single, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one]`.

Simplify using the standard rewrite rules.
-/
theorem entry_le_opn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖M i j‖ ≤ Formalism.L2.SG.WuDecay.opn M := by
  unfold Formalism.L2.SG.WuDecay.opn
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M).le_opNorm
    (EuclideanSpace.single j (1 : ℂ))
  rw [PiLp.norm_single, norm_one, mul_one] at h1
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h1)
  rw [← EuclideanSpace.toLp_single, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one]
  simp

/- English proof (translation)
Establish `h` using `entry_le_opn g (wI k r 0) (wI k r 0)`. Rewrite `h` using `[(colB_of_mem hg).ww 0 0, if_pos rfl, norm_one]`. Conclude with `h`.
-/
theorem one_le_opn {g : Mx k r} (hg : g ∈ Nset k r) : 1 ≤ Formalism.L2.SG.WuDecay.opn g := by
  have h := entry_le_opn g (wI k r 0) (wI k r 0)
  rw [(colB_of_mem hg).ww 0 0, if_pos rfl, norm_one] at h
  exact h

/- English proof (translation)
Rewrite using `[mof, Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, conjTranspose_apply, norm_star, sq]`. Conclude with `mul_le_mul (entry_le_opn g (esI k r c) (esI k r a)) (entry_le_opn g (eI k r c) (esI k r b)) (norm_nonneg _) (opn_nonneg' _)`. Use `_ = r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by simp`.
-/
theorem mof_le (g : Mx k r) (a b : Fin r) :
    ‖mof g a b‖ ≤ r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  rw [mof, Matrix.mul_apply]
  calc ‖∑ c, (bF g)ᴴ a c * bC g c b‖ ≤ ∑ c, ‖(bF g)ᴴ a c * bC g c b‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin r, Formalism.L2.SG.WuDecay.opn g ^ 2 := Finset.sum_le_sum fun c _ => by
        rw [norm_mul, conjTranspose_apply, norm_star, sq]
        exact mul_le_mul (entry_le_opn g (esI k r c) (esI k r a)) (entry_le_opn g (eI k r c) (esI k r b))
          (norm_nonneg _) (opn_nonneg' _)
    _ = r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by simp

/- English proof (translation)
Establish `h2 : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite using `[kof, norm_div, h2]`. Use `norm_sub_le (mof g a b) (star (mof g b a))` as an intermediate fact. Rewrite `this` using `[norm_star]`. Establish `h1` using `mof_le g a b`.

Establish `h3` using `mof_le g b a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kof_le (g : Mx k r) (a b : Fin r) :
    ‖kof g a b‖ ≤ r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [kof, norm_div, h2]
  have := norm_sub_le (mof g a b) (star (mof g b a))
  rw [norm_star] at this
  have h1 := mof_le g a b
  have h3 := mof_le g b a
  linarith

/- English proof (translation)
Use `set o := Formalism.L2.SG.WuDecay.opn g with ho`. Establish `h1 : 1 ≤ o` using `one_le_opn hg`. Establish `hoo : o ≤ o ^ 2` using `by nlinarith`. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `ho2 : 0 ≤ o ^ 2` using `sq_nonneg o`.

Break down `i with p | q | p` into its components or cases. Use `entry_le_opn g (eI k r p.1.1) (eI k r p.1.2) show ‖g _ _‖ ≤ _` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `entry_le_opn g (eI k r q.1) (wI k r q.2) show ‖g _ _‖ ≤ _` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `kof_le g p.1.1 p.1.2 show ‖kof g _ _‖ ≤ _` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem psiC_le {g : Mx k r} (hg : g ∈ Nset k r) (i : CI k r) :
    ‖psiC g i‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  set o := Formalism.L2.SG.WuDecay.opn g with ho
  have h1 : 1 ≤ o := one_le_opn hg
  have hoo : o ≤ o ^ 2 := by nlinarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ho2 : 0 ≤ o ^ 2 := sq_nonneg o
  rcases i with p | q | p
  · have := entry_le_opn g (eI k r p.1.1) (eI k r p.1.2)
    show ‖g _ _‖ ≤ _
    nlinarith
  · have := entry_le_opn g (eI k r q.1) (wI k r q.2)
    show ‖g _ _‖ ≤ _
    nlinarith
  · have := kof_le g p.1.1 p.1.2
    show ‖kof g _ _‖ ≤ _
    nlinarith

/- English proof (translation)
Establish `h` using `mof_le g a a`. Establish `h' : ‖psiR g a‖ ≤ ‖mof g a a‖`. Rewrite using `[psiR, Real.norm_eq_abs]`. Conclude with `Complex.abs_im_le_norm _`. Establish `ho2 : 0 ≤ Formalism.L2.SG.WuDecay.opn g ^ 2` using `sq_nonneg _`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem psiR_le (g : Mx k r) (a : Fin r) :
    ‖psiR g a‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  have h := mof_le g a a
  have h' : ‖psiR g a‖ ≤ ‖mof g a a‖ := by
    rw [psiR, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
  have ho2 : 0 ≤ Formalism.L2.SG.WuDecay.opn g ^ 2 := sq_nonneg _
  nlinarith

/- English proof (translation)
Use `show 1 + ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn g ^ 2`. Establish `h1 : 1 ≤ Formalism.L2.SG.WuDecay.opn g` using `one_le_opn hg`. Establish `hB : 0 ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2` using `by positivity`. Establish `hC : ‖psiC g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2` using `(pi_norm_le_iff_of_nonneg hB).2 fun i => psiC_le hg i`. Establish `hR : ‖psiR g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2` using `(pi_norm_le_iff_of_nonneg hB).2 fun a => psiR_le g a`.

Establish `hP : ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2`. Rewrite using `[Prod.norm_def]`. Conclude with `max_le hC hR`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem growth (g : Mx k r) (hg : g ∈ Nset k r) :
    1 + ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn (Matrix.of g) ^ 2 := by
  show 1 + ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn g ^ 2
  have h1 : 1 ≤ Formalism.L2.SG.WuDecay.opn g := one_le_opn hg
  have hB : 0 ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by positivity
  have hC : ‖psiC g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 :=
    (pi_norm_le_iff_of_nonneg hB).2 fun i => psiC_le hg i
  have hR : ‖psiR g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 :=
    (pi_norm_le_iff_of_nonneg hB).2 fun a => psiR_le g a
  have hP : ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
    rw [Prod.norm_def]; exact max_le hC hR
  nlinarith

/- English proof (translation)
Establish `h` using `growth (phi0 x s) (test_vector_mem_schwartz_bruhat x s)`. Rewrite `h` using `[(nilpotent_chart_right_inverse x s).1, (nilpotent_chart_right_inverse x s).2]`. Conclude with `h`.
-/
theorem nilpotent_chart_norm_bound (x : CI k r → ℂ) (s : Fin r → ℝ) :
    1 + ‖(x, s)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn (Matrix.of (phi0 x s)) ^ 2 := by
  have h := growth (phi0 x s) (test_vector_mem_schwartz_bruhat x s)
  rw [(nilpotent_chart_right_inverse x s).1, (nilpotent_chart_right_inverse x s).2] at h
  exact h

end WlocSk.NB

end
