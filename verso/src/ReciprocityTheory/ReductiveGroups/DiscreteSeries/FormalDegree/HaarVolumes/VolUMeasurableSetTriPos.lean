import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalA

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

/- English proof (translation)
Unfold `volU`. Conclude with `Finset.prod_pos fun i _ => by positivity`.
-/
theorem volU_pos' (M : ℕ) : 0 < volU M := by
  unfold volU
  exact Finset.prod_pos fun i _ => by positivity

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [conjTranspose_apply, Matrix.neg_apply, skMat]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `[h.ne, h.ne', h, not_lt.2 h.le]`. Simplify using the standard rewrite rules.

Simplify using `[h.ne, h.ne', h, not_lt.2 h.le]`.
-/
theorem volU_skMat_conjTranspose (x : UCo N) : (skMat x)ᴴ = -skMat x := by
  ext a b
  simp only [conjTranspose_apply, Matrix.neg_apply, skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, h.ne', h, not_lt.2 h.le]
  · simp
  · simp [h.ne, h.ne', h, not_lt.2 h.le]

/- English proof (translation)
Establish `hJ : Jm (fun _ : Fin N => true) = 1` using `by simp [Jm]`. Unfold `inUJ`. Rewrite using `[hJ, Matrix.mul_one, ← Matrix.exp_conjTranspose, volU_skMat_conjTranspose, ← Matrix.exp_add_of_commute (-skMat x) (skMat x) (Commute.refl (skMat x)).neg_left, neg_add_cancel, NormedSpace.exp_zero]`.
-/
theorem volU_exp_inUJ (x : UCo N) :
    inUJ (fun _ : Fin N => true) (NormedSpace.exp (skMat x)) := by
  have hJ : Jm (fun _ : Fin N => true) = 1 := by simp [Jm]
  unfold inUJ
  rw [hJ, Matrix.mul_one, ← Matrix.exp_conjTranspose, volU_skMat_conjTranspose,
    ← Matrix.exp_add_of_commute (-skMat x) (skMat x) (Commute.refl (skMat x)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [skMat]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `only [h.ne, h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true] fun_prop`. Simplify using `only [if_true] fun_prop`.

Simplify using `only [h.ne', h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true] fun_prop`.
-/
theorem volU_continuous_skMat : Continuous (skMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h.ne, h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop
  · simp only [if_true]
    fun_prop
  · simp only [h.ne', h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop

/- English proof (translation)
Introduce `x y h`. Establish `h1 : ∀ a b, skMat x a b = skMat y a b` using `fun a b => by rw [h]`. Use `Prod.ext (funext fun a => ?_) (funext fun ab => ?_)` and prove the remaining obligations. Simplify `h1 a a` using `[skMat, Complex.I_ne_zero]`. Take `⟨⟨a, b⟩, hab⟩` from `ab`.

Simplify `h1 a b` using `[skMat, hab.ne', hab]`.
-/
theorem volU_skMat_injective : Function.Injective (skMat (N := N)) := by
  intro x y h
  have h1 : ∀ a b, skMat x a b = skMat y a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · simpa [skMat, Complex.I_ne_zero] using h1 a a
  · obtain ⟨⟨a, b⟩, hab⟩ := ab
    simpa [skMat, hab.ne', hab] using h1 a b

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[skMat]`.
-/
theorem volU_skMat_zero : skMat (0 : UCo N) = 0 := by
  ext a b
  simp [skMat]

/- English proof (translation)
Take `⟨ℓ, -, -, hℓ⟩` from `lcA_exists_log (n := N)`. Establish `hc : Tendsto (skMat (N` using `N)) (𝓝 0) (𝓝 0) := by`. Use `(volU_continuous_skMat (N := N)).tendsto 0` as an intermediate fact. Rewrite `this` using `[volU_skMat_zero]`. Then use the resulting hypothesis. Take `⟨δ, hδ, hδ'⟩` from `Metric.eventually_nhds_iff.1 (hc.eventually hℓ)`.

Use `⟨δ, hδ, fun x hx y hy hxy => volU_skMat_injective ?_⟩` and prove the remaining obligations. Establish `ex` using `hδ' (Metric.mem_ball.1 hx)`. Establish `ey` using `hδ' (Metric.mem_ball.1 hy)`. Simplify using `only at hxy ex ey`. Rewrite using `[← ex, ← ey, hxy]`.
-/
theorem volU_exp_injOn : ∃ δ > 0, Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x))
    (Metric.ball 0 δ) := by
  obtain ⟨ℓ, -, -, hℓ⟩ := lcA_exists_log (n := N)
  have hc : Tendsto (skMat (N := N)) (𝓝 0) (𝓝 0) := by
    have := (volU_continuous_skMat (N := N)).tendsto 0
    rwa [volU_skMat_zero] at this
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hc.eventually hℓ)
  refine ⟨δ, hδ, fun x hx y hy hxy => volU_skMat_injective ?_⟩
  have ex := hδ' (Metric.mem_ball.1 hx)
  have ey := hδ' (Metric.mem_ball.1 hy)
  simp only at hxy ex ey
  rw [← ex, ← ey, hxy]

def volUOne (N : ℕ) : TriCo N := (fun _ => 1, 0)

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[upMat, volUOne, add_comm]`. Simplify using `[upMat, volUOne, h]`.
-/
theorem volU_upMat_add (t : TriCo N) : upMat (t + volUOne N) = 1 + upMat t := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [upMat, volUOne, add_comm]
  · simp [upMat, volUOne, h]

/- English proof (translation)
Simplify using `[qrWt, volUOne]`.
-/
theorem volU_qrWt_one : qrWt (volUOne N) = 1 := by
  simp [qrWt, volUOne]

/- English proof (translation)
The claim follows from `continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_fst).pow _`.
-/
theorem volU_continuous_qrWt : Continuous (qrWt (N := N)) :=
  continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_fst).pow _

/- English proof (translation)
Introduce `t ht j`. Rewrite `ht` using `[Metric.mem_ball, dist_eq_norm]`. Establish `h1 : ‖(t - volUOne N).1 j‖ ≤ ‖t - volUOne N‖` using `(norm_le_pi_norm _ j).trans (norm_fst_le _)`. Establish `h2 : (t - volUOne N).1 j = t.1 j - 1` using `by simp [volUOne]`. Rewrite `h1` using `[h2, Real.norm_eq_abs]`.

Combine the linear relations using `[neg_le_abs (t.1 j - 1)]`.
-/
theorem volU_ball_sub_triPos {ρ : ℝ} (hρ : ρ ≤ 1) : Metric.ball (volUOne N) ρ ⊆ triPos N := by
  intro t ht j
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have h1 : ‖(t - volUOne N).1 j‖ ≤ ‖t - volUOne N‖ :=
    (norm_le_pi_norm _ j).trans (norm_fst_le _)
  have h2 : (t - volUOne N).1 j = t.1 j - 1 := by simp [volUOne]
  rw [h2, Real.norm_eq_abs] at h1
  linarith [neg_le_abs (t.1 j - 1)]

/- English proof (translation)
Simplify using `only [triPos, Set.ofPred_forall]`. Conclude with `MeasurableSet.iInter fun j => measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)`.
-/
theorem volU_measurableSet_triPos : MeasurableSet (triPos N) := by
  simp only [triPos, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

end ReciprocityTheory.ChartRestriction.DS
