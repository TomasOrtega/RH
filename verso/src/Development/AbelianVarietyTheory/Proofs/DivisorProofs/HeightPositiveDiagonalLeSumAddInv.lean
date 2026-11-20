import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

/- English proof (translation)
Establish `hinv : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => (((r i)⁻¹ : ℝ) : ℂ))`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i w`.

Establish `: (r i : ℂ) ≠ 0` using `by exact_mod_cast (hr i).ne'`. Simplify using `[this]`. Establish `key : ∀ s : Fin a → ℝ, (∀ i, 0 < s i) → ‖toL (Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ)))‖ ≤ ∑ i, s i`. Introduce `s hs`. Establish `h0 : 0 ≤ ∑ i, s i` using `Finset.sum_nonneg fun i _ => (hs i).le`.

Use `(pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖(Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ))) i j w‖ ≤ _`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs i)]`.

Conclude with `Finset.single_le_sum (fun k _ => (hs k).le) (Finset.mem_univ i)`. Rewrite using `[Matrix.diagonal_apply_ne _ hij]`. Simplify using `using h0`. Establish `h1` using `key r hr`. Establish `h2` using `key (fun i => (r i)⁻¹) (fun i => inv_pos.2 (hr i))`.

Unfold `GlobalTheory.CuspRep.height`. Rewrite using `[hd, hinv]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem height_diagonal_le_sum (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (d : GL (Fin a) (Cinf E)) (hr : ∀ i, 0 < r i)
    (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ))) :
    height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  classical
  have hinv : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => (((r i)⁻¹ : ℝ) : ℂ)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
    simp [this]
  have key : ∀ s : Fin a → ℝ, (∀ i, 0 < s i) →
      ‖toL (Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ)))‖ ≤ ∑ i, s i := by
    intro s hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => (hs i).le
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
      (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
    change ‖(Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ))) i j w‖ ≤ _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs i)]
      exact Finset.single_le_sum (fun k _ => (hs k).le) (Finset.mem_univ i)
    · rw [Matrix.diagonal_apply_ne _ hij]
      simpa using h0
  have h1 := key r hr
  have h2 := key (fun i => (r i)⁻¹) (fun i => inv_pos.2 (hr i))
  unfold GlobalTheory.CuspRep.height
  rw [hd, hinv]
  linarith

end GlobalTheory
