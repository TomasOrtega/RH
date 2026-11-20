import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegral

open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1.Height
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

/- English proof (translation)
Conclude with `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp`.
-/
theorem norm_one_le : ‖(1 : Cinf E)‖ ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

/- English proof (translation)
Establish `n0` using `norm_nonneg (toL y.val)`. Establish `hent : ∀ i j, ‖(y.val i j : Cinf E)‖ ≤ ‖toL y.val‖` using `fun i j => (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)`. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) i j‖ ≤ _`. Rewrite using `[GlobalTheory.SmGL.val_emb₂]`.

Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply]`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'`. Generalize the expression as in `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'`. Apply the tactic sequence `rcases i' with i' | i' <;> rcases j' with j' | j'`. Simplify using `using (hent i' j').trans (by linarith)`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ‖((1 : Matrix (Fin s) (Fin s) (Cinf E)) i' j')‖ ≤ 1`.

Distinguish the cases in `h : i' = j'`. Substitute `h` using the available equality. Simplify using `using norm_one_le`. Simplify using `[Matrix.one_apply_ne h]`. Simplify using `using h1.trans (by linarith)`.
-/
theorem norm_lev_le (y : GL (Fin r) (Cinf E)) :
    ‖toL (lev (Cinf E) r s (y, 1)).val‖ ≤ ‖toL y.val‖ + 1 := by
  have n0 := norm_nonneg (toL y.val)
  have hent : ∀ i j, ‖(y.val i j : Cinf E)‖ ≤ ‖toL y.val‖ := fun i j =>
    (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) i j‖ ≤ _
  rw [GlobalTheory.SmGL.val_emb₂]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using (hent i' j').trans (by linarith)
  · simp; linarith
  · simp; linarith
  · have h1 : ‖((1 : Matrix (Fin s) (Fin s) (Cinf E)) i' j')‖ ≤ 1 := by
      by_cases h : i' = j'
      · subst h; simpa using norm_one_le
      · simp [Matrix.one_apply_ne h]
    simpa using h1.trans (by linarith)

/- English proof (translation)
Establish `e : (lev (Cinf E) r s (y, 1))⁻¹ = lev (Cinf E) r s (y⁻¹, 1)`. Rewrite using `[← map_inv, Prod.inv_mk, inv_one]`. Establish `h1` using `norm_lev_le (s := s) y`. Establish `h2` using `norm_lev_le (s := s) y⁻¹`. Establish `n1` using `norm_nonneg (toL y.val)`.

Establish `n2` using `norm_nonneg (toL (y⁻¹).val)`. Unfold `height`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem height_lev_le (y : GL (Fin r) (Cinf E)) :
    height (lev (Cinf E) r s (y, 1)) ≤ 3 * height y := by
  have e : (lev (Cinf E) r s (y, 1))⁻¹ = lev (Cinf E) r s (y⁻¹, 1) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_lev_le (s := s) y
  have h2 := norm_lev_le (s := s) y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.CompanionTheory.CTFin.Slice1.Height

/- English proof (translation)
Introduce `E _ _ _ r s c`. Establish `hb : 0 ≤ GlobalTheory.CompanionTheory.GrowthConv.bnd c`. Unfold `GlobalTheory.CompanionTheory.GrowthConv.bnd`. Check the signs of the components of the expression. Use `⟨3 * GlobalTheory.CompanionTheory.GrowthConv.bnd c, by positivity, fun y => ?_⟩` and prove the remaining obligations.

Use `(GlobalTheory.CompanionTheory.GrowthConv.height_mul_le_bnd c _).trans ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (Height.height_lev_le (s := s) y) hb` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  intro E _ _ _ r s c
  have hb : 0 ≤ GlobalTheory.CompanionTheory.GrowthConv.bnd c := by
    unfold GlobalTheory.CompanionTheory.GrowthConv.bnd
    positivity
  refine ⟨3 * GlobalTheory.CompanionTheory.GrowthConv.bnd c, by positivity, fun y => ?_⟩
  refine (GlobalTheory.CompanionTheory.GrowthConv.height_mul_le_bnd c _).trans ?_
  have := mul_le_mul_of_nonneg_left (Height.height_lev_le (s := s) y) hb
  linarith

end
