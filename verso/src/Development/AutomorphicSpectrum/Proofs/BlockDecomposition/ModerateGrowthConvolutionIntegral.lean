import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthConv

open GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def rmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := rmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    mul_add (Matrix.of z) (Matrix.of x) (Matrix.of y)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.mul_smul (Matrix.of z) c (Matrix.of x)

def lmulLin : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' x y := ContinuousLinearMap.ext fun z =>
    add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)
  map_smul' c x := ContinuousLinearMap.ext fun z =>
    Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

/- English proof (translation)
The claim follows from `(rmulLin (E := E) (a := a)).continuous_of_finiteDimensional`.
-/
theorem continuous_rmul : Continuous (rmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (rmulLin (E := E) (a := a)).continuous_of_finiteDimensional

/- English proof (translation)
The claim follows from `(lmulLin (E := E) (a := a)).continuous_of_finiteDimensional`.
-/
theorem continuous_lmul : Continuous (lmul : Lie E a → (Lie E a →L[ℝ] Lie E a)) :=
  (lmulLin (E := E) (a := a)).continuous_of_finiteDimensional

def bnd (c : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖

/- English proof (translation)
Establish `h1 : toL (y * c).val = rmul (toL c.val) (toL y.val)` using `rfl`. Establish `h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val)`. Rewrite using `[_root_.mul_inv_rev]`. Both sides reduce to the same expression. Establish `e1` using `(rmul (toL c.val)).le_opNorm (toL y.val)`.

Establish `e2` using `(lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)`. Establish `n1` using `norm_nonneg (toL y.val)`. Establish `n2` using `norm_nonneg (toL (y⁻¹).val)`. Establish `n3` using `norm_nonneg (rmul (toL c.val))`. Establish `n4` using `norm_nonneg (lmul (toL (c⁻¹).val))`.

Unfold `height bnd`. Rewrite using `[h1, h2]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem height_mul_le_bnd (c y : GL (Fin a) (Cinf E)) : height (y * c) ≤ bnd c * height y := by
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height bnd
  rw [h1, h2]
  nlinarith

/- English proof (translation)
Simplify using `only [toGL, map_inv]`.
-/
theorem toGL_inv (u : AutomorphicForm.archGroup E a) : toGL E a u⁻¹ = (toGL E a u)⁻¹ := by
  simp only [toGL, map_inv]

/- English proof (translation)
Establish `hm : Continuous (mMap E a)` using `(mMap E a).continuous_of_finiteDimensional`. Establish `hv : Continuous fun u : AutomorphicForm.archGroup E a => ((u : (AutomorphicForm.ArchMatrix E a)ˣ) : AutomorphicForm.ArchMatrix E a)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `h1 : Continuous fun u : AutomorphicForm.archGroup E a => toL (toGL E a u).val`. Repeatedly rewrite using `[toL_toGL]`. Conclude with `hm.comp hv`.

Establish `h2 : Continuous fun u : AutomorphicForm.archGroup E a => toL ((toGL E a u)⁻¹).val`. Repeatedly rewrite using `[← toGL_inv, toL_toGL]`. Conclude with `hm.comp (hv.comp continuous_inv)`. Unfold `bnd`. Conclude with `(continuous_const.add (continuous_rmul.comp h1).norm).add (continuous_lmul.comp h2).norm`.
-/
theorem continuous_bnd : Continuous fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u) := by
  have hm : Continuous (mMap E a) := (mMap E a).continuous_of_finiteDimensional
  have hv : Continuous fun u : AutomorphicForm.archGroup E a =>
      ((u : (AutomorphicForm.ArchMatrix E a)ˣ) : AutomorphicForm.ArchMatrix E a) :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun u : AutomorphicForm.archGroup E a => toL (toGL E a u).val := by
    simp_rw [toL_toGL]
    exact hm.comp hv
  have h2 : Continuous fun u : AutomorphicForm.archGroup E a => toL ((toGL E a u)⁻¹).val := by
    simp_rw [← toGL_inv, toL_toGL]
    exact hm.comp (hv.comp continuous_inv)
  unfold bnd
  exact (continuous_const.add (continuous_rmul.comp h1).norm).add (continuous_lmul.comp h2).norm

/- English proof (translation)
Introduce `E _ _ _ a _ _ ν _ φ ψ _ hgrow D hD hDc hψ g`. Take `⟨C, N, hC⟩` from `hgrow g`. Establish `hpos : ∀ y : GL (Fin a) (Cinf E), 0 ≤ height y` using `fun y => by`. Combine the linear relations using `[one_le_height y]`. Establish `C0 : 0 ≤ C`.

Establish `h1` using `(norm_nonneg _).trans (hC 1)`. Establish `hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N` using `pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N`. Conclude with `nonneg_of_mul_nonneg_left h1 hp`. Take `⟨B, hB⟩` from `IsCompact.exists_bound_of_continuousOn (f := fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u)) hDc continuous_bnd.continuousOn`. Establish `hint : Integrable (fun u => ‖D u‖) ν` using `(hD.integrable_of_hasCompactSupport hDc).norm`.

Use `⟨C * B ^ N * ∫ u, ‖D u‖ ∂ν, N, fun y => ?_⟩` and prove the remaining obligations. Establish `pt : ∀ u, ‖φ (g * infGL E a y * AutomorphicForm.infEmb E a u) * D u‖ ≤ (C * (B * height y) ^ N) * ‖D u‖` using `fun u => by`. Distinguish the cases in `hu : u ∈ tsupport D`. Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations.

Establish `e : g * infGL E a y * AutomorphicForm.infEmb E a u = g * infGL E a (y * toGL E a u)`. Rewrite using `[infEmb_eq, mul_assoc, map_mul]`. Rewrite using `[e]`. Use `(hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _) ?_ N) C0)` and prove the remaining obligations. Conclude with `(height_mul_le_bnd _ y).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB u hu)) (hpos y))`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hu]`. Simplify using the standard rewrite rules. Establish `key` using `norm_integral_le_of_norm_le (hint.const_mul (C * (B * height y) ^ N)) (Filter.Eventually.of_forall pt)`. Rewrite using `[hψ]`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[integral_const_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem growth_conv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a _ _ ν _ φ ψ _ hgrow D hD hDc hψ g
  obtain ⟨C, N, hC⟩ := hgrow g
  have hpos : ∀ y : GL (Fin a) (Cinf E), 0 ≤ height y := fun y => by
    linarith [one_le_height y]
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (f := fun u : AutomorphicForm.archGroup E a => bnd (toGL E a u))
    hDc continuous_bnd.continuousOn
  have hint : Integrable (fun u => ‖D u‖) ν := (hD.integrable_of_hasCompactSupport hDc).norm
  refine ⟨C * B ^ N * ∫ u, ‖D u‖ ∂ν, N, fun y => ?_⟩
  have pt : ∀ u, ‖φ (g * infGL E a y * AutomorphicForm.infEmb E a u) * D u‖ ≤
      (C * (B * height y) ^ N) * ‖D u‖ := fun u => by
    by_cases hu : u ∈ tsupport D
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have e : g * infGL E a y * AutomorphicForm.infEmb E a u = g * infGL E a (y * toGL E a u) := by
        rw [infEmb_eq, mul_assoc, map_mul]
      rw [e]
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _) ?_ N) C0)
      exact (height_mul_le_bnd _ y).trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB u hu)) (hpos y))
    · rw [image_eq_zero_of_notMem_tsupport hu]
      simp
  have key := norm_integral_le_of_norm_le (hint.const_mul (C * (B * height y) ^ N)) (Filter.Eventually.of_forall pt)
  rw [hψ]
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul, mul_pow]
  ring

end GlobalTheory.CompanionTheory.GrowthConv
