import Mathlib
import Formalism.UnipotentAdelicQuotients.SmComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfTangentCurveStatement
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace GlobalTheory.CompanionTheory.MatrixLie

/- English proof (translation)
Use `haveI : CompleteSpace A := FiniteDimensional.complete ℝ A`. Establish `hX` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Establish `hY` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)`. Establish `hXY` using `hX.mul hY`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hXY`.

Conclude with `hXY`.
-/
theorem hasDerivAt_exp_mul_exp_of_finiteDimensional {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y)) (X + Y) 0 := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  have hX := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hY := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  have hXY := hX.mul hY
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hXY
  exact hXY

/- English proof (translation)
The claim follows from `(LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_exp_mul_exp_of_finiteDimensional X Y)`.
-/
private theorem hasDerivAt_zero_linear_exp_smul_mul_exp_smul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) (ℓ : A →ₗ[ℝ] ℂ) :
    HasDerivAt (fun t : ℝ => ℓ (NormedSpace.exp (t • X) * NormedSpace.exp (t • Y))) (ℓ (X + Y)) 0 :=
  (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_mul_exp_of_finiteDimensional X Y)

/- English proof (translation)
Establish `hs : ∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t : ℂ) • Z) = t • Z`. Introduce `t Z`. Use extensionality with `a b`. Simplify using `[Complex.real_smul]`. Simplify using `only [hs]`.

Conclude with `@hasDerivAt_zero_linear_exp_smul_mul_exp_smul (Matrix (Fin n) (Fin n) ℂ) Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra inferInstance X Y { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`.
-/
theorem entry_hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ =>
      (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y)) i j) ((X + Y) i j) 0 := by
  have hs : ∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t : ℂ) • Z) = t • Z := by
    intro t Z
    ext a b
    simp [Complex.real_smul]
  simp only [hs]
  exact @hasDerivAt_zero_linear_exp_smul_mul_exp_smul (Matrix (Fin n) (Fin n) ℂ) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra inferInstance X Y
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/- English proof (translation)
The claim follows from `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => entry_hasDerivAt_exp_mul_exp X Y i j`.
-/
theorem hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y))
      (X + Y) 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => entry_hasDerivAt_exp_mul_exp X Y i j

/- English proof (translation)
Introduce `n G hG`. Use `⟨{ carrier := lieAlg G, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩` and prove the remaining obligations. Introduce `a b ha hb`. Establish `ha' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • a) ∈ G` using `ha`. Establish `hb' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • b) ∈ G` using `hb`.

Use `GlobalTheory.T.lie_algebra_of_tangent_curve n G hG (fun t : ℝ => NormedSpace.exp ((t : ℂ) • a) * NormedSpace.exp ((t : ℂ) • b)) (a + b) ?_ ?_ (hasDerivAt_exp_mul_exp a b)` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `Filter.Eventually.of_forall (fun t => hG.2.2.1 _ (ha' t) _ (hb' t))`. Use `show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (0 : Matrix (Fin n) (Fin n) ℂ)) ∈ G`. Introduce `t`.

Simplify using `using hG.2.1`. Introduce `c X hX`. Establish `hX' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G` using `hX`. Use `show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (c • X)) ∈ G`. Introduce `t`.

Establish `he : ((t : ℂ) • (c • X)) = ((t * c : ℝ) : ℂ) • X`. Use extensionality with `a b`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`.

Conclude with `hX' (t * c)`.
-/
theorem exists_submodule_eq_lieAlg :
    ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
      ∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
        (S : Set (Matrix (Fin n) (Fin n) ℂ)) = lieAlg G := by
  intro n G hG
  refine ⟨{ carrier := lieAlg G, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    have ha' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • a) ∈ G := ha
    have hb' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • b) ∈ G := hb
    refine GlobalTheory.T.lie_algebra_of_tangent_curve n G hG
      (fun t : ℝ => NormedSpace.exp ((t : ℂ) • a) * NormedSpace.exp ((t : ℂ) • b)) (a + b) ?_ ?_
      (hasDerivAt_exp_mul_exp a b)
    · simp
    · exact Filter.Eventually.of_forall (fun t => hG.2.2.1 _ (ha' t) _ (hb' t))
  · show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (0 : Matrix (Fin n) (Fin n) ℂ)) ∈ G
    intro t
    simpa using hG.2.1
  · intro c X hX
    have hX' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G := hX
    show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (c • X)) ∈ G
    intro t
    have he : ((t : ℂ) • (c • X)) = ((t * c : ℝ) : ℂ) • X := by
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [he]
    exact hX' (t * c)

end GlobalTheory.CompanionTheory.MatrixLie
