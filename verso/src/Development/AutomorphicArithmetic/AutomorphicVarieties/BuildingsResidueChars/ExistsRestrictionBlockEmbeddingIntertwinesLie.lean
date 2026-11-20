import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingCommInfEmbAndExp
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def extL (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) :
    archLie K a →ₗ[ℝ] archLie K n where
  toFun Y := (isExpLieAlgebra K n).ofLie (toLie K n (ext0 e (mat Y.1)))
  map_add' X Y := Subtype.ext (matrixExtendByZero_add e (mat X.1) (mat Y.1))
  map_smul' c X := Subtype.ext (by
    change ext0 e (c • mat X.1) = c • ext0 e (mat X.1)
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul])

/- English proof (translation)
Take `⟨h1, h2⟩` from `UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e`. Establish `h3 : embArch e ((isExpLieAlgebra K a).expG Y) = (isExpLieAlgebra K n).expG (extL K e Y)` using `h2 (mat Y.1)`. Rewrite using `[← h3, ← map_mul, archSlice_apply, archSlice_apply, ← h1, map_mul (emb e) m, mul_assoc]`.
-/
private theorem key (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K n) (ψ : AdelicGLn.AdelicGL K n → ℂ) (m : AdelicGLn.AdelicGL K a) (x : archGroup K a)
    (Y : archLie K a) :
    archSlice (fun m => ψ (g * emb e m)) m (x * (isExpLieAlgebra K a).expG Y) =
      archSlice ψ (g * emb e m) (embArch e x * (isExpLieAlgebra K n).expG (extL K e Y)) := by
  obtain ⟨h1, h2⟩ := UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e
  have h3 : embArch e ((isExpLieAlgebra K a).expG Y) = (isExpLieAlgebra K n).expG (extL K e Y) := h2 (mat Y.1)
  rw [← h3, ← map_mul, archSlice_apply, archSlice_apply, ← h1, map_mul (emb e) m, mul_assoc]

/- English proof (translation)
Introduce `K _ _ a n e g`. Establish `hs : ∀ ψ : archSmooth K n, (fun m => ψ.1 (g * emb e m)) ∈ archSmooth K a` using `fun ψ m => by`. Rewrite using `[IsExpLieAlgebra.isSmoothFun_iff]`. Introduce `x`. Simplify using `only [key]`.

Conclude with `(((isExpLieAlgebra K n).isSmoothFun_iff).1 (ψ.2 (g * emb e m)) (embArch e x)).comp (LinearMap.toContinuousLinearMap (extL K e)).contDiff`. Use `⟨{ toFun := fun ψ => ⟨_, hs ψ⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }, fun _ _ => rfl, fun X ψ => Subtype.ext (funext fun m => ?_)⟩` and prove the remaining obligations. Establish `h1` using `(isExpLieAlgebra K a).hasDerivAt_rightDeriv (hs ψ m) ((isExpLieAlgebra K a).ofLie (toLie K a X)) 1`. Establish `h2` using `(isExpLieAlgebra K n).hasDerivAt_rightDeriv (ψ.2 (g * emb e m)) (extL K e ((isExpLieAlgebra K a).ofLie (toLie K a X))) 1`. Simplify using `only [key, map_one, map_smul] at h1`.

Conclude with `(uAction_ι_apply (toLie K n (ext0 e X)) ψ (g * emb e m)).trans ((h2.unique h1).trans (uAction_ι_apply (toLie K a X) ⟨_, hs ψ⟩ m).symm)`.
-/
theorem UpperTheory.exists_restriction_blockEmbedding_intertwines_lie :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K n), ∃ f : archSmooth K n →ₗ[ℂ] archSmooth K a, (∀ ψ m, (f ψ).1 m = ψ.1 (g * emb e m)) ∧ ∀ X ψ, f (lam K n (ext0 e X) ψ) = lam K a X (f ψ) := by
  intro K _ _ a n e g
  have hs : ∀ ψ : archSmooth K n, (fun m => ψ.1 (g * emb e m)) ∈ archSmooth K a := fun ψ m => by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro x
    simp only [key]
    exact (((isExpLieAlgebra K n).isSmoothFun_iff).1 (ψ.2 (g * emb e m)) (embArch e x)).comp
      (LinearMap.toContinuousLinearMap (extL K e)).contDiff
  refine ⟨{ toFun := fun ψ => ⟨_, hs ψ⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun _ _ => rfl, fun X ψ => Subtype.ext (funext fun m => ?_)⟩
  have h1 := (isExpLieAlgebra K a).hasDerivAt_rightDeriv (hs ψ m) ((isExpLieAlgebra K a).ofLie (toLie K a X)) 1
  have h2 := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (ψ.2 (g * emb e m))
    (extL K e ((isExpLieAlgebra K a).ofLie (toLie K a X))) 1
  simp only [key, map_one, map_smul] at h1
  exact (uAction_ι_apply (toLie K n (ext0 e X)) ψ (g * emb e m)).trans
    ((h2.unique h1).trans (uAction_ι_apply (toLie K a X) ⟨_, hs ψ⟩ m).symm)
