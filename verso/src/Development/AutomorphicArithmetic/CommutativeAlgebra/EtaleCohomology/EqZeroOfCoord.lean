import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VInduction

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

/- English proof (translation)
Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem UpperTheory.Ru.crystallineComparison.eq_zero_of_coord {F V C : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup C] [Module F C] (w : V ⊗[F] C)
    (h : ∀ f : Module.Dual F V, TensorProduct.lid F C (LinearMap.rTensor C f w) = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext i
  have key : ∀ w : V ⊗[F] C, (TensorProduct.equivFinsuppOfBasisLeft b w) i =
      TensorProduct.lid F C (LinearMap.rTensor C (b.coord i) w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]
  rw [key, h]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Ru.crystallineComparison.injOf :
    UpperTheory.Ru.crystallineComparison.InjOf := by
  intro l _ K B₀ ι hι hc hq G Amp hF hE hL e e' hB hP hcomp M hM j κ _ v c u hu
  obtain ⟨a⟩ := hL.ch M hM
  have h0 : (per l K).t ^ u • ∑ k, (show (per l K).A from c k) • e'.e a j (v k) = 0 := by
    change ((UpperTheory.Ru.crystallineComparison.tA l ^ u • ∑ k, c k • (show (M.MS j).lim from e'.e a j (v k)) : (M.MS j).lim)) = 0
    apply Subtype.ext
    funext n
    have := hu n
    simp only [UpperTheory.Ru.crystallineComparison.evE] at this
    simpa [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, hcomp] using this
  have h1 := UpperTheory.Ru.crystallineComparison.injAbs l K (per l K) G (dat Amp) hF hE hL e' hB hP M hM a j κ v c u h0
  apply UpperTheory.Ru.crystallineComparison.eq_zero_of_coord
  intro f
  apply hι
  have h2 := h1 f
  simp only [UpperTheory.Ru.crystallineComparison.vec, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, pow_zero, mul_one, map_zero]
  simp only [Algebra.smul_def, map_mul, hq, hc]
  exact h2
