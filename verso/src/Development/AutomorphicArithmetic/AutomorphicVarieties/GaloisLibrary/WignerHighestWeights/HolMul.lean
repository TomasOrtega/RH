import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HolEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
private theorem atEmb_add' {E : Type} [Field E] (τ : E →+* ℂ) (z w : ℂ) :
    atEmb τ (z + w) = atEmb τ z + atEmb τ w := by
  rw [atEmb_eq τ (z + w), atEmb_eq τ z, atEmb_eq τ w, Complex.add_re, Complex.add_im, add_smul, add_smul]
  abel

private noncomputable def atEmbHom {E : Type} [Field E] (τ : E →+* ℂ) : ℂ →+ Cinf E :=
  AddMonoidHom.mk' (atEmb τ) (atEmb_add' τ)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem mul_atEmb_map {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    p * x.map (atEmb τ) = (p.map (coord τ) * x).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [show atEmb τ (∑ k, coord τ (p i k) * x k j) = ∑ k, atEmb τ (coord τ (p i k) * x k j) from
    map_sum (atEmbHom τ) _ _]
  exact Finset.sum_congr rfl fun k _ => GlobalTheory.CapAdInv.mul_atEmb _ _ _

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem atEmb_map_mul {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    x.map (atEmb τ) * p = (x * p.map (coord τ)).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [show atEmb τ (∑ k, x i k * coord τ (p k j)) = ∑ k, atEmb τ (x i k * coord τ (p k j)) from
    map_sum (atEmbHom τ) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_comm (x i k)]
  exact GlobalTheory.CapAdInv.mul_atEmb _ _ _

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem atEmb_map_sub {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (x y : Matrix (Fin a) (Fin a) ℂ) :
    (x - y).map (atEmb τ) = x.map (atEmb τ) - y.map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.sub_apply, Matrix.map_apply]
  exact map_sub (atEmbHom τ) _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.holMul :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N),
      (∀ p q : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (p * X * q))) →
        ∀ x, hol τ L' x = hol τ L (p.map (coord τ) * x * q.map (coord τ))) ∧
      ∀ Y : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (Y * X - X * Y))) →
        ∀ x, hol τ L' x = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  intro E _ _ _ a N _ _ _ _ τ L L'
  refine ⟨fun p q h x => ?_, fun Y h x => ?_⟩
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← atEmb_map_sub, ← atEmb_map_sub, ← smul_sub]
