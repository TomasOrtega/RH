import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPointsStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

/- English proof (translation)
Introduce `L _ _ _ n a ι _ _ b P ι' _ _ b' P' hP hP' τ B`. Establish `key : ∀ x, evM P' x - b'.toMatrix b * evM P x * b.toMatrix b' = Matrix.of fun i j => MvPolynomial.eval x (P' i j - ∑ k, ∑ l, MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j))`. Introduce `x`. Use extensionality with `i j`. Simplify using `only [evM, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, map_sub, map_sum, map_mul, MvPolynomial.eval_C, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Establish `hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = b'.toMatrix b * evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * b.toMatrix b'`. Introduce `γ₀ h`. Take `⟨γ, hγ⟩` from `exists_gq γ₀ h`. Establish `e1` using `hP γ γ₀ hγ`.

Establish `e2` using `hP' γ γ₀ hγ`. Establish `e3` using `(basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b') (c := b') (b' := b) (c' := b) (f := a.ρ γ)).symm`. Establish `f1 : evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ)`. Rewrite using `[e1]`. Both sides reduce to the same expression.

Establish `f2 : evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b' b' (a.ρ γ)`. Rewrite using `[e2]`. Both sides reduce to the same expression. Rewrite using `[f1, f2, e3]`. Establish `hz : ∀ i j, MvPolynomial.eval (evPt τ B) (P' i j - ∑ k, ∑ l, MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) = 0`.

Introduce `i j`. Rewrite using `[evPt_eq_upt]`. Use `GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n _ ?_ (tauPt τ B) (isUPt_tauPt τ B)` and prove the remaining obligations. Introduce `γ₀ h`. Use `congrArg (fun M => M i j) (key (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))))` as an intermediate fact.

Simplify using `only [hrat γ₀ h, sub_self] at this`. Simplify using `using this.symm`. Rewrite using `[← sub_eq_zero, key]`. Use extensionality with `i j`. Simplify using `using hz i j`.
-/
theorem evM_change_of_basis : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (b' : Module.Basis ι' ℂ a.W) (P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → Agrees a b' P' → ∀ (τ : L →+* ℂ) (B : GL (Fin n) ℂ), evM P' (evPt τ B) = b'.toMatrix b * evM P (evPt τ B) * b.toMatrix b' := by
  intro L _ _ _ n a ι _ _ b P ι' _ _ b' P' hP hP' τ B

  have key : ∀ x, evM P' x - b'.toMatrix b * evM P x * b.toMatrix b' =
      Matrix.of fun i j => MvPolynomial.eval x (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) := by
    intro x
    ext i j
    simp only [evM, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, map_sub, map_sum, map_mul, MvPolynomial.eval_C, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) =
        b'.toMatrix b * evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * b.toMatrix b' := by
    intro γ₀ h
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h
    have e1 := hP γ γ₀ hγ
    have e2 := hP' γ γ₀ hγ
    have e3 := (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b') (c := b') (b' := b) (c' := b) (f := a.ρ γ)).symm
    have f1 : evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
      rw [e1]; rfl
    have f2 : evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b' b' (a.ρ γ) := by
      rw [e2]; rfl
    rw [f1, f2, e3]
  have hz : ∀ i j, MvPolynomial.eval (evPt τ B) (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) = 0 := by
    intro i j
    rw [evPt_eq_upt]
    refine GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n _ ?_ (tauPt τ B) (isUPt_tauPt τ B)
    intro γ₀ h
    have := congrArg (fun M => M i j) (key (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))))
    simp only [hrat γ₀ h, sub_self] at this
    simpa using this.symm
  rw [← sub_eq_zero, key]
  ext i j
  simpa using hz i j

end GlobalTheory.AlgWtHW
