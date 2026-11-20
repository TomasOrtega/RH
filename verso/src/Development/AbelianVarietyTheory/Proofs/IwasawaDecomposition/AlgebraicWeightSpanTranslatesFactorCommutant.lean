import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeightStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

/- English proof (translation)
Introduce `L _ _ _ n a ι _ _ b P hA τ v hv w`. Establish `hS` using `GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight L n a ι b P hA v hv w`. Use `Submodule.span_mono ?_ hS` and prove the remaining obligations. Introduce and unpack `x ⟨γ₀, hγ, rfl⟩`. Take `⟨_, hmul⟩` from `GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P hA`.

Use `set B : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.map τ γ₀ with hBdef`. Establish `hBv : B.val = γ₀.val.map τ` using `rfl`. Use `set R : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ => if σ = τ ∨ σ = ComplexEmbedding.conjugate τ then 1 else ratPt γ₀.val σ with hRdef`. Establish `hU` using `isUPt_ratPt γ₀ hγ`. Establish `hR : IsUPt R`.

Introduce `σ`. Distinguish the cases in `h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ`. Establish `h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ`. Break down `h with h | h` into its components or cases. Use `right`.

Rewrite using `[h]`. Use `left`. Rewrite using `[h, conj_conj]`. Simplify using `only [R, if_pos h, if_pos h', Matrix.transpose_one, mul_one]`. Establish `h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ)`.

Introduce and unpack `(h' | h')`. Conclude with `h (Or.inr (by rw [← h', conj_conj]))`. Conclude with `h (Or.inl (by simpa [conj_conj] using congrArg ComplexEmbedding.conjugate h'))`. Simplify using `only [R, if_neg h, if_neg h']`. Conclude with `hU σ`.

Establish `hinv : ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (ratPt γ₀.val (ComplexEmbedding.conjugate τ))ᵀ`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Conclude with `hU τ`. Establish `hdec : ratPt γ₀.val = fun σ => tauPt τ B σ * R σ`. Use function extensionality and compare the values at `σ`.

Establish `hne` using `conjugate_ne_self τ`. Distinguish the cases in `h1 : σ = τ`. Substitute `h1` using the available equality. Simplify using `[tauPt, R, hBv, ratPt]`. Distinguish the cases in `h2 : σ = ComplexEmbedding.conjugate τ`.

Substitute `h2` using the available equality. Simplify using `only [tauPt, if_neg h1, if_true, R, or_true, mul_one]`. Rewrite using `[hinv, Matrix.transpose_transpose]`. Simplify using `[tauPt, R, h1, h2]`. Establish `hcomm : ∀ A : GL (Fin n) ℂ, (fun σ => tauPt τ A σ * R σ) = (fun σ => R σ * tauPt τ A σ)`.

Introduce `A`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ`. Simplify using `[R, h]`. Establish `h1 : σ ≠ τ` using `fun e => h (Or.inl e)`.

Establish `h2 : σ ≠ ComplexEmbedding.conjugate τ` using `fun e => h (Or.inr e)`. Simplify using `[tauPt, h1, h2]`. Use `⟨B, evM P (upt R), ?_, ?_⟩` and prove the remaining obligations. Introduce `A`. Rewrite using `[evPt_eq_upt, ← hmul _ _ hR (isUPt_tauPt τ A), ← hmul _ _ (isUPt_tauPt τ A) hR, hcomm A]`.

Rewrite using `[hdec, hmul _ _ (isUPt_tauPt τ B) hR, evPt_eq_upt, Matrix.mulVec_mulVec]`.
-/
theorem span_tau_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  intro L _ _ _ n a ι _ _ b P hA τ v hv w
  classical
  have hS := GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight L n a ι b P hA v hv w
  refine Submodule.span_mono ?_ hS
  rintro x ⟨γ₀, hγ, rfl⟩
  obtain ⟨_, hmul⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P hA
  set B : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.map τ γ₀ with hBdef
  have hBv : B.val = γ₀.val.map τ := rfl
  set R : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
    if σ = τ ∨ σ = ComplexEmbedding.conjugate τ then 1 else ratPt γ₀.val σ with hRdef
  have hU := isUPt_ratPt γ₀ hγ
  have hR : IsUPt R := by
    intro σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
        rcases h with h | h
        · right; rw [h]
        · left; rw [h, conj_conj]
      simp only [R, if_pos h, if_pos h', Matrix.transpose_one, mul_one]
    · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
        rintro (h' | h')
        · exact h (Or.inr (by rw [← h', conj_conj]))
        · exact h (Or.inl (by simpa [conj_conj] using congrArg ComplexEmbedding.conjugate h'))
      simp only [R, if_neg h, if_neg h']
      exact hU σ
  have hinv : ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (ratPt γ₀.val (ComplexEmbedding.conjugate τ))ᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    exact hU τ
  have hdec : ratPt γ₀.val = fun σ => tauPt τ B σ * R σ := by
    funext σ
    have hne := conjugate_ne_self τ
    by_cases h1 : σ = τ
    · subst h1
      simp [tauPt, R, hBv, ratPt]
    · by_cases h2 : σ = ComplexEmbedding.conjugate τ
      · subst h2
        simp only [tauPt, if_neg h1, if_true, R, or_true, mul_one]
        rw [hinv, Matrix.transpose_transpose]
      · simp [tauPt, R, h1, h2]
  have hcomm : ∀ A : GL (Fin n) ℂ, (fun σ => tauPt τ A σ * R σ) = (fun σ => R σ * tauPt τ A σ) := by
    intro A
    funext σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · simp [R, h]
    · have h1 : σ ≠ τ := fun e => h (Or.inl e)
      have h2 : σ ≠ ComplexEmbedding.conjugate τ := fun e => h (Or.inr e)
      simp [tauPt, h1, h2]
  refine ⟨B, evM P (upt R), ?_, ?_⟩
  · intro A
    rw [evPt_eq_upt, ← hmul _ _ hR (isUPt_tauPt τ A), ← hmul _ _ (isUPt_tauPt τ A) hR, hcomm A]
  · rw [hdec, hmul _ _ (isUPt_tauPt τ B) hR, evPt_eq_upt, Matrix.mulVec_mulVec]

end GlobalTheory.AlgWtHW
