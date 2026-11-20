import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.SympBlocks

open scoped ComplexOrder

/- English proof (translation)
Establish `h4 : Dᵀ * A - Bᵀ * C = 1`. Simplify `congrArg Matrix.transpose h3` using `[transpose_sub, transpose_mul]`. Establish `e3 : Aᵀ * D = 1 + Cᵀ * B` using `by rw [← h3]; abel`. Establish `e4 : Dᵀ * A = 1 + Bᵀ * C` using `by rw [← h4]; abel`. Simplify using `only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul, I_mul_I]`.

Rewrite using `[← h1, ← h2, e3, e4]`. Use `module`.
-/
theorem herm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (Aᵀ + I • Bᵀ) * (C - I • D) - (Cᵀ + I • Dᵀ) * (A - I • B) = (-(2 * I)) • (1 : Matrix l l ℂ) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
    I_mul_I]
  rw [← h1, ← h2, e3, e4]
  module

/- English proof (translation)
Establish `h4 : Dᵀ * A - Bᵀ * C = 1`. Simplify `congrArg Matrix.transpose h3` using `[transpose_sub, transpose_mul]`. Establish `e3 : Aᵀ * D = 1 + Cᵀ * B` using `by rw [← h3]; abel`. Establish `e4 : Dᵀ * A = 1 + Bᵀ * C` using `by rw [← h4]; abel`. Simplify using `only [transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`.

Rewrite using `[← h1, ← h2, e3, e4]`. Use `module`.
-/
theorem symm_identity {l : Type} [Fintype l] [DecidableEq l] (A B C D : Matrix l l ℂ)
    (h1 : Aᵀ * C = Cᵀ * A) (h2 : Bᵀ * D = Dᵀ * B) (h3 : Aᵀ * D - Cᵀ * B = 1) :
    (A - I • B)ᵀ * (C - I • D) = (C - I • D)ᵀ * (A - I • B) := by
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg Matrix.transpose h3
  have e3 : Aᵀ * D = 1 + Cᵀ * B := by rw [← h3]; abel
  have e4 : Dᵀ * A = 1 + Bᵀ * C := by rw [← h4]; abel
  simp only [transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← h1, ← h2, e3, e4]
  module

end GlobalTheory.SympBlocks

namespace GlobalTheory.SympBlocks

open scoped ComplexOrder

/- English proof (translation)
Introduce `l _ _ s P Q hP hQ hs`. Establish `hs' : fromBlocks s.toBlocks₁₁ s.toBlocks₁₂ s.toBlocks₂₁ s.toBlocks₂₂ ∈ Matrix.symplecticGroup l ℝ` using `by rwa [fromBlocks_toBlocks]`. Take `⟨r1, r2, r3⟩` from `SymplecticGroup.fromBlocks_mem_iff.1 hs'`. Use `set A := s.toBlocks₁₁.map Complex.ofRealHom`. Use `set B := s.toBlocks₁₂.map Complex.ofRealHom`.

Use `set C := s.toBlocks₂₁.map Complex.ofRealHom`. Use `set D := s.toBlocks₂₂.map Complex.ofRealHom`. Establish `h1 : Aᵀ * C = Cᵀ * A`. Simplify using `only [A, C, ← transpose_map, ← Matrix.map_mul, r1]`. Establish `h2 : Bᵀ * D = Dᵀ * B`.

Simplify using `only [B, D, ← transpose_map, ← Matrix.map_mul, r2]`. Establish `h3 : Aᵀ * D - Cᵀ * B = 1`. Simplify using `only [A, B, C, D, ← transpose_map, ← Matrix.map_mul]`. Rewrite using `[← Matrix.map_sub _ (fun a b => map_sub Complex.ofRealHom a b), r3]`. Simplify using the standard rewrite rules.

Establish `ePQ : P = A - I • B ∧ Q = C - I • D`. Apply the tactic sequence `constructor <;> ext a b <;> simp [A, B, C, D, hP, hQ, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]`. Take `⟨eP, eQ⟩` from `ePQ`. Establish `hPc : Pᴴ = Aᵀ + I • Bᵀ`. Rewrite using `[eP]`.

Use extensionality with `a b`. Simplify using `[A, B, conjTranspose_apply, transpose_apply]`. Establish `hQc : Qᴴ = Cᵀ + I • Dᵀ`. Rewrite using `[eQ]`. Use extensionality with `a b`.

Simplify using `[C, D, conjTranspose_apply, transpose_apply]`. Establish `hH : Pᴴ * Q - Qᴴ * P = (-(2 * I)) • (1 : Matrix l l ℂ)`. Rewrite using `[hPc, hQc, eP, eQ]`. Conclude with `herm_identity A B C D h1 h2 h3`. Establish `hS : Pᵀ * Q = Qᵀ * P`.

Rewrite using `[eP, eQ]`. Conclude with `symm_identity A B C D h1 h2 h3`. Establish `hdet : P.det ≠ 0`. Introduce `h0`. Take `⟨v, hv0, hv⟩` from `(Matrix.exists_mulVec_eq_zero_iff).2 h0`.

Establish `key : star v ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ v) = 0`. Rewrite using `[Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hv, star_zero, zero_dotProduct]`. Rewrite `key` using `[hH, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]`. Establish `h2I : (-(2 * I)) ≠ 0` using `by simp [I_ne_zero]`. Establish `: star v ⬝ᵥ v = 0` using `(mul_eq_zero.1 key).resolve_left h2I`.

Conclude with `hv0 (dotProduct_star_self_eq_zero.1 this)`. Use `⟨hdet, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hdet`. Establish `huT : IsUnit Pᵀ.det` using `by rwa [det_transpose]`. Apply `Matrix.IsSymm.neg` to reduce the goal to its premises.

Unfold `Matrix.IsSymm`. Rewrite using `[transpose_mul, transpose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]`. Use `_ = Pᵀ⁻¹ * (Pᵀ * Q) * P⁻¹ := by rw [hS]`.

Use `_ = Q * P⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.one_mul]`.
-/
theorem det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ),
    (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) →
    s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  intro l _ _ s P Q hP hQ hs
  have hs' : fromBlocks s.toBlocks₁₁ s.toBlocks₁₂ s.toBlocks₂₁ s.toBlocks₂₂ ∈
      Matrix.symplecticGroup l ℝ := by rwa [fromBlocks_toBlocks]
  obtain ⟨r1, r2, r3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hs'
  set A := s.toBlocks₁₁.map Complex.ofRealHom
  set B := s.toBlocks₁₂.map Complex.ofRealHom
  set C := s.toBlocks₂₁.map Complex.ofRealHom
  set D := s.toBlocks₂₂.map Complex.ofRealHom
  have h1 : Aᵀ * C = Cᵀ * A := by
    simp only [A, C, ← transpose_map, ← Matrix.map_mul, r1]
  have h2 : Bᵀ * D = Dᵀ * B := by
    simp only [B, D, ← transpose_map, ← Matrix.map_mul, r2]
  have h3 : Aᵀ * D - Cᵀ * B = 1 := by
    simp only [A, B, C, D, ← transpose_map, ← Matrix.map_mul]
    rw [← Matrix.map_sub _ (fun a b => map_sub Complex.ofRealHom a b), r3]; simp
  have ePQ : P = A - I • B ∧ Q = C - I • D := by
    constructor <;> ext a b <;> simp [A, B, C, D, hP, hQ, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
      toBlocks₂₂]
  obtain ⟨eP, eQ⟩ := ePQ
  have hPc : Pᴴ = Aᵀ + I • Bᵀ := by
    rw [eP]; ext a b; simp [A, B, conjTranspose_apply, transpose_apply]
  have hQc : Qᴴ = Cᵀ + I • Dᵀ := by
    rw [eQ]; ext a b; simp [C, D, conjTranspose_apply, transpose_apply]
  have hH : Pᴴ * Q - Qᴴ * P = (-(2 * I)) • (1 : Matrix l l ℂ) := by
    rw [hPc, hQc, eP, eQ]; exact herm_identity A B C D h1 h2 h3
  have hS : Pᵀ * Q = Qᵀ * P := by
    rw [eP, eQ]; exact symm_identity A B C D h1 h2 h3
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have key : star v ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ v) = 0 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hv,
        star_zero, zero_dotProduct]
    rw [hH, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at key
    have h2I : (-(2 * I)) ≠ 0 := by simp [I_ne_zero]
    have : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 key).resolve_left h2I
    exact hv0 (dotProduct_star_self_eq_zero.1 this)
  refine ⟨hdet, ?_⟩
  have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hdet
  have huT : IsUnit Pᵀ.det := by rwa [det_transpose]
  apply Matrix.IsSymm.neg
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_nonsing_inv]
  calc Pᵀ⁻¹ * Qᵀ = Pᵀ⁻¹ * (Qᵀ * P) * P⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Pᵀ⁻¹ * (Pᵀ * Q) * P⁻¹ := by rw [hS]
    _ = Q * P⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.one_mul]

end GlobalTheory.SympBlocks
