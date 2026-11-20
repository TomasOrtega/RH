import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionMultiplicative
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviComm

open Matrix GlobalTheory.LeviElem

/- English proof (translation)
Simplify using `only [blk, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal, Matrix.one_mul, Matrix.mul_one]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [mul_comm]`.
-/
theorem blk_comm {R : Type} [CommRing R] {b : ℕ} (g : Matrix (Fin b) (Fin b) R) (t u : R) :
    blk 1 t u * blk g 1 1 = blk g 1 1 * blk 1 t u := by
  simp only [blk, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    diagonal_mul_diagonal, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n₁ X X₁ H i₀ i₁ r s r₁ s₁ hB hX hX₁ hH t a g₀ g' ha hg`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hσ : ∀ z, σ (σ z) = z` using `fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Establish `hdet : X₁.J.det ≠ 0`. Establish `h` using `det_ne_of_sig _ (hX₁.sig w)`.

Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `: (X₁.J.map (B.emb w).1).det = (B.emb w).1 X₁.J.det` using `(RingHom.map_det (B.emb w).1 _).symm`. Rewrite using `[this, h0, map_zero]`. Use `set P := fromCols H.ι (cols2 H.x H.y) with hP`.

Establish `hK : Pᵀ * X.J * P.map σ = fromBlocks X₁.J 0 0 swap2` using `gram_block σ hσ B hX.herm hH`. Use `set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks X₁.J 0 0 swap2 with hKdef`. Establish `hKdet : IsUnit Kᵀ.det`. Rewrite using `[det_transpose, hKdef, det_fromBlocks_zero₂₁]`. Simplify using `[swap2, det_fin_two, hdet]`.

Use `set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * X.Jᵀ) with hQ`. Establish `hQP : Q * P = 1`. Establish `: (P.map σ)ᵀ * X.Jᵀ * P = Kᵀ`. Rewrite using `[← hK]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.

Rewrite using `[hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`. Use `set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA`. Establish `hPf : P.map f = PA`. Use extensionality with `i (j | j)`.

Both sides reduce to the same expression. Apply the tactic sequence `fin_cases j <;> rfl`. Establish `hQP' : Q.map f * PA = 1`. Rewrite using `[← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]`. Establish `hPQ' : PA * Q.map f = 1` using `(Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'`.

Establish `h1` using `GlobalTheory.LeviHom.levi_mul_cols H t 1 a ha`. Establish `h2` using `GlobalTheory.LeviHom.levi_mul_cols H 1 g₀ g' hg`. Establish `hm1 : mat (1 : UA σ X₁.J) = 1` using `rfl`. Rewrite `h1` using `[hm1]`. Simplify using `only [Units.val_one, inv_one, map_one] at h1 h2`.

Establish `key : mat a * mat g' * PA = mat g' * mat a * PA`. Rewrite using `[Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, blk_comm, Matrix.mul_assoc (mat g'), h1, ← Matrix.mul_assoc, ← h2, Matrix.mul_assoc]`. Establish `e : mat (a * g') = mat (g' * a)`. Use `congrArg (· * Q.map f) key` as an intermediate fact. Simplify using `only [Matrix.mul_assoc, hPQ', Matrix.mul_one] at this`.

Conclude with `this`. Conclude with `Subtype.ext (Units.ext e)`.
-/
theorem levi_comm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ (t : (AE F E)ˣ) (a : UA σ X.J) (g₀ : UA σ X₁.J) (g' : UA σ X.J),
    IsLevi (W₁ := X₁) H t 1 a → IsLevi H 1 g₀ g' → a * g' = g' * a := by
  intro F E _ _ _ _ _ σ B n₁ X X₁ H i₀ i₁ r s r₁ s₁ hB hX hX₁ hH t a g₀ g' ha hg
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : X₁.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hX₁.sig w)
    intro h0
    apply h
    have : (X₁.J.map (B.emb w).1).det = (B.emb w).1 X₁.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * X.J * P.map σ = fromBlocks X₁.J 0 0 swap2 := gram_block σ hσ B hX.herm hH
  set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks X₁.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * X.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * X.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  have h1 := GlobalTheory.LeviHom.levi_mul_cols H t 1 a ha
  have h2 := GlobalTheory.LeviHom.levi_mul_cols H 1 g₀ g' hg
  have hm1 : mat (1 : UA σ X₁.J) = 1 := rfl
  rw [hm1] at h1
  simp only [Units.val_one, inv_one, map_one] at h1 h2
  have key : mat a * mat g' * PA = mat g' * mat a * PA := by
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, blk_comm, Matrix.mul_assoc (mat g'), h1,
      ← Matrix.mul_assoc, ← h2, Matrix.mul_assoc]
  have e : mat (a * g') = mat (g' * a) := by
    have := congrArg (· * Q.map f) key
    simp only [Matrix.mul_assoc, hPQ', Matrix.mul_one] at this
    exact this
  exact Subtype.ext (Units.ext e)

end GlobalTheory.LeviComm
