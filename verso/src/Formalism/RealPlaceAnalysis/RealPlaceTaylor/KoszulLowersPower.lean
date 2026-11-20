import Formalism.RealPlaceAnalysis.UJLocCompact
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInducingCoeMatrix

open Matrix Topology

noncomputable section

namespace Formalism.REAL

def coeMatrixAlt {n : ℕ} (ε : Fin n → Bool) : UJ ε → Matrix (Fin n) (Fin n) ℂ :=
  fun g => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma coeMatrix_left_inv {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', jm_sq_lemma]

/- English proof (translation)
The claim follows from `Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ g.2)`.
-/
lemma coeMatrix_inv_eq {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε :=
  Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ g.2)

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
lemma continuous_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Continuous (coeMatrixAlt ε) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Use `show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Jm ε * g = Jm ε}`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`.
-/
lemma isClosed_pseudoUnitary {n : ℕ} (ε : Fin n → Bool) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Jm ε * g = Jm ε}
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Conclude with `u.2`. Introduce `hg`.

Establish `hl` using `coeMatrix_left_inv ε g hg`. Set `u : (Matrix (Fin n) (Fin n) ℂ)ˣ` to `⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp hl, hl⟩`. Conclude with `⟨⟨u, hg⟩, rfl⟩`.
-/
lemma range_coeMatrix {n : ℕ} (ε : Fin n → Bool) :
    Set.range (coeMatrixAlt ε) = {g | inUJ ε g} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hg
    have hl := coeMatrix_left_inv ε g hg
    let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp hl, hl⟩
    exact ⟨⟨u, hg⟩, rfl⟩

/- English proof (translation)
Establish `hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε)))` using `continuous_id.prodMk (MulOpposite.continuous_op.comp ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))`. Use `IsInducing.of_comp (continuous_coeMatrix ε) hc ?_` and prove the remaining obligations. Establish `heq : (fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))) ∘ coeMatrixAlt ε = (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘ (Subtype.val : UJ ε → _)`. Use function extensionality and compare the values at `g`. Use `Prod.ext rfl ?_` and prove the remaining obligations.

Use `show MulOpposite.op (Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε) = MulOpposite.op (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[coeMatrix_inv_eq]`. Rewrite using `[heq]`. Conclude with `Units.isInducing_embedProduct.comp IsInducing.subtypeVal`.
-/
lemma isInducing_coeMatrix {n : ℕ} (ε : Fin n → Bool) : IsInducing (coeMatrixAlt ε) := by
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ =>
      (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  refine IsInducing.of_comp (continuous_coeMatrix ε) hc ?_
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))) ∘ coeMatrixAlt ε
      = (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘ (Subtype.val : UJ ε → _) := by
    funext g
    refine Prod.ext rfl ?_
    show MulOpposite.op (Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε) =
      MulOpposite.op (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)
    rw [coeMatrix_inv_eq]
  rw [heq]
  exact Units.isInducing_embedProduct.comp IsInducing.subtypeVal

/- English proof (translation)
Introduce `a b h`. Conclude with `Subtype.ext (Units.ext h)`.
-/
lemma injective_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Function.Injective (coeMatrixAlt ε) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

/- English proof (translation)
Introduce `n ε`. Use `⟨⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, ?_⟩, range_coeMatrix ε⟩` and prove the remaining obligations. Use `show IsClosed (Set.range (coeMatrixAlt ε))`. Rewrite using `[range_coeMatrix ε]`. Conclude with `isClosed_pseudoUnitary ε`.
-/
theorem isClosedEmbeddingMatrix : UJEmb := by
  intro n ε
  refine ⟨⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, ?_⟩, range_coeMatrix ε⟩
  show IsClosed (Set.range (coeMatrixAlt ε))
  rw [range_coeMatrix ε]
  exact isClosed_pseudoUnitary ε

/- English proof (translation)
Introduce `n ε`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := Pi.locallyCompactSpace_of_finite`. Conclude with `(h n ε).1.locallyCompactSpace`.
-/
theorem uJLocCompact_of (h : UJEmb) : UJLocCompact := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := Pi.locallyCompactSpace_of_finite
  exact (h n ε).1.locallyCompactSpace

end Formalism.REAL
