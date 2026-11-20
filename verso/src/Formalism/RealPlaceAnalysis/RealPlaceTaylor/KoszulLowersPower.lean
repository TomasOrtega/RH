import Formalism.RealPlaceAnalysis.UJLocCompact
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInducingCoeMatrix

open Matrix Topology

noncomputable section

namespace Formalism.REAL

def coeMatrixAlt {n : ℕ} (ε : Fin n → Bool) : UJ ε → Matrix (Fin n) (Fin n) ℂ :=
  fun g => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
lemma coeMatrix_left_inv {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', jm_sq_lemma]

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma coeMatrix_inv_eq {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε :=
  Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ g.2)

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma continuous_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Continuous (coeMatrixAlt ε) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma isClosed_pseudoUnitary {n : ℕ} (ε : Fin n → Bool) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Jm ε * g = Jm ε}
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Introduce a local definition for the expression. Supply the required witnesses or components. A detailed English derivation is pending.
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
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
lemma injective_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Function.Injective (coeMatrixAlt ε) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isClosedEmbeddingMatrix : UJEmb := by
  intro n ε
  refine ⟨⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, ?_⟩, range_coeMatrix ε⟩
  show IsClosed (Set.range (coeMatrixAlt ε))
  rw [range_coeMatrix ε]
  exact isClosed_pseudoUnitary ε

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem uJLocCompact_of (h : UJEmb) : UJLocCompact := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := Pi.locallyCompactSpace_of_finite
  exact (h n ε).1.locallyCompactSpace

end Formalism.REAL
