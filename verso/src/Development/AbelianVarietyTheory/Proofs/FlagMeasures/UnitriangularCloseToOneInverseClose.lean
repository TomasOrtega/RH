import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Both sides reduce to the same expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem unitriangular_inv_close {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E) (ht : t ∈ L.O) (hlow : ∀ i j, j < i → M i j = 0) (hdiag : ∀ i, M i i = 1) (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) : ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  have hMO : ∀ i j, M i j ∈ L.O := by
    intro i j
    obtain ⟨o, ho, he⟩ := hcl i j
    have : M i j = t * o + (1 : Matrix (Fin n) (Fin n) E) i j := by
      rw [← he]; simp
    rw [this]
    refine L.O.add_mem (L.O.mul_mem ht ho) ?_
    by_cases h : i = j
    · subst h; simp [L.O.one_mem]
    · simp [h, L.O.zero_mem]
  let f : L.O →+* E := L.O.subtype
  let M' : Matrix (Fin n) (Fin n) L.O := Matrix.of fun i j => ⟨M i j, hMO i j⟩
  have hM' : f.mapMatrix M' = M := by
    ext i j; rfl
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : f M'.det = (f.mapMatrix M').det := RingHom.map_det f M'
    have h2 : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (M := M) (fun i j hij => hlow i j hij)]
      simp [hdiag]
    change f M'.det = f 1
    rw [h1, hM', h2, map_one]
  have hu : IsUnit M'.det := by rw [hdet]; exact isUnit_one
  refine ⟨f.mapMatrix M'⁻¹, ?_, ?_, ?_⟩
  · rw [← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
  · rw [← hM', ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  · intro i j
    set Mi := f.mapMatrix M'⁻¹ with hMi
    have hinv : Mi * M = 1 := by
      rw [hMi, ← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
    have key : Mi - 1 = -(Mi * (M - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
    choose o ho he using hcl
    refine ⟨-(∑ k, (M'⁻¹ i k : E) * o k j), ?_, ?_⟩
    · exact L.O.neg_mem (L.O.sum_mem fun k _ => L.O.mul_mem (M'⁻¹ i k).2 (ho k j))
    · rw [key, Matrix.neg_apply, Matrix.mul_apply]
      simp only [he]
      rw [mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hMi, f]
      ring

end GlobalTheory
