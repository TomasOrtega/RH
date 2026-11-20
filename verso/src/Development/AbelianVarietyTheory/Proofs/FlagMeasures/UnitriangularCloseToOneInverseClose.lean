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
Establish `hMO : ∀ i j, M i j ∈ L.O`. Introduce `i j`. Take `⟨o, ho, he⟩` from `hcl i j`. Establish `: M i j = t * o + (1 : Matrix (Fin n) (Fin n) E) i j`. Rewrite using `[← he]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `L.O.add_mem (L.O.mul_mem ht ho) ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[L.O.one_mem]`. Simplify using `[h, L.O.zero_mem]`. Set `f : L.O →+* E` to `L.O.subtype`. Set `M' : Matrix (Fin n) (Fin n) L.O` to `Matrix.of fun i j => ⟨M i j, hMO i j⟩`. Establish `hM' : f.mapMatrix M' = M`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hdet : M'.det = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : f M'.det = (f.mapMatrix M').det` using `RingHom.map_det f M'`.

Establish `h2 : M.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (M := M) (fun i j hij => hlow i j hij)]`. Simplify using `[hdiag]`. Express the relevant statement in the definitionally equal form `f M'.det = f 1`. Rewrite using `[h1, hM', h2, map_one]`.

Establish `hu : IsUnit M'.det` using `by rw [hdet]; exact isUnit_one`. Use `⟨f.mapMatrix M'⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]`. Rewrite using `[← hM', ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]`. Introduce `i j set Mi := f.mapMatrix M'⁻¹ with hMi`.

Establish `hinv : Mi * M = 1`. Rewrite using `[hMi, ← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]`. Establish `key : Mi - 1 = -(Mi * (M - 1))`. Rewrite using `[Matrix.mul_sub, hinv, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.

Use `choose o ho he using hcl`. Use `⟨-(∑ k, (M'⁻¹ i k : E) * o k j), ?_, ?_⟩` and prove the remaining obligations. Conclude with `L.O.neg_mem (L.O.sum_mem fun k _ => L.O.mul_mem (M'⁻¹ i k).2 (ho k j))`. Rewrite using `[key, Matrix.neg_apply, Matrix.mul_apply]`. Simplify using `only [he]`.

Rewrite using `[mul_neg, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[hMi, f]`. Expand and normalize the polynomial expressions, which then agree.
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
