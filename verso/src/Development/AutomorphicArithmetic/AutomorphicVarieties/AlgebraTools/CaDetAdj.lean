import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `P _ ι _ _ z m Q hQ hrel ⟨j, hj⟩`. Establish `hzm : ∀ k, z.mulVec m k ∈ Q` using `fun k => hrel (Ideal.subset_span ⟨k, rfl⟩)`. Establish `hdet : z.det * m j ∈ Q`. Establish `h1 : (z.adjugate.mulVec (z.mulVec m)) j = z.det * m j`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Simplify using the standard rewrite rules. Rewrite using `[← h1, Matrix.mulVec, dotProduct]`. Conclude with `Q.sum_mem fun k _ => Q.mul_mem_left _ (hzm k)`. Establish `hd : z.det ∈ Q` using `(hQ.mem_or_mem hdet).resolve_right hj`. Conclude with `sup_le hrel ((Ideal.span_singleton_le_iff_mem _).mpr hd)`.
-/
theorem UpperTheory.V.AlgebraTools.det_mem_of_rel :
    ∀ (P : Type) [CommRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P)
      (Q : Ideal P), Q.IsPrime → relIdeal z m ≤ Q → (∃ j, m j ∉ Q) → detIdeal z m ≤ Q := by
  intro P _ ι _ _ z m Q hQ hrel ⟨j, hj⟩
  have hzm : ∀ k, z.mulVec m k ∈ Q := fun k => hrel (Ideal.subset_span ⟨k, rfl⟩)
  have hdet : z.det * m j ∈ Q := by
    have h1 : (z.adjugate.mulVec (z.mulVec m)) j = z.det * m j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [← h1, Matrix.mulVec, dotProduct]
    exact Q.sum_mem fun k _ => Q.mul_mem_left _ (hzm k)
  have hd : z.det ∈ Q := (hQ.mem_or_mem hdet).resolve_right hj
  exact sup_le hrel ((Ideal.span_singleton_le_iff_mem _).mpr hd)
