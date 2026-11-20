import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

open Matrix
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h`. Take `⟨u, hu, h0⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h`. Establish `hsum : ((1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)).PosDef` using `(hA.add hB).add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)`. Establish `heq : (1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B) = (1 - Aᴴ * B) + (1 - Aᴴ * B)ᴴ`.

Simplify using `only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]`. Normalize the expressions using the abelian group laws. Rewrite `hsum` using `[heq]`. Establish `hpos` using `hsum.dotProduct_mulVec_pos hu`. Establish `h2 : star u ⬝ᵥ ((1 - Aᴴ * B)ᴴ *ᵥ u) = 0`.

Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h0]`. Simplify using the standard rewrite rules. Rewrite `hpos` using `[Matrix.add_mulVec, dotProduct_add, h0, h2]`. Simplify using `at hpos`.
-/
theorem isUnit_det_one_sub_conjTranspose_mul_of_contractions (P Q : ℕ)
    (A B : Matrix (Fin P) (Fin Q) ℂ) (hA : (1 - Aᴴ * A).PosDef) (hB : (1 - Bᴴ * B).PosDef) :
    IsUnit (1 - Aᴴ * B).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨u, hu, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hsum : ((1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)).PosDef :=
    (hA.add hB).add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)
  have heq : (1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)
      = (1 - Aᴴ * B) + (1 - Aᴴ * B)ᴴ := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [heq] at hsum
  have hpos := hsum.dotProduct_mulVec_pos hu
  have h2 : star u ⬝ᵥ ((1 - Aᴴ * B)ᴴ *ᵥ u) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h0]
    simp
  rw [Matrix.add_mulVec, dotProduct_add, h0, h2] at hpos
  simp at hpos

end GlobalTheory
