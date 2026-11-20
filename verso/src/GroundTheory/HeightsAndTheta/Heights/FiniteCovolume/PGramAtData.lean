import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GramAtData.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    GramAtData.Statement h v := by
  intro w
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [gramAt, conjTranspose_apply, map_apply, Automorphic.gram_apply]
    change starRingEnd ℂ (w.embedding (h.toSesq (v j) (v i))) = w.embedding (h.toSesq (v i) (v j))
    rw [← embedding_conj (F := F) w.embedding]
    congr 1
    exact h.isSymm.eq (v j) (v i)
  · simp only [gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding

end GroundTheory.Heights₂.Heights.FiniteCovolume
