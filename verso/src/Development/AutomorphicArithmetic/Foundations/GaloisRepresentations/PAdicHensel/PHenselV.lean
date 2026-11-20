import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G1.pHenselV :
    HenselV := by
  intro F _ _ v f a₀ hf h0 h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers F)
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
  obtain ⟨a, ha, hm⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) f hf a₀
    (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h0)
    (h1.map (Ideal.Quotient.mk _))
  refine ⟨a, ha, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm
