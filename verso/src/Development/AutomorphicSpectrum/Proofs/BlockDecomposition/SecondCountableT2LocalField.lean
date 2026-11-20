import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistClassAssociation.TwClassUnique
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GLMeasure

open ValuativeRel

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem secondCountable_t2_local_field (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact ⟨secondCountable_of_proper, inferInstance⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem secondCountable_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : SecondCountableTopology (GL (Fin n) k) := by
  obtain ⟨_, _⟩ := secondCountable_t2_local_field k
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) k)).secondCountableTopology

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem sigmaCompact_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : SigmaCompactSpace (GL (Fin n) k) := by
  obtain ⟨_, _⟩ := secondCountable_t2_local_field k
  haveI : SigmaCompactSpace k := inferInstance
  haveI : SigmaCompactSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SigmaCompactSpace (Fin n → Fin n → k))
  haveI : SigmaCompactSpace (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) k)).sigmaCompactSpace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem glMeas : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.GLMeas k := by
  intro k _ _ _ _ n _ _
  haveI := secondCountable_GL k n
  haveI := sigmaCompact_GL k n
  refine ⟨inferInstance, inferInstance, fun μ hμ => ?_⟩
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  infer_instance

end GlobalTheory.CompanionTheory.GLMeasure
