import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistClassAssociation.TwClassUnique
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GLMeasure

open ValuativeRel

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `letI : (Valued.v (R := k)).RankOne := { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`. Use `haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k`.

Conclude with `⟨secondCountable_of_proper, inferInstance⟩`.
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
Take `⟨_, _⟩` from `secondCountable_t2_local_field k`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Conclude with `(Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) k)).secondCountableTopology`.
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
Take `⟨_, _⟩` from `secondCountable_t2_local_field k`. Use `haveI : SigmaCompactSpace k := inferInstance`. Use `haveI : SigmaCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (SigmaCompactSpace (Fin n → Fin n → k))`. Use `haveI : SigmaCompactSpace (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace`. Conclude with `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) k)).sigmaCompactSpace`.
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
Introduce `k _ _ _ _ n _ _`. Use `haveI := secondCountable_GL k n`. Use `haveI := sigmaCompact_GL k n`. Use `⟨inferInstance, inferInstance, fun μ hμ => ?_⟩` and prove the remaining obligations. Use `haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ`.

Use `infer_instance`.
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
