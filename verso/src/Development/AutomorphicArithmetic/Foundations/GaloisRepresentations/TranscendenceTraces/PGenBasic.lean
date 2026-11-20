import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem genPt_exists_spec {S : Scheme.{0}} (s : S) : ∃ t : S, t ⤳ s ∧ GenPt t := by
  have hC : IsIrreducible (irreducibleComponent s) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent s) := isClosed_irreducibleComponent
  have ht : IsGenericPoint hC.genericPoint (irreducibleComponent s) :=
    hC.isGenericPoint_genericPoint hcl
  refine ⟨hC.genericPoint, ht.specializes mem_irreducibleComponent, ?_⟩
  intro t' h'
  have hsub : irreducibleComponent s ⊆ closure {t'} := by
    rw [← ht.def]
    exact h'.closure_subset
  have heq : closure ({t'} : Set S) = irreducibleComponent s :=
    eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  have ht' : IsGenericPoint t' (irreducibleComponent s) := heq
  exact ht'.eq ht

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem genPt_open {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (s : U) :
    GenPt (j s) ↔ GenPt s := by
  have he := j.isOpenEmbedding
  constructor
  · intro h t hts
    exact he.injective (h _ (hts.map he.continuous))
  · intro h t hts
    have hmem : t ∈ Set.range j := hts.mem_open he.isOpen_range ⟨s, rfl⟩
    obtain ⟨t', rfl⟩ := hmem
    have : t' ⤳ s := he.isInducing.specializes_iff.1 hts
    rw [h t' this]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
private theorem genPt_integral (S : Scheme.{0}) [IsIntegral S] (s : S) :
    GenPt s ↔ s = genericPoint S := by
  constructor
  · intro h
    exact (h _ (genericPoint_specializes s)).symm
  · rintro rfl t ht
    exact (ht.antisymm (genericPoint_specializes t)).eq

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.Gal.TranscendenceTraces.genBasic_of :
    GenBasic := by
  refine ⟨fun S => ?_, fun j _ s => genPt_open j s, fun S _ s => genPt_integral S s⟩
  rw [dense_iff_inter_open]
  rintro N hN ⟨s, hs⟩
  obtain ⟨t, hts, ht⟩ := genPt_exists_spec s
  exact ⟨t, hts.mem_open hN hs, ht⟩
