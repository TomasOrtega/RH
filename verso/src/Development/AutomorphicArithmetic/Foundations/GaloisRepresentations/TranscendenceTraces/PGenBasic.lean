import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `hC : IsIrreducible (irreducibleComponent s)` using `isIrreducible_irreducibleComponent`. Establish `hcl : IsClosed (irreducibleComponent s)` using `isClosed_irreducibleComponent`. Establish `ht : IsGenericPoint hC.genericPoint (irreducibleComponent s)` using `hC.isGenericPoint_genericPoint hcl`. Use `⟨hC.genericPoint, ht.specializes mem_irreducibleComponent, ?_⟩` and prove the remaining obligations. Introduce `t' h'`.

Establish `hsub : irreducibleComponent s ⊆ closure {t'}`. Rewrite using `[← ht.def]`. Conclude with `h'.closure_subset`. Establish `heq : closure ({t'} : Set S) = irreducibleComponent s` using `eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub`. Establish `ht' : IsGenericPoint t' (irreducibleComponent s)` using `heq`.

Conclude with `ht'.eq ht`.
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
Establish `he` using `j.isOpenEmbedding`. Prove the components needed by the constructor for the conclusion. Introduce `h t hts`. Conclude with `he.injective (h _ (hts.map he.continuous))`. Introduce `h t hts`.

Establish `hmem : t ∈ Set.range j` using `hts.mem_open he.isOpen_range ⟨s, rfl⟩`. Take `⟨t', rfl⟩` from `hmem`. Establish `: t' ⤳ s` using `he.isInducing.specializes_iff.1 hts`. Rewrite using `[h t' this]`.
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
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(h _ (genericPoint_specializes s)).symm`. Introduce and unpack `rfl t ht`. Conclude with `(ht.antisymm (genericPoint_specializes t)).eq`.
-/
private theorem genPt_integral (S : Scheme.{0}) [IsIntegral S] (s : S) :
    GenPt s ↔ s = genericPoint S := by
  constructor
  · intro h
    exact (h _ (genericPoint_specializes s)).symm
  · rintro rfl t ht
    exact (ht.antisymm (genericPoint_specializes t)).eq

/- English proof (translation)
Use `⟨fun S => ?_, fun j _ s => genPt_open j s, fun S _ s => genPt_integral S s⟩` and prove the remaining obligations. Rewrite using `[dense_iff_inter_open]`. Introduce and unpack `N hN ⟨s, hs⟩`. Take `⟨t, hts, ht⟩` from `genPt_exists_spec s`. Conclude with `⟨t, hts.mem_open hN hs, ht⟩`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.genBasic_of :
    GenBasic := by
  refine ⟨fun S => ?_, fun j _ s => genPt_open j s, fun S _ s => genPt_integral S s⟩
  rw [dense_iff_inter_open]
  rintro N hN ⟨s, hs⟩
  obtain ⟨t, hts, ht⟩ := genPt_exists_spec s
  exact ⟨t, hts.mem_open hN hs, ht⟩
