import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicLoc

/- English proof (translation)
Introduce `A _ c p _`. Use `letI := @Module.addCommMonoidToAddCommGroup A`. Use `haveI : Module.FinitePresentation A c := Module.finitePresentation_of_projective A c`. Use `haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl c) := Module.free_of_flat_of_isLocalRing`. Take `⟨f, hf, hfree, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl c) (Localization.AtPrime p)`.

Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Rewrite using `[CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]`. Conclude with `Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) c)`.
-/
theorem exists_away_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A) (p : Ideal A) [p.IsPrime], ∃ f ∉ p, CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1 := by
  intro A _ c p _
  letI := @Module.addCommMonoidToAddCommGroup A
  haveI : Module.FinitePresentation A c := Module.finitePresentation_of_projective A c
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl c) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl c) (Localization.AtPrime p)
  refine ⟨f, hf, ?_⟩
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]
  exact Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) c)

/- English proof (translation)
Introduce `A _ c`. Set `T : Set A` to `{f | CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1}`. Establish `hT : Ideal.span T = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ h`.

Take `⟨f, hf, hf1⟩` from `exists_away_mapAlgebra_eq_one A c m`. Conclude with `hf (hle (Ideal.subset_span hf1))`. Take `⟨s, hsT, hs⟩` from `(Ideal.span_eq_top_iff_finite T).mp hT`. Set `R : s → Type` to `fun i => Localization.Away (i : A)`. Use `haveI : ∀ i, Algebra.Etale A (R i) := fun i => Algebra.Etale.of_isLocalizationAway (i : A)`.

Establish `halg : ∀ i, (Pi.evalRingHom R i).comp (algebraMap A ((i : s) → R i)) = algebraMap A (R i)` using `fun i => RingHom.ext fun _ => rfl`. Use `⟨(i : s) → R i, inferInstance, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Use `Module.FaithfullyFlat.of_comap_surjective fun p => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i : s, (i : A) ∉ p.asIdeal := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Apply `p.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← hs, Ideal.span_le]`. Introduce `x hx`. Conclude with `h ⟨x, hx⟩`.

Establish `hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (R i)))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (R i) (i : A)]`. Conclude with `hi`. Take `⟨q, rfl⟩` from `hp`. Use `⟨PrimeSpectrum.comap (Pi.evalRingHom R i) q, ?_⟩` and prove the remaining obligations.

Rewrite using `[← PrimeSpectrum.comap_comp_apply, halg]`. Apply `GlobalTheory.PicPi.eq_one_of_forall` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom, halg, CommRing.Pic.mapRingHom_algebraMap]`. Conclude with `hsT i.2`.
-/
theorem exists_etale_faithfullyFlat_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  intro A _ c
  classical
  let T : Set A := {f | CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1}
  have hT : Ideal.span T = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hf1⟩ := exists_away_mapAlgebra_eq_one A c m
    exact hf (hle (Ideal.subset_span hf1))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  let R : s → Type := fun i => Localization.Away (i : A)
  haveI : ∀ i, Algebra.Etale A (R i) := fun i => Algebra.Etale.of_isLocalizationAway (i : A)
  have halg : ∀ i, (Pi.evalRingHom R i).comp (algebraMap A ((i : s) → R i)) = algebraMap A (R i) :=
    fun i => RingHom.ext fun _ => rfl
  refine ⟨(i : s) → R i, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, hi⟩ : ∃ i : s, (i : A) ∉ p.asIdeal := by
      by_contra h
      push Not at h
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hs, Ideal.span_le]
      intro x hx
      exact h ⟨x, hx⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (R i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (R i) (i : A)]
      exact hi
    obtain ⟨q, rfl⟩ := hp
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom R i) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, halg]
  · apply GlobalTheory.PicPi.eq_one_of_forall
    intro i
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom, halg,
      CommRing.Pic.mapRingHom_algebraMap]
    exact hsT i.2

end GlobalTheory.PicLoc
