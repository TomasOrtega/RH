import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumberFieldPrimeZetaSumAddLogIsBigO
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in

/- English proof (translation)
Introduce `K M _ _ _ _ _ S hS h`. Use `choose P P' hne hP hP' hNP hNP' using h`. Establish `key : ∀ {Q : HeightOneSpectrum (𝓞 M)} {v w : HeightOneSpectrum (𝓞 K)}, Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w` using `fun h₁ h₂ => HeightOneSpectrum.ext (h₁.over.trans h₂.over.symm)`. Set `f : {v // v ∉ S} × Bool → HeightOneSpectrum (𝓞 M)` to `fun x => if x.2 then P x.1 x.1.2 else P' x.1 x.1.2`. Establish `lies : ∀ x, (f x).asIdeal.LiesOver x.1.1.asIdeal`.

Introduce and unpack `⟨⟨v, hv⟩, b⟩`. Consider the cases of `b`. Use `exacts [hP' v hv, hP v hv]`. Use `_root_.GlobalTheory.Mem.ZetaPole.not_injective_double_primes K M S hS f ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨v, hv⟩, b⟩ ⟨⟨w, hw⟩, c⟩ hfe`.

Establish `hvw : v = w` using `key (lies (⟨v, hv⟩, b)) (by rw [hfe]; exact lies _)`. Substitute `hvw` using the available equality. Apply the tactic sequence `cases b <;> cases c`. Both sides reduce to the same expression. Conclude with `absurd hfe.symm (hne v hv)`.

Conclude with `absurd hfe (hne v hv)`. Both sides reduce to the same expression. Introduce and unpack `⟨⟨v, hv⟩, b⟩`. Consider the cases of `b`. Use `exacts [hNP' v hv, hNP v hv]`.
-/
theorem _root_.GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ S hS h
  choose P P' hne hP hP' hNP hNP' using h
  have key : ∀ {Q : HeightOneSpectrum (𝓞 M)} {v w : HeightOneSpectrum (𝓞 K)},
      Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w :=
    fun h₁ h₂ => HeightOneSpectrum.ext (h₁.over.trans h₂.over.symm)
  let f : {v // v ∉ S} × Bool → HeightOneSpectrum (𝓞 M) :=
    fun x => if x.2 then P x.1 x.1.2 else P' x.1 x.1.2
  have lies : ∀ x, (f x).asIdeal.LiesOver x.1.1.asIdeal := by
    rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hP' v hv, hP v hv]
  refine _root_.GlobalTheory.Mem.ZetaPole.not_injective_double_primes K M S hS f ?_ ?_
  · rintro ⟨⟨v, hv⟩, b⟩ ⟨⟨w, hw⟩, c⟩ hfe
    have hvw : v = w := key (lies (⟨v, hv⟩, b)) (by rw [hfe]; exact lies _)
    subst hvw
    cases b <;> cases c
    · rfl
    · exact absurd hfe.symm (hne v hv)
    · exact absurd hfe (hne v hv)
    · rfl
  · rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hNP' v hv, hNP v hv]

end GlobalTheory
