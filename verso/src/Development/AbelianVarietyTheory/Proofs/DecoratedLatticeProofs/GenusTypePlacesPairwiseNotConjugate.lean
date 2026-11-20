import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

/- English proof (translation)
Introduce `D Pg hT PP hP PP' hP' hc`. Establish `hstar : ∀ z : D.host.E, star z = D.host.conj z` using `Formalism.BasicNotions.bridge_star_holds D.R D.host`. Establish `hFfix : ∀ r : 𝓞 D.host.F, D.host.conj ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E)` using `fun r => (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2`. Establish `hle : PP.asIdeal.under (𝓞 D.host.F) ≤ PP'.asIdeal.under (𝓞 D.host.F)`. Introduce `r hr`.

Rewrite `hr`, the goal using `[Ideal.under_def, Ideal.mem_comap]`. Take `⟨c', hc', he⟩` from `hc _ hr`. Establish `: c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[he, hstar, hFfix]`.

Rewrite using `[← this]` and apply the resulting hypothesis. Establish `hmax : (PP.asIdeal.under (𝓞 D.host.F)).IsMaximal`. Rewrite using `[← HeightOneSpectrum.under_asIdeal]`. Conclude with `(HeightOneSpectrum.under (𝓞 D.host.F) PP).isMaximal`. Establish `hne : PP'.asIdeal.under (𝓞 D.host.F) ≠ ⊤`.

Rewrite using `[← HeightOneSpectrum.under_asIdeal]`. Conclude with `(HeightOneSpectrum.under (𝓞 D.host.F) PP').isPrime.ne_top`. Establish `hund : HeightOneSpectrum.under (𝓞 D.host.F) PP' = HeightOneSpectrum.under (𝓞 D.host.F) PP`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Rewrite using `[HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]`.

Conclude with `(hmax.eq_of_le hne hle).symm`. Establish `hgP` using `hT.1 PP hP`. Establish `hgv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal`. Rewrite using `[HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `hgP`.

Take `⟨W, _, hW⟩` from `hT.2 _ hgv`. Establish `e1 : PP = W` using `hW PP ⟨hP, rfl⟩`. Establish `e2 : PP' = W` using `hW PP' ⟨hP', hund⟩`. Establish `e : PP' = PP` using `e2.trans e1.symm`. Substitute `e` using the available equality.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by`. Rewrite `hgP` using `[Nat.cast_mul]`. Break down `PP'.isPrime.mem_or_mem hgP with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`.

Take `⟨x, hx, hxn⟩` from `(GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP' hk).2.2.1`. Take `⟨c', hc', he⟩` from `hc x hx`. Conclude with `hxn c' (he.trans (hstar _)) hc'`.
-/
theorem typePlaces_noConj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg →
    ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg hT PP hP PP' hP' hc
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hFfix : ∀ r : 𝓞 D.host.F,
      D.host.conj ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) :=
    fun r => (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2

  have hle : PP.asIdeal.under (𝓞 D.host.F) ≤ PP'.asIdeal.under (𝓞 D.host.F) := by
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap] at hr ⊢
    obtain ⟨c', hc', he⟩ := hc _ hr
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
      apply RingOfIntegers.ext
      rw [he, hstar, hFfix]
    rwa [← this]
  have hmax : (PP.asIdeal.under (𝓞 D.host.F)).IsMaximal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP).isMaximal
  have hne : PP'.asIdeal.under (𝓞 D.host.F) ≠ ⊤ := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP').isPrime.ne_top
  have hund : HeightOneSpectrum.under (𝓞 D.host.F) PP' = HeightOneSpectrum.under (𝓞 D.host.F) PP := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    exact (hmax.eq_of_le hne hle).symm
  have hgP := hT.1 PP hP
  have hgv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hgP
  obtain ⟨W, _, hW⟩ := hT.2 _ hgv
  have e1 : PP = W := hW PP ⟨hP, rfl⟩
  have e2 : PP' = W := hW PP' ⟨hP', hund⟩
  have e : PP' = PP := e2.trans e1.symm
  subst e

  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    rw [Nat.cast_mul] at hgP
    rcases PP'.isPrime.mem_or_mem hgP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨x, hx, hxn⟩ :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP' hk).2.2.1
  obtain ⟨c', hc', he⟩ := hc x hx
  exact hxn c' (he.trans (hstar _)) hc'

end GlobalTheory.Core.Mi
