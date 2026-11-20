import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqPlGwOrIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesOnto

/- English proof (translation)
Introduce `D k P hP hg`. Establish `hne : P ≠ ⊥`. Introduce `h`. Rewrite `hg` using `[h, Ideal.mem_bot]`. Establish `h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E)` using `by simpa using hg`.

Use `Nat.cast_injective h0` as an intermediate fact. Conclude with `(D.host.g_prime k).ne_zero this`. Set `w : HeightOneSpectrum (𝓞 D.host.E)` to `⟨P, hP, hne⟩`. Establish `hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k)` using `hg`. Take `⟨v, hv | hv⟩` from `GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw`.

Conclude with `⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩`. Use `⟨v, Or.inr ?_⟩ set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc` and prove the remaining obligations. Rewrite using `[Ideal.map_comap_of_equiv]`. Use extensionality with `y`. Rewrite using `[Ideal.mem_comap]`.

Establish `key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]`. Establish `: c (c.symm y) = y` using `c.apply_symm_apply y`. Rewrite using `[← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]`. Both sides reduce to the same expression.

Conclude with `((hv (c.symm y) y key).symm.trans Iff.rfl)`.
-/
theorem prime_eq_plGw_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  intro D k P hP hg
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hg
    have h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E) := by simpa using hg
    have := Nat.cast_injective h0
    exact (D.host.g_prime k).ne_zero this
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP, hne⟩
  have hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := hg
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw
  · exact ⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩
  · refine ⟨v, Or.inr ?_⟩
    set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap]
    have key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E) := by
      rw [← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]
      have : c (c.symm y) = y := c.apply_symm_apply y
      rw [← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]
      rfl
    exact ((hv (c.symm y) y key).symm.trans Iff.rfl)
end GlobalTheory.TypePrimesOnto
