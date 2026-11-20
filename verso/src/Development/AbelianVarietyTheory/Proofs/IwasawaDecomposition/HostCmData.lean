import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

/- English proof (translation)
Introduce `R H`. Use `letI := H.cmStar`. Establish `hcm` using `H.isCMField_hostE`. Establish `hs : ∀ x : H.E, star x = H.conj x` using `bridge_star_holds R H`. Use `⟨⟨inferInstance, fun φ a => ?_, fun P hP => ?_⟩, inferInstance, ?_, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[hs]`. Conclude with `H.conjE_apply _ _`. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)`. Establish `h` using `H.der.unramEF P hP.isPrime hP0`. Take `⟨x, hx⟩` from `not_forall.1 h`.

Use `⟨x, H.conj • x, ?_, fun h' => hx ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Both sides reduce to the same expression. Use `P.neg_mem h'` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis.

Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Rewrite using `[hs]`. Establish `h` using `H.conjE_mem_hostF_iff a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`.

Conclude with `⟨⟨a, h.2 ha⟩, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `h.1 y.2`.
-/
theorem host_cmData : ∀ (R : Ranks) (H : Host R), @CMData H.F H.E _ _ _ _ H.cmStar _ := by
  intro R H
  letI := H.cmStar
  have hcm := H.isCMField_hostE
  have hs : ∀ x : H.E, star x = H.conj x := bridge_star_holds R H
  refine ⟨⟨inferInstance, fun φ a => ?_, fun P hP => ?_⟩, inferInstance, ?_, fun a => ?_⟩
  · rw [hs]
    exact H.conjE_apply _ _
  · have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    have h := H.der.unramEF P hP.isPrime hP0
    obtain ⟨x, hx⟩ := not_forall.1 h
    refine ⟨x, H.conj • x, ?_, fun h' => hx ?_⟩
    · rw [hs]; rfl
    · have := P.neg_mem h'
      rwa [neg_sub] at this
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · rw [hs]
    have h := H.conjE_mem_hostF_iff a
    constructor
    · intro ha
      exact ⟨⟨a, h.2 ha⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact h.1 y.2

end GlobalTheory.Mem
