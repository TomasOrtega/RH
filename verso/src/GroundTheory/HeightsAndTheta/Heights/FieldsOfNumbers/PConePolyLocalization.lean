import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarUnit
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarSurj
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

set_option maxHeartbeats 400000 in

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP W hW hPW v hv`. Use `hP.isPrime` as an intermediate fact. Use `hW.isPrime` as an intermediate fact. Establish `hA : IsLocalRing (degZeroLoc P {W})` using `h₀ F K ι P hP W hW hPW`. Use `⟨hA, ?_⟩` and prove the remaining obligations.

Set `_` to `(coneVarMap P W hPW v).toRingHom.toAlgebra`. Use `isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))` as an intermediate fact. Establish `hQ : ∀ q : MvPolynomial K (degZeroLoc P {W}), q ∈ ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl ↔ ∃ e, IsUnit (q.coeff e)`. Introduce `q`. Rewrite using `[Ideal.mem_primeCompl_iff, mem_map_C_iff]`.

Use `push Not`. Simplify using `only [mem_maximalIdeal, mem_nonunits_iff, not_not]`. Use `(isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `(hQ y).mp y.2`. Conclude with `h₁ F K ι P hP W hW hPW v hv y e he`.

Take `⟨p, q, e, he, hz⟩` from `h₂ F K ι P hP W hW hPW v hv z`. Conclude with `⟨⟨p, ⟨q, (hQ q).mpr ⟨e, he⟩⟩⟩, hz⟩`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[h₃ F K ι P hP W hW hPW v hv hxy]`.
-/
theorem ConePolyLocalization.proof (h₀ : DegZeroLocLocal.Statement.{u}) (h₁ : ConeVarUnit.Statement.{u})
    (h₂ : ConeVarSurj.Statement.{u}) (h₃ : ConeVarInj.Statement.{u}) :
    ConePolyLocalization.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  have hA : IsLocalRing (degZeroLoc P {W}) := h₀ F K ι P hP W hW hPW
  refine ⟨hA, ?_⟩
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have hQ : ∀ q : MvPolynomial K (degZeroLoc P {W}),
      q ∈ ((maximalIdeal (degZeroLoc P {W})).map
        (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl ↔ ∃ e, IsUnit (q.coeff e) := by
    intro q
    rw [Ideal.mem_primeCompl_iff, mem_map_C_iff]
    push Not
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨e, he⟩ := (hQ y).mp y.2
    exact h₁ F K ι P hP W hW hPW v hv y e he
  · obtain ⟨p, q, e, he, hz⟩ := h₂ F K ι P hP W hW hPW v hv z
    exact ⟨⟨p, ⟨q, (hQ q).mpr ⟨e, he⟩⟩⟩, hz⟩
  · refine ⟨1, ?_⟩
    rw [h₃ F K ι P hP W hW hPW v hv hxy]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
