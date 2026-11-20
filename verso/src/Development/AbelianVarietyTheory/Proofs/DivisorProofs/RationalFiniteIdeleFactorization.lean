import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.RatIdele

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_rat_mul_intUnit : ∀ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∃ (r : ℚˣ) (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧
    t = Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r * u := by
  intro t
  obtain ⟨k, u, hu, he⟩ := GlobalTheory.TwV.Xc.ClsPow.exists_pow_eq_diag_mul t
  have hc : Fintype.card (ClassGroup (𝓞 ℚ)) = 1 := by
    have := Rat.classNumber_eq
    rwa [NumberField.classNumber] at this
  rw [hc, pow_one] at he
  have hinv : ∀ P : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) P) *
        ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) P) = 1 :=
      congrArg (fun s : FiniteAdeleRing (𝓞 ℚ) ℚ => s P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨k, u, ?_, ?_, he⟩
  · intro P
    show (u : FiniteAdeleRing (𝓞 ℚ) ℚ) P ∈ P.adicCompletionIntegers ℚ
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu P]
  · intro P
    show ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) P ∈ P.adicCompletionIntegers ℚ
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hinv P]

end GlobalTheory.RatIdele
