import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.HatTripleRepresentations.GradedDegreeZeroLocal
import ReciprocityTheory.GaloisValuations.ArithOfA

open NumberField IsDedekindDomain Pointwise

namespace GlobalTheory.PlaceConjQ

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem eq_of_prime_mem {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have : Fact q.Prime := ⟨hq⟩
  have := v.isPrime
  have := w.isPrime
  have h1 := ((ReciprocityTheory.Gal.liesOver_span_iff q v.asIdeal).2 hv).over
  have h2 := ((ReciprocityTheory.Gal.liesOver_span_iff q w.asIdeal).2 hw).over
  apply HeightOneSpectrum.ext
  ext x
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  have e : Rat.ringOfIntegersEquiv.symm n = algebraMap ℤ (𝓞 ℚ) n :=
    (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n).trans (eq_intCast (algebraMap ℤ (𝓞 ℚ)) n).symm
  rw [e, ← Ideal.mem_comap, ← Ideal.mem_comap]
  change n ∈ v.asIdeal.under ℤ ↔ n ∈ w.asIdeal.under ℤ
  rw [← h1, ← h2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_Ine_smul_iff {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (x σ : Formalism.ConjugateSelfDual.G F Ω) :
    σ ∈ Formalism.MainNotions.V.Lang.Ine (F := F) (x • A) ↔ x⁻¹ * σ * x ∈ Formalism.MainNotions.V.Lang.Ine (F := F) A := by
  constructor
  · intro h
    have := ReciprocityTheory.Gal.conj_mem_Ine_smul (F := F) (A := x • A) (γ := x⁻¹) (σ := σ) h
    rw [inv_inv, inv_smul_smul] at this
    exact this
  · intro h
    have := ReciprocityTheory.Gal.conj_mem_Ine_smul (F := F) (A := A) (γ := x) (σ := x⁻¹ * σ * x) h
    rw [show x * (x⁻¹ * σ * x) * x⁻¹ = σ by group] at this
    exact this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_Dec_smul_iff {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (x σ : Formalism.ConjugateSelfDual.G F Ω) :
    σ ∈ Formalism.MainNotions.V.Lang.Dec (F := F) (x • A) ↔ x⁻¹ * σ * x ∈ Formalism.MainNotions.V.Lang.Dec (F := F) A := by
  rw [Formalism.MainNotions.V.Lang.mem_Dec, Formalism.MainNotions.V.Lang.mem_Dec, mul_smul, mul_smul, inv_smul_eq_iff]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D), Formalism.MainNotions.V.Pf.V3.P4.F_PlcConj V := by
  intro D V q hq A hA
  have : IsAlgClosure ℚ Formalism.BasicNotions.TV.QbarQ := AlgebraicClosure.instIsAlgClosure ℚ
  obtain ⟨v, hv, hqv⟩ := hA
  obtain ⟨w, hw, hqw⟩ := V.plc_above q hq
  obtain rfl := eq_of_prime_mem hq hqv hqw
  obtain ⟨x, hx⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (F := ℚ) hw hv
  refine ⟨x, fun σ => ?_, fun σ => ?_⟩
  · rw [← hx]; exact mem_Ine_smul_iff _ x σ
  · rw [← hx]; exact mem_Dec_smul_iff _ x σ

end GlobalTheory.PlaceConjQ
