import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.HatTripleRepresentations.GradedDegreeZeroLocal
import ReciprocityTheory.GaloisValuations.ArithOfA

open NumberField IsDedekindDomain Pointwise

namespace GlobalTheory.PlaceConjQ

/- English proof (translation)
Establish `: Fact q.Prime` using `⟨hq⟩`. Use `v.isPrime` as an intermediate fact. Use `w.isPrime` as an intermediate fact. Establish `h1` using `((ReciprocityTheory.Gal.liesOver_span_iff q v.asIdeal).2 hv).over`. Establish `h2` using `((ReciprocityTheory.Gal.liesOver_span_iff q w.asIdeal).2 hw).over`.

Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Take `⟨n, rfl⟩` from `Rat.ringOfIntegersEquiv.symm.surjective x`. Establish `e : Rat.ringOfIntegersEquiv.symm n = algebraMap ℤ (𝓞 ℚ) n` using `(eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n).trans (eq_intCast (algebraMap ℤ (𝓞 ℚ)) n).symm`. Rewrite using `[e, ← Ideal.mem_comap, ← Ideal.mem_comap]`.

Express the relevant statement in the definitionally equal form `n ∈ v.asIdeal.under ℤ ↔ n ∈ w.asIdeal.under ℤ`. Rewrite using `[← h1, ← h2]`.
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
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `ReciprocityTheory.Gal.conj_mem_Ine_smul (F := F) (A := x • A) (γ := x⁻¹) (σ := σ) h` as an intermediate fact. Rewrite `this` using `[inv_inv, inv_smul_smul]`. Conclude with `this`.

Introduce `h`. Use `ReciprocityTheory.Gal.conj_mem_Ine_smul (F := F) (A := A) (γ := x) (σ := x⁻¹ * σ * x) h` as an intermediate fact. Rewrite `this` using `[show x * (x⁻¹ * σ * x) * x⁻¹ = σ by group]`. Conclude with `this`.
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
Rewrite using `[Formalism.MainNotions.V.Lang.mem_Dec, Formalism.MainNotions.V.Lang.mem_Dec, mul_smul, mul_smul, inv_smul_eq_iff]`.
-/
theorem mem_Dec_smul_iff {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (x σ : Formalism.ConjugateSelfDual.G F Ω) :
    σ ∈ Formalism.MainNotions.V.Lang.Dec (F := F) (x • A) ↔ x⁻¹ * σ * x ∈ Formalism.MainNotions.V.Lang.Dec (F := F) A := by
  rw [Formalism.MainNotions.V.Lang.mem_Dec, Formalism.MainNotions.V.Lang.mem_Dec, mul_smul, mul_smul, inv_smul_eq_iff]

/- English proof (translation)
Introduce `D V q hq A hA`. Establish `: IsAlgClosure ℚ Formalism.BasicNotions.TV.QbarQ` using `AlgebraicClosure.instIsAlgClosure ℚ`. Take `⟨v, hv, hqv⟩` from `hA`. Take `⟨w, hw, hqw⟩` from `V.plc_above q hq`. Take `rfl` from `eq_of_prime_mem hq hqv hqw`.

Take `⟨x, hx⟩` from `ReciprocityTheory.Gal.exists_smul_eq_of_over (F := ℚ) hw hv`. Use `⟨x, fun σ => ?_, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hx]`. Conclude with `mem_Ine_smul_iff _ x σ`. Rewrite using `[← hx]`.

Conclude with `mem_Dec_smul_iff _ x σ`.
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
