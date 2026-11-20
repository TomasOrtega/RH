import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

namespace GlobalTheory.TripleUnramified

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/- English proof (translation)
Simplify using `only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`.
-/
theorem mem_smul_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y ∈ A := by
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

/- English proof (translation)
Rewrite using `[ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', mem_smul_iff, mem_smul_iff, map_inv₀, map_eq_zero_iff _ (AlgEquiv.injective _)]`.
-/
theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', mem_smul_iff, mem_smul_iff,
    map_inv₀, map_eq_zero_iff _ (AlgEquiv.injective _)]

/- English proof (translation)
Rewrite `hσ`, the goal using `[mem_Ine]`. Take `⟨hdec, hval⟩` from `hσ`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hdec' : σ • g • A = g • A` using `hdec show (g⁻¹ * σ * g) • A = A`. Rewrite using `[mul_smul, mul_smul, hdec', inv_smul_smul]`.

Establish `hx' : (g • A).valuation (g x) ≤ 1`. Rewrite using `[ValuationSubring.valuation_le_one_iff, mem_smul_iff, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Conclude with `(ValuationSubring.valuation_le_one_iff _ _).1 hx`. Establish `key` using `(valuation_smul_lt_one_iff A g _).1 (hval (g x) hx')`. Establish `e : (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x`.

Simplify using `[AlgEquiv.mul_apply, map_sub]`. Rewrite `key` using `[e]`. Then use the resulting hypothesis.
-/
theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · have hdec' : σ • g • A = g • A := hdec
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, hdec', inv_smul_smul]
  ·
    have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff, ← AlgEquiv.mul_apply, inv_mul_cancel,
        AlgEquiv.one_apply]
      exact (ValuationSubring.valuation_le_one_iff _ _).1 hx
    have key := (valuation_smul_lt_one_iff A g _).1 (hval (g x) hx')
    have e : (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      simp [AlgEquiv.mul_apply, map_sub]
    rwa [e] at key

end Galois

/- English proof (translation)
Introduce `D bkP i s h v hvl hvg A hA σ hσ`. Take `⟨ι, π₁, π, h1, -, hrow, -⟩` from `h`. Establish `hunr` using `h1.unr v hvl (hrow.unr₁ v hvg)`. Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 v) hA`. Establish `h0` using `hunr _ (conj_mem_Ine_of_smul hσ)`.

Establish `hs : σ = g * (g⁻¹ * σ * g) * g⁻¹` using `by group`. Rewrite using `[hs, map_mul, map_mul, h0, mul_one, ← map_mul, mul_inv_cancel, map_one]`.
-/
theorem unrRho_of_tripleAtt : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → UnrRho i s := by
  intro D bkP i s h v hvl hvg A hA σ hσ
  obtain ⟨ι, π₁, π, h1, -, hrow, -⟩ := h

  have hunr := h1.unr v hvl (hrow.unr₁ v hvg)

  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 v) hA
  have h0 := hunr _ (conj_mem_Ine_of_smul hσ)
  have hs : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
  rw [hs, map_mul, map_mul, h0, mul_one, ← map_mul, mul_inv_cancel, map_one]

end GlobalTheory.TripleUnramified

end
