import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
open IsDedekindDomain Polynomial
open scoped nonZeroDivisors

namespace GlobalTheory.OrdTransport

/- English proof (translation)
Introduce `A F _ _ _ _ _ τ σ hc v w hvw x hx`. Establish `h : v.asIdeal = w.asIdeal.comap τ` using `Ideal.ext fun a => by`. Rewrite using `[Ideal.mem_comap]`. Conclude with `hvw a`. Establish `hv : v.valuation F x = w.valuation F (σ x)`.

Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := A) x`. Rewrite using `[map_div₀ σ, hc, hc, map_div₀, map_div₀]`. Simplify using `only [HeightOneSpectrum.valuation_of_algebraMap, GlobalTheory.QNorm.intValuation_of_eq_comap τ w v h]`. Establish `hσx : σ x ≠ 0` using `(map_ne_zero σ).2 hx`. Rewrite `hv` using `[GlobalTheory.Idele.valuation_eq_exp_neg_count v hx, GlobalTheory.Idele.valuation_eq_exp_neg_count w hσx, WithZero.exp_inj, neg_inj]`.

Conclude with `hv.symm`.
-/
theorem count_spanSingleton_ringEquiv : ∀ (A F : Type) [CommRing A] [IsDedekindDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] (τ : A ≃+* A) (σ : F ≃+* F),
    (∀ a : A, σ (algebraMap A F a) = algebraMap A F (τ a)) → ∀ v w : HeightOneSpectrum A,
    (∀ a : A, a ∈ v.asIdeal ↔ τ a ∈ w.asIdeal) → ∀ x : F, x ≠ 0 →
    FractionalIdeal.count F w (FractionalIdeal.spanSingleton A⁰ (σ x)) =
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton A⁰ x) := by
  intro A F _ _ _ _ _ τ σ hc v w hvw x hx
  have h : v.asIdeal = w.asIdeal.comap τ := Ideal.ext fun a => by
    rw [Ideal.mem_comap]; exact hvw a
  have hv : v.valuation F x = w.valuation F (σ x) := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [map_div₀ σ, hc, hc, map_div₀, map_div₀]
    simp only [HeightOneSpectrum.valuation_of_algebraMap,
      GlobalTheory.QNorm.intValuation_of_eq_comap τ w v h]
  have hσx : σ x ≠ 0 := (map_ne_zero σ).2 hx
  rw [GlobalTheory.Idele.valuation_eq_exp_neg_count v hx, GlobalTheory.Idele.valuation_eq_exp_neg_count w hσx,
    WithZero.exp_inj, neg_inj] at hv
  exact hv.symm

end GlobalTheory.OrdTransport
