import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.QuasiCompactOfProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ResidueExistence.ResEx

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

/- English proof (translation)
Introduce `h l _ K _ _ _ f hf hc ϖ hϖ M hM n j T hr hPt A hA B₀`. Take `⟨r⟩` from `UpperTheory.Gal.CD.resEx l K`. Establish `hx : ∀ x : r.k, x ^ l ^ f = x`. Establish `hker : RingHom.ker r.ρ = IsLocalRing.maximalIdeal (OK l K)`. Establish `hm : (RingHom.ker r.ρ).IsMaximal` using `RingHom.ker_isMaximal_of_surjective r.ρ r.surj`.

Conclude with `IsLocalRing.eq_maximalIdeal hm`. Establish `e : IsLocalRing.ResidueField (OK l K) ≃+* r.k` using `(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective r.surj)`. Establish `hcard : Nat.card r.k = l ^ f`. Rewrite using `[← Nat.card_congr e.toEquiv]`. Conclude with `hc`.

Establish `hfin : Finite r.k` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)`. Use `Fintype.ofFinite r.k` as an intermediate fact. Introduce `x`. Rewrite using `[← hcard, Nat.card_eq_fintype_card]`. Conclude with `FiniteField.pow_card x`.

Conclude with `UpperTheory.Ru.crystallineComparison.final l K r f hf hx (h l K r f hf) ϖ hϖ M hM n j T hr hPt A hA B₀`.
-/
theorem UpperTheory.Ru.crystallineComparison.finAll_of :
    (∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ), 0 < f → CIn l K r f) → UpperTheory.Gal.crystallineComparison.Br.FinAll := by
  intro h l _ K _ _ _ f hf hc ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨r⟩ := UpperTheory.Gal.CD.resEx l K
  have hx : ∀ x : r.k, x ^ l ^ f = x := by
    have hker : RingHom.ker r.ρ = IsLocalRing.maximalIdeal (OK l K) := by
      have hm : (RingHom.ker r.ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective r.ρ r.surj
      exact IsLocalRing.eq_maximalIdeal hm
    have e : IsLocalRing.ResidueField (OK l K) ≃+* r.k :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective r.surj)
    have hcard : Nat.card r.k = l ^ f := by
      rw [← Nat.card_congr e.toEquiv]
      exact hc
    have hfin : Finite r.k :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    have := Fintype.ofFinite r.k
    intro x
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  exact UpperTheory.Ru.crystallineComparison.final l K r f hf hx (h l K r f hf) ϖ hϖ M hM n j T hr hPt A hA B₀
