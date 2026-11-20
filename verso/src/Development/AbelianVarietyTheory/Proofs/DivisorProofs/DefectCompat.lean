import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvSubstNatMultiplePrimePowConstantStatement

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

/- English proof (translation)
The claim follows from `h.const unit := h.unit comm := h.comm law := by simpa using h`.
-/
theorem isLift_id_of_isLaw {O : Type} [CommRing O] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (h : IsLaw μ) : IsLift (RingHom.id O) μ where
  const := h.const
  unit := h.unit
  comm := h.comm
  law := by simpa using h

/- English proof (translation)
Introduce `p _ O E _ _ _ hF G d c f hf`. Establish `hD` using `QLogDefect.main p O O E (RingHom.id O) hF d c.μ (isLift_id_of_isLaw c.isLaw) ⊤ f hf`. Establish `hex : ∀ n, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0` using `fun n => by`. Take `⟨s, -, hs⟩` from `(T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d) ⊤ _).1.1 (hD n).1`. Use `⟨s, hs, hF.inj ?_⟩` and prove the remaining obligations.

Establish `h0 : ∀ i, constantCoeff (up E (nmul c.μ n) i) = 0` using `fun i => by`. Simplify using `[up, (hD n).2 i]`. Rewrite using `[← constantCoeff_map, hs, map_zero, defect, map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf.1]`. Simplify using `[hf.1]`. Use `⟨hex, fun n s s' hs hs' => ?_⟩` and prove the remaining obligations.

Take `⟨κ, -, hκ⟩` from `(T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1.1 hf.2.2`. Take `⟨s₁, hs₁, -⟩` from `hex p`. Establish `h` using `((T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ).2.2 p s₁ hs₁).2 (p ^ n) s s' hs (by rw [← pow_succ]; exact hs')`. Use `haveI := hF.complete`. Use `⟨c.ev (n + 1) s₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[h, map_add, map_smul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).2.2, Nat.cast_pow]`. Conclude with `add_comm _ _`.
-/
theorem defect_compat : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → (∀ n, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0) ∧ ∀ (n : ℕ) (s s' : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → map (algebraMap O E) s' = defect c.μ (p ^ (n + 1)) f → ∃ z, c.ev (n + 1) s' = G.mulP n (c.ev n s) + (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf
  have hD := QLogDefect.main p O O E (RingHom.id O) hF d c.μ (isLift_id_of_isLaw c.isLaw) ⊤ f hf
  have hex : ∀ n, ∃ s : MvPowerSeries (Fin d) O,
      map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0 := fun n => by
    obtain ⟨s, -, hs⟩ := (T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d) ⊤ _).1.1 (hD n).1
    refine ⟨s, hs, hF.inj ?_⟩
    have h0 : ∀ i, constantCoeff (up E (nmul c.μ n) i) = 0 := fun i => by
      simp [up, (hD n).2 i]
    rw [← constantCoeff_map, hs, map_zero, defect, map_sub,
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf.1]
    simp [hf.1]
  refine ⟨hex, fun n s s' hs hs' => ?_⟩
  obtain ⟨κ, -, hκ⟩ := (T.coeffsInIdealOfPowerSeries_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1.1 hf.2.2
  obtain ⟨s₁, hs₁, -⟩ := hex p
  have h := ((T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ).2.2 p s₁ hs₁).2 (p ^ n) s s' hs
    (by rw [← pow_succ]; exact hs')
  haveI := hF.complete
  refine ⟨c.ev (n + 1) s₁, ?_⟩
  rw [h, map_add, map_smul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).2.2, Nat.cast_pow]
  exact add_comm _ _

end GlobalTheory.QLog
