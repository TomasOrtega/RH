import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverageStatement

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem avg_add_of_per : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  intro G _ _ _ _ _ _ Γ hΓ Φ Φ' h h'
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hs : Per Γ (fun x => Φ x + Φ' x) :=
    ⟨h.1.add h'.1, fun γ hγ x => by simp only [h.2 γ hγ x, h'.2 γ hγ x]⟩
  obtain ⟨-, -, i1, e1⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ h
  obtain ⟨-, -, i2, e2⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ' h'
  obtain ⟨-, -, -, e3⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF _ hs
  rw [h1] at e1 e2 e3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at e1 e2 e3
  rw [← e1, ← e2, ← e3]
  exact integral_add i1 i2

end GlobalTheory.CuspGeneric
