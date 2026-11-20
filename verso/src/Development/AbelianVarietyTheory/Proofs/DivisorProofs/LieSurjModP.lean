import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveModPrimeEqQuasiLogarithmDefectStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

/- English proof (translation)
Introduce `p _ O E _ _ _ hF G d c l`. Take `⟨b, z, hbz, hl⟩` from `GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow p O G l 1`. Rewrite `hbz` using `[pow_one]`. Take `⟨f, s, y, hf, hs, hy⟩` from `GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect p O E hF G d c b z hbz`. Take `⟨l', hl', -⟩` from `GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL p O E hF G d c f hf`.

Establish `hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w`. Introduce `w`. Take `⟨φ, hφ⟩` from `AugCot.d_surjective _ (w.1 1)`. Establish `h1` using `hl w φ hφ`. Establish `h2` using `hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)`.

Rewrite `h1`, `h2` using `[pow_one]`. Rewrite `h2` using `[hy, map_add, map_smul, smul_eq_mul]`. Establish `h3 : (p : O) ∣ l' w - φ b`. Use `dvd_add h2 (dvd_mul_right (p : O) (φ y))` as an intermediate fact. Rewrite `this` using `[show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring]`. Then use the resulting hypothesis.

Use `dvd_sub h1 h3` as an intermediate fact. Rewrite `this` using `[show l w - φ b - (l' w - φ b) = (l - l') w by simp]`. Then use the resulting hypothesis. Take `⟨l'', hl''⟩` from `GlobalTheory.T.dual_eq_smul_of_forall_dvd' O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv`. Conclude with `⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩`.
-/
theorem lie_surj_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie),
      QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ O E _ _ _ hF G d c l
  obtain ⟨b, z, hbz, hl⟩ := GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow p O G l 1
  rw [pow_one] at hbz
  obtain ⟨f, s, y, hf, hs, hy⟩ := GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect p O E hF G d c b z hbz
  obtain ⟨l', hl', -⟩ := GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL p O E hF G d c f hf
  have hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w := by
    intro w
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    have h1 := hl w φ hφ
    have h2 := hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)
    rw [pow_one] at h1 h2
    rw [hy, map_add, map_smul, smul_eq_mul] at h2
    have h3 : (p : O) ∣ l' w - φ b := by
      have := dvd_add h2 (dvd_mul_right (p : O) (φ y))
      rwa [show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring] at this
    have := dvd_sub h1 h3
    rwa [show l w - φ b - (l' w - φ b) = (l - l') w by simp] at this
  obtain ⟨l'', hl''⟩ := GlobalTheory.T.dual_eq_smul_of_forall_dvd' O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv
  exact ⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩

end GlobalTheory.QLog
