import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

/- English proof (translation)
Introduce `p _ k _ _ _ d μ h hb m hm`. Take `⟨R1, R2, -, -, -, R6, ZariskiNoetherianInduction⟩` from `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)`. Take `⟨-, R2', -, -, -, R6', R7'⟩` from `GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)`. Take `⟨-, C1, -, -⟩` from `GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const`. Proceed by induction on `m using Submodule.Quotient.induction_on with`.

Consider the case `H x`. Take `⟨f, hf⟩` from `x`. Rewrite `hm` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `(p : WittVector p k) • f ∈ intBy p k (Fin d) 1 at hm`.

Express the relevant statement in the definitionally equal form `f ∈ intBy p k (Fin d) 1`. Take `⟨b, hB⟩` from `(R1 _).1 hm`. Establish `hL : ∀ i, constantCoeff (lift p (μ i)) = 0` using `fun i => constantCoeff_lift p (h.const i)`. Establish `hcob : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) = (p : WittVector p k) • cob1 (fun i => lift p (μ i)) f`. Rewrite using `[← algebraMap_smul (Fr p k) (p : WittVector p k) f, formalCoboundary_smul hL, algebraMap_smul]`.

Establish `hcp : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) ∈ intBy p k _ (p : WittVector p k)`. Rewrite using `[hcob, R7']`. Conclude with `⟨_, hf.2, rfl⟩`. Establish `h0 : cob1 μ b = 0` using `R2' _ _ _ (C1 _ _ hB).1 ((R6' _).1 hcp)`. Establish `hb0 : b = 0` using `hb b h0`.

Substitute `hb0` using the available equality. Take `⟨g, hg, hfg⟩` from `(ZariskiNoetherianInduction _ _).1 ((R6 _).2 hB)`. Establish `hp : (algebraMap (WittVector p k) (Fr p k) (p : WittVector p k)) ≠ 0`. Rewrite using `[map_natCast]`. Introduce `h0`.

Use `IsFractionRing.injective (WittVector p k) (Fr p k)` as an intermediate fact. Apply `WittVector.p_nonzero (p := p) (R := k)` to reduce the goal to its premises. Apply `this` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero]`. Conclude with `h0`.

Establish `: f = g`. Use extensionality with `α`. Use `congrArg (coeff α) hfg` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul (Fr p k) (p : WittVector p k) f, ← algebraMap_smul (Fr p k) (p : WittVector p k) g, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Conclude with `mul_left_cancel₀ hp this`.

Rewrite using `[this]`. Conclude with `hg`.
-/
theorem mod_noPTorsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ b, cob1 μ b = 0 → b = 0) → ∀ m : Mod p h, (p : WittVector p k) • m = 0 → m = 0 := by
  intro p _ k _ _ _ d μ h hb m hm
  obtain ⟨R1, R2, -, -, -, R6, ZariskiNoetherianInduction⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  obtain ⟨-, R2', -, -, -, R6', R7'⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, C1, -, -⟩ := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  induction m using Submodule.Quotient.induction_on with
  | H x =>
  obtain ⟨f, hf⟩ := x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  rw [Submodule.Quotient.mk_eq_zero]
  change (p : WittVector p k) • f ∈ intBy p k (Fin d) 1 at hm
  change f ∈ intBy p k (Fin d) 1
  obtain ⟨b, hB⟩ := (R1 _).1 hm
  have hL : ∀ i, constantCoeff (lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hcob : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) =
      (p : WittVector p k) • cob1 (fun i => lift p (μ i)) f := by
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, formalCoboundary_smul hL, algebraMap_smul]
  have hcp : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) ∈ intBy p k _ (p : WittVector p k) := by
    rw [hcob, R7']; exact ⟨_, hf.2, rfl⟩
  have h0 : cob1 μ b = 0 := R2' _ _ _ (C1 _ _ hB).1 ((R6' _).1 hcp)
  have hb0 : b = 0 := hb b h0
  subst hb0
  obtain ⟨g, hg, hfg⟩ := (ZariskiNoetherianInduction _ _).1 ((R6 _).2 hB)
  have hp : (algebraMap (WittVector p k) (Fr p k) (p : WittVector p k)) ≠ 0 := by
    rw [map_natCast]
    intro h0
    have := IsFractionRing.injective (WittVector p k) (Fr p k)
    apply WittVector.p_nonzero (p := p) (R := k)
    apply this; rw [map_natCast, map_zero]; exact h0
  have : f = g := by
    ext α
    have := congrArg (coeff α) hfg
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, ← algebraMap_smul (Fr p k) (p : WittVector p k) g,
      map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact mul_left_cancel₀ hp this
  rw [this]; exact hg

end GlobalTheory.Katz
