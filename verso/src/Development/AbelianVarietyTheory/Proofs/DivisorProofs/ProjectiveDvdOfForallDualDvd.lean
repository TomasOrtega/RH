import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

/- English proof (translation)
Introduce `O M _ _ _ _ a b h`. Take `⟨s, hs⟩` from `Module.projective_def'.mp (inferInstance : Module.Projective O M)`. Establish `hc : ∀ i : M, a ∣ s b i` using `fun i => h ((Finsupp.lapply i).comp s)`. Use `choose c hc using hc`. Use `⟨∑ i ∈ (s b).support, c i • i, ?_⟩` and prove the remaining obligations.

Establish `hb : Finsupp.linearCombination O id (s b) = b`. Simplify using `using LinearMap.congr_fun hs b`. Rewrite using `[Finset.smul_sum]`. Use `conv_lhs => rw [← hb]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← hc i]`. Both sides reduce to the same expression.
-/
theorem projective_dvd_of_forall_dual_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M),
      (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  intro O M _ _ _ _ a b h
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O M)
  have hc : ∀ i : M, a ∣ s b i := fun i => h ((Finsupp.lapply i).comp s)
  choose c hc using hc
  refine ⟨∑ i ∈ (s b).support, c i • i, ?_⟩
  have hb : Finsupp.linearCombination O id (s b) = b := by
    simpa using LinearMap.congr_fun hs b
  rw [Finset.smul_sum]
  conv_lhs => rw [← hb]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

end GlobalTheory
