import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `F _ n k m Z f hZ`. Take `⟨c, hc, g, hg, hf⟩` from `hZ`. Use `⟨c ^ m, pow_ne_zero _ hc, g, fun W hW => hg W (Finsupp.support_smul hW), ?_⟩` and prove the remaining obligations. Establish `hsub : (m • Z).support ⊆ Z.support` using `Finsupp.support_smul`. Rewrite using `[Finset.prod_subset hsub (fun W _ hW => by rw [Finsupp.notMem_support_iff.mp hW, pow_zero]), hf, mul_pow, ← map_pow, ← Finset.prod_pow]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun W _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]`.
-/
theorem ChowFormCycleSmul.proof : ChowFormCycleSmul.Statement := by
  intro F _ n k m Z f hZ
  obtain ⟨c, hc, g, hg, hf⟩ := hZ
  refine ⟨c ^ m, pow_ne_zero _ hc, g, fun W hW => hg W (Finsupp.support_smul hW), ?_⟩
  have hsub : (m • Z).support ⊆ Z.support := Finsupp.support_smul
  rw [Finset.prod_subset hsub (fun W _ hW => by rw [Finsupp.notMem_support_iff.mp hW, pow_zero]), hf,
    mul_pow, ← map_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun W _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]

end GroundTheory.Heights₂.Heights
