import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem derivWeierstrassP_add_half_period :
    ∀ (L : PeriodPair) (a t : ℂ), a ∉ L.lattice → 2 * a ∈ L.lattice → t ∉ L.lattice → t + a ∉ L.lattice → L.derivWeierstrassP (t + a) * (L.weierstrassP t - L.weierstrassP a) ^ 2 = -(3 * L.weierstrassP a ^ 2 - L.g₂ / 4) * L.derivWeierstrassP t := by
  intro L a t ha h2 ht hta
  have hd : L.derivWeierstrassP a = 0 :=
    (GlobalTheory.derivWeierstrassP_eq_zero_iff L ha).2 (by rw [← two_mul]; exact h2)
  have hne : L.weierstrassP t ≠ L.weierstrassP a := by
    intro h
    rcases (GlobalTheory.weierstrassP_eq_iff L ht ha).1 h with h' | h'
    · apply hta
      have := L.lattice.add_mem h' h2
      rwa [show t - a + 2 * a = t + a by ring] at this
    · exact hta h'
  obtain ⟨h1, h3⟩ := GlobalTheory.weierstrassP_add L ht ha hne
  have e1 := L.derivWeierstrassP_sq t ht
  have e2 := L.derivWeierstrassP_sq a ha
  rw [h3, h1]
  rw [hd] at e2 ⊢
  have hd0 : L.weierstrassP t - L.weierstrassP a ≠ 0 := sub_ne_zero.2 hne
  generalize L.weierstrassP t = x at *
  generalize L.weierstrassP a = e at *
  generalize L.derivWeierstrassP t = y at *
  generalize L.g₂ = g at *
  generalize L.g₃ = k at *
  have hq : ((y - 0) / (x - e)) ^ 2 = (4 * (x ^ 2 + x * e + e ^ 2) - g) / (x - e) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hd0) hd0]
    linear_combination (x - e) * (e1 - e2)
  rw [hq]
  field_simp
  ring

end GlobalTheory
