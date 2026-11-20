import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem zs_eq_mul_dep_eis : ∀ (k l j : ℕ) (u v A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zs k l u v (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c A u)) (dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1)) := by
  intro k l j u v A A' c c' hjk
  funext n
  unfold Zs mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c A u) p.1 * dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    have hx0 : (x.1 : ℂ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.1 ≠ 0 := fun e => p1 (by rw [← this, e, zero_mul])
      exact_mod_cast this
    have hk : k - 2 = (k - 1 - j - 1) + j := by omega
    have hj : j + 1 - 1 = j := by omega
    rw [hk, hj, pow_add, div_pow]
    field_simp

end GlobalTheory
