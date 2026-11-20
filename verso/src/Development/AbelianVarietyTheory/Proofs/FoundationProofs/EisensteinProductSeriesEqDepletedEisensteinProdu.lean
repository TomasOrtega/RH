import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Introduce `k l j u w A A' c c' hjk`. Use function extensionality and compare the values at `n`. Unfold `Zm mul`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : l ∣ p.1 ∨ l ∣ p.2`.

Establish `hz : dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1) p.1 * dep l (eis (j + 1) c' A' w) p.2 = 0`. Apply the tactic sequence `rcases h with h | h <;> simp [dep, h]`. Rewrite using `[hz]`. Simplify using `[h]`. Use `push_neg at h`.

Take `⟨h1, h2⟩` from `h`. Establish `p1 : p.1 ≠ 0` using `fun e => h1 (e ▸ dvd_zero l)`. Establish `p2 : p.2 ≠ 0` using `fun e => h2 (e ▸ dvd_zero l)`. Simplify using `only [dep, eis, h1, h2, p1, p2, if_false, or_self]`. Establish `hsw : ∑ q ∈ p.2.divisorsAntidiagonal, A' (q.1 : ℤ) * ((q.1 : ℂ)) ^ (j + 1 - 1) * w (q.2 : ℤ) = ∑ y ∈ p.2.divisorsAntidiagonal, A' (y.2 : ℤ) * ((y.2 : ℂ)) ^ (j + 1 - 1) * w (y.1 : ℤ)`.

Use `Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun q => ?_) (fun q _ => rfl)` and prove the remaining obligations. Simplify using `only [Nat.mem_divisorsAntidiagonal, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]`. Rewrite using `[hsw, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Establish `hx0 : (x.1 : ℂ) ≠ 0`.

Use `(Nat.mem_divisorsAntidiagonal.mp hx).1` as an intermediate fact. Establish `: x.1 ≠ 0` using `fun e => p1 (by rw [← this, e, zero_mul])`. Conclude with `this` after adjusting the coercions. Establish `hk : k - 2 = (k - 1 - j - 1) + j` using `by omega`. Establish `hj : j + 1 - 1 = j` using `by omega`.

Rewrite using `[hk, hj, pow_add, div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem zm_eq_mul_dep_eis : ∀ (k l j : ℕ) (u w A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zm k l u w (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1)) (dep l (eis (j + 1) c' A' w)) := by
  intro k l j u w A A' c c' hjk
  funext n
  unfold Zm mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1) p.1 * dep l (eis (j + 1) c' A' w) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    have hsw : ∑ q ∈ p.2.divisorsAntidiagonal, A' (q.1 : ℤ) * ((q.1 : ℂ)) ^ (j + 1 - 1) * w (q.2 : ℤ)
        = ∑ y ∈ p.2.divisorsAntidiagonal, A' (y.2 : ℤ) * ((y.2 : ℂ)) ^ (j + 1 - 1) * w (y.1 : ℤ) := by
      refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun q => ?_) (fun q _ => rfl)
      simp only [Nat.mem_divisorsAntidiagonal, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]
    rw [hsw, Finset.sum_mul_sum]
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
