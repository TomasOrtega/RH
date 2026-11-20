import Mathlib

namespace GlobalTheory.SingleStatement

/- English proof (translation)
Introduce `p _ ι s g r hr hg`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hr`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Establish `h1 : ‖g a‖ ≤ r` using `hg a (Finset.mem_insert_self a s)`. Establish `h2 : ‖∑ k ∈ s, g k‖ ≤ r` using `ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))`. Conclude with `(PadicComplex.isNonarchimedean p (g a) (∑ k ∈ s, g k)).trans (max_le h1 h2)`.
-/
theorem main : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → ℂ_[p]) {r : ℝ},
    (0 : ℝ) ≤ r → (∀ k ∈ s, ‖g k‖ ≤ r) → ‖∑ k ∈ s, g k‖ ≤ r := by
  intro p _ ι s g r hr hg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖g a‖ ≤ r := hg a (Finset.mem_insert_self a s)
    have h2 : ‖∑ k ∈ s, g k‖ ≤ r := ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))
    exact (PadicComplex.isNonarchimedean p (g a) (∑ k ∈ s, g k)).trans (max_le h1 h2)

end GlobalTheory.SingleStatement
