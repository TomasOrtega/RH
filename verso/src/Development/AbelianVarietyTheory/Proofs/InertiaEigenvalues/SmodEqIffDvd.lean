import Mathlib

namespace GlobalTheory.ModularLimit

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem smodEq_iff_dvd {W : Type} [CommRing W] (x a b : W) (k : ℕ) :
    a ≡ b [SMOD ((Ideal.span {x}) ^ k • ⊤ : Submodule W W)] ↔ x ^ k ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dvd_sub_of_le {W : Type} [CommRing W] (x : W) (f : ℕ → W)
    (hf : ∀ k : ℕ, x ^ k ∣ f (k + 1) - f k) {m n : ℕ} (hmn : m ≤ n) :
    x ^ m ∣ f n - f m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hstep : x ^ m ∣ f (n + 1) - f n := (pow_dvd_pow x hmn).trans (hf n)
    have hsplit : f (n + 1) - f m = (f (n + 1) - f n) + (f n - f m) := by ring
    rw [hsplit]
    exact dvd_add hstep ih

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem exists_limit {W : Type} [inst : CommRing W] (x : W)
    [h : IsPrecomplete (Ideal.span {x}) W] (f : ℕ → W)
    (hf : ∀ (k : ℕ), x ^ k ∣ f (k + (1 : ℕ)) - f k) :
    ∃ (z : W), ∀ (k : ℕ), x ^ k ∣ z - f k := by
  obtain ⟨z, hz⟩ := h.prec (f := f) (fun {m n} hmn => by
    rw [smodEq_iff_dvd, dvd_sub_comm]
    exact dvd_sub_of_le x f hf hmn)
  refine ⟨z, fun k => ?_⟩
  have hk := hz k
  rw [smodEq_iff_dvd] at hk
  rwa [dvd_sub_comm]

end GlobalTheory.ModularLimit
