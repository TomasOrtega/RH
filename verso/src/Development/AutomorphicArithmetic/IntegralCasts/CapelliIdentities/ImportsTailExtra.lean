import Mathlib

/- English proof (translation)
Introduce `g n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).tsum_eq]`.

Establish `h : ∀ p : ℤ × (Fin n → ℤ), (∏ i : Fin (n+1), g ((Fin.consEquiv (fun _ : Fin (n+1) => ℤ)) p i)) = g p.1 * ∏ i : Fin n, g (p.2 i)`. Introduce `p`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[Fin.consEquiv]`. Repeatedly rewrite using `[h]`.

Rewrite using `[ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin n → ℤ) => g a * ∏ i : Fin n, g (b i))]`. Repeatedly rewrite using `[ENNReal.tsum_mul_left, ih]`. Rewrite using `[ENNReal.tsum_mul_right, pow_succ']`.
-/
theorem UpperTheory.Reformulated.B.Yvb3.main :
    ∀ (g : ℤ → ENNReal) (n : ℕ), ∑' (m : Fin n → ℤ), ∏ i : Fin n, g (m i) = (∑' (k : ℤ), g k) ^ n := by
  intro g n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).tsum_eq]
    have h : ∀ p : ℤ × (Fin n → ℤ),
        (∏ i : Fin (n+1), g ((Fin.consEquiv (fun _ : Fin (n+1) => ℤ)) p i)) = g p.1 * ∏ i : Fin n, g (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.consEquiv]
    simp_rw [h]
    rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin n → ℤ) => g a * ∏ i : Fin n, g (b i))]
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right, pow_succ']
