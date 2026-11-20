import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Introduce `s hs a ha`. Establish `h` using `Multiset.prod_X_add_C_eq_sum_esymm s`. Establish `hR : ∑ j ∈ Finset.range (s.card + 1), Polynomial.C (s.esymm j) * Polynomial.X ^ (s.card - j) = Polynomial.X ^ s.card`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using `[Multiset.esymm, Multiset.powersetCard_zero_left]`.

Introduce `j _ hj`. Rewrite using `[hs j (Nat.one_le_iff_ne_zero.mpr hj)]`. Simplify using the standard rewrite rules. Introduce `h0`. Conclude with `absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0`.

Rewrite `h` using `[hR]`. Establish `h2` using `congrArg (Polynomial.eval (-a)) h`. Rewrite `h2` using `[Polynomial.eval_multiset_prod, Polynomial.eval_pow, Polynomial.eval_X]`. Establish `h3 : (Multiset.map (Polynomial.eval (-a)) (Multiset.map (fun r => Polynomial.X + Polynomial.C r) s)).prod = 0`. Apply `Multiset.prod_eq_zero` to reduce the goal to its premises.

Rewrite using `[Multiset.map_map]`. Conclude with `Multiset.mem_map.mpr ⟨a, ha, by simp⟩`. Rewrite `h2` using `[h3]`. Conclude with `neg_eq_zero.mp (pow_eq_zero_iff'.mp h2.symm).1`.
-/
theorem esymmZero : esymmZeroStatement := by
  intro s hs a ha
  have h := Multiset.prod_X_add_C_eq_sum_esymm s
  have hR : ∑ j ∈ Finset.range (s.card + 1), Polynomial.C (s.esymm j) * Polynomial.X ^ (s.card - j)
      = Polynomial.X ^ s.card := by
    rw [Finset.sum_eq_single 0]
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro j _ hj
      rw [hs j (Nat.one_le_iff_ne_zero.mpr hj)]
      simp
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  rw [hR] at h
  have h2 := congrArg (Polynomial.eval (-a)) h
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_pow, Polynomial.eval_X] at h2
  have h3 : (Multiset.map (Polynomial.eval (-a))
      (Multiset.map (fun r => Polynomial.X + Polynomial.C r) s)).prod = 0 := by
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨a, ha, by simp⟩
  rw [h3] at h2
  exact neg_eq_zero.mp (pow_eq_zero_iff'.mp h2.symm).1

end ReciprocityTheory.L2DbarEstimates.Norm
