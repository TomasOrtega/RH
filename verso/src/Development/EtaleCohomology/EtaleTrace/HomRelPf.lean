import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq, aeval_def, eval₂_eq, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : (∑ i ∈ d.support, d i) = m`. Use `hH (mem_support_iff.mp hd)` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum]`.

Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]`. Rewrite using `[IsScalarTower.algebraMap_apply k K (Polynomial K), Polynomial.algebraMap_eq, mul_assoc]`.
-/
theorem homRel_aeval_scale (k K : Type) [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K)
    (H : MvPolynomial (Fin n) k) (m : ℕ) (hH : H.IsHomogeneous m) :
    aeval (fun j => Polynomial.C (v j) * Polynomial.X) H = Polynomial.C (aeval v H) * Polynomial.X ^ m := by
  classical
  rw [aeval_def, eval₂_eq, aeval_def, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : (∑ i ∈ d.support, d i) = m := by
    have := hH (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]
  rw [IsScalarTower.algebraMap_apply k K (Polynomial K), Polynomial.algebraMap_eq, mul_assoc]

/- English proof (translation)
Introduce `k K _ _ _ d hd n hn v`. Use `set x : Fin n → Polynomial K := fun j => Polynomial.C (v j) * Polynomial.X with hx`. Establish `htr : Algebra.trdeg k (Polynomial K) = Algebra.trdeg k K + 1`. Rewrite using `[← trdeg_add_eq (R := k) (S := K) (A := Polynomial K), Polynomial.trdeg_of_isDomain]`. Establish `hni : ¬ AlgebraicIndependent k x`.

Introduce `h`. Establish `h1` using `h.cardinalMk_le_trdeg`. Rewrite `h1` using `[htr, Cardinal.mk_fin]`. Establish `h2 : ((n : ℕ) : Cardinal) ≤ ((d + 1 : ℕ) : Cardinal)` using `by push_cast; exact h1.trans (by gcongr)`. Establish `: n ≤ d + 1` using `by exact_mod_cast h2`.

Use linear arithmetic over natural numbers and integers. Rewrite `hni` using `[algebraicIndependent_iff]`. Use `push Not at hni`. Take `⟨G, hGx, hG0⟩` from `hni`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, homogeneousComponent m G ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hG0` to reduce the goal to its premises. Rewrite using `[← sum_homogeneousComponent G]`. Conclude with `Finset.sum_eq_zero fun i _ => h i`.

Use `⟨m, homogeneousComponent m G, hm, homogeneousComponent_isHomogeneous m G, ?_⟩` and prove the remaining obligations. Establish `hsum : aeval x G = ∑ i ∈ Finset.range (G.totalDegree + 1), Polynomial.C (aeval v (homogeneousComponent i G)) * Polynomial.X ^ i` using `by conv_lhs => rw [← sum_homogeneousComponent G]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => homRel_aeval_scale k K v _ i (homogeneousComponent_isHomogeneous i G)`. Establish `hmem : m ∈ Finset.range (G.totalDegree + 1)`.

Rewrite using `[Finset.mem_range]`. Assume the negation of the conclusion as `h`. Conclude with `hm (homogeneousComponent_eq_zero m G (by omega))`. Establish `hc` using `congrArg (fun p => Polynomial.coeff p m) (hsum.symm.trans hGx)`. Simplify using `only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc`.

Rewrite `hc` using `[Finset.sum_ite_eq, if_pos hmem]`. Then use the resulting hypothesis.
-/
theorem HomRel_of : HomRel := by
  intro k K _ _ _ d hd n hn v
  classical
  set x : Fin n → Polynomial K := fun j => Polynomial.C (v j) * Polynomial.X with hx
  have htr : Algebra.trdeg k (Polynomial K) = Algebra.trdeg k K + 1 := by
    rw [← trdeg_add_eq (R := k) (S := K) (A := Polynomial K), Polynomial.trdeg_of_isDomain]
  have hni : ¬ AlgebraicIndependent k x := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin] at h1
    have h2 : ((n : ℕ) : Cardinal) ≤ ((d + 1 : ℕ) : Cardinal) := by
      push_cast; exact h1.trans (by gcongr)
    have : n ≤ d + 1 := by exact_mod_cast h2
    omega
  rw [algebraicIndependent_iff] at hni
  push Not at hni
  obtain ⟨G, hGx, hG0⟩ := hni
  obtain ⟨m, hm⟩ : ∃ m, homogeneousComponent m G ≠ 0 := by
    by_contra h
    push Not at h
    apply hG0
    rw [← sum_homogeneousComponent G]
    exact Finset.sum_eq_zero fun i _ => h i
  refine ⟨m, homogeneousComponent m G, hm, homogeneousComponent_isHomogeneous m G, ?_⟩
  have hsum : aeval x G = ∑ i ∈ Finset.range (G.totalDegree + 1),
      Polynomial.C (aeval v (homogeneousComponent i G)) * Polynomial.X ^ i := by
    conv_lhs => rw [← sum_homogeneousComponent G]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      homRel_aeval_scale k K v _ i (homogeneousComponent_isHomogeneous i G)
  have hmem : m ∈ Finset.range (G.totalDegree + 1) := by
    rw [Finset.mem_range]
    by_contra h
    exact hm (homogeneousComponent_eq_zero m G (by omega))
  have hc := congrArg (fun p => Polynomial.coeff p m) (hsum.symm.trans hGx)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rwa [Finset.sum_ite_eq, if_pos hmem] at hc

end LateralTheory.EtaleTrace.Cov
