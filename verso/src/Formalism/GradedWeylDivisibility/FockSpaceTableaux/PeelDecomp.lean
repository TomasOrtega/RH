import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCpeelLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `B _ r n l j hlj a0 ω g hg`. Establish `key : ∀ m ∈ g.support, m (a0, l) + m (a0, j) = ω (a0, l)`. Introduce `m hm`. Establish `hw` using `hg (mem_support_iff.1 hm)`. Use `lcpeel_weight_apply l j hlj m a0 l` as an intermediate fact.

Rewrite `this` using `[hw]`. Simplify using `using this.symm`. Establish `hterm : ∀ k, X (a0, l) ^ k * X (a0, j) ^ (ω (a0, l) - k) * peel l j a0 k g = ∑ m ∈ g.support.filter (fun m => m (a0, l) = k), monomial m (coeff m g)`. Introduce `k`. Unfold `peel`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `m hm`. Take `⟨hm1, hm2⟩` from `Finset.mem_filter.1 hm`. Establish `hkey` using `key m hm1`.

Rewrite using `[X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul, one_mul, one_mul]`. Use `congrArg (fun e => monomial e (coeff m g)) ?_` and prove the remaining obligations. Use extensionality with `⟨b, t⟩`. Simplify using `only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply, Prod.mk.injEq]`. Break down `eq_or_ne b a0 with rfl | hb` into its components or cases.

Break down `eq_or_ne t l with rfl | ht` into its components or cases. Simplify using `only [hlj, hlj.symm, and_true, and_false, if_true, if_false]`. Use linear arithmetic over natural numbers and integers. Break down `eq_or_ne t j with rfl | ht'` into its components or cases. Simplify using `only [ht, Ne.symm ht, and_true, and_false, if_true, if_false]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[ht, ht', Ne.symm ht, Ne.symm ht']`. Simplify using `[hb, Ne.symm hb]`. Rewrite using `[Finset.sum_congr rfl (fun k _ => hterm k)]`. Establish `hmaps : ∀ m ∈ g.support, (fun m : Fin r × Fin n →₀ ℕ => m (a0, l)) m ∈ Finset.range (ω (a0, l) + 1)`.

Introduce `m hm`. Use `key m hm` as an intermediate fact. Use `show m (a0, l) ∈ _`. Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.

Establish `hfib` using `Finset.sum_fiberwise_of_maps_to hmaps (fun m => monomial m (coeff m g))`. Conclude with `(hfib.trans (as_sum g).symm).symm`.
-/
theorem peelDecomposition : PeelDecomp := by
  intro B _ r n l j hlj a0 ω g hg
  have key : ∀ m ∈ g.support, m (a0, l) + m (a0, j) = ω (a0, l) := by
    intro m hm
    have hw := hg (mem_support_iff.1 hm)
    have := lcpeel_weight_apply l j hlj m a0 l
    rw [hw] at this
    simpa using this.symm
  have hterm : ∀ k, X (a0, l) ^ k * X (a0, j) ^ (ω (a0, l) - k) * peel l j a0 k g =
      ∑ m ∈ g.support.filter (fun m => m (a0, l) = k), monomial m (coeff m g) := by
    intro k
    unfold peel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    have hkey := key m hm1
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul, one_mul, one_mul]
    refine congrArg (fun e => monomial e (coeff m g)) ?_
    ext ⟨b, t⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply, Prod.mk.injEq]
    rcases eq_or_ne b a0 with rfl | hb
    · rcases eq_or_ne t l with rfl | ht
      · simp only [hlj, hlj.symm, and_true, and_false, if_true, if_false]
        omega
      · rcases eq_or_ne t j with rfl | ht'
        · simp only [ht, Ne.symm ht, and_true, and_false, if_true, if_false]
          omega
        · simp [ht, ht', Ne.symm ht, Ne.symm ht']
    · simp [hb, Ne.symm hb]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hmaps : ∀ m ∈ g.support, (fun m : Fin r × Fin n →₀ ℕ => m (a0, l)) m ∈ Finset.range (ω (a0, l) + 1) := by
    intro m hm
    have := key m hm
    show m (a0, l) ∈ _
    rw [Finset.mem_range]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun m => monomial m (coeff m g))
  exact (hfib.trans (as_sum g).symm).symm

end Formalism.GradedWeylDivisibility
