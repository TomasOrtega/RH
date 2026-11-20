import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `key : ∀ a : ℤ, AddMonoidAlgebra.single a (p.coeff a) * AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) = AddMonoidAlgebra.single j (p.coeff a * q.coeff (-a + j))`. Introduce `a`. Rewrite using `[AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]`. Repeatedly rewrite using `[key]`. Establish `hc : (p * q).coeff j = ∑ a ∈ p.coeff.support, p.coeff a * q.coeff (-a + j)`.

Rewrite using `[AddMonoidAlgebra.coeff_mul, Finsupp.sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum]`. Establish `hcond : ∀ b : ℤ, (a + b = j) ↔ (b = -a + j)` using `fun b => by omega`. Repeatedly rewrite using `[hcond]`.

Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with hm`. Both sides reduce to the same expression. Rewrite using `[Finsupp.notMem_support_iff.mp hm, mul_zero]`. Rewrite using `[hc]`.

Use extensionality with `k`. Simplify using `only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply]`. Use `split_ifs with hk`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.Fr.single_coeff_mul {K : Type} [CommRing K] (p q : AddMonoidAlgebra K ℤ) (j : ℤ) :
    AddMonoidAlgebra.single j ((p * q).coeff j) = ∑ a ∈ p.coeff.support,
      AddMonoidAlgebra.single a (p.coeff a) * AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) := by
  classical
  have key : ∀ a : ℤ, AddMonoidAlgebra.single a (p.coeff a) *
      AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) =
        AddMonoidAlgebra.single j (p.coeff a * q.coeff (-a + j)) := by
    intro a
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
  simp_rw [key]
  have hc : (p * q).coeff j = ∑ a ∈ p.coeff.support, p.coeff a * q.coeff (-a + j) := by
    rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.sum]
    have hcond : ∀ b : ℤ, (a + b = j) ↔ (b = -a + j) := fun b => by omega
    simp_rw [hcond]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [Finsupp.notMem_support_iff.mp hm, mul_zero]
  rw [hc]
  ext k
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.finset_sum_apply,
    Finsupp.single_apply]
  split_ifs with hk
  · rfl
  · simp

/- English proof (translation)
Introduce `C K _ _ _ _ P _ h N`. Set `comp : lauSub P → ℤ → lauSub P` to `fun q k => ⟨AddMonoidAlgebra.single k (q.1.coeff k), single_mem_lauSub P (q.2 k)⟩`. Establish `hcomp : ∀ q k, (comp q k).1 = AddMonoidAlgebra.single k (q.1.coeff k)` using `fun _ _ => rfl`. Establish `base : ∀ q : lauSub P, q ∈ vertex h → ∀ k : ℤ, comp q k ∈ vertex h`. Introduce `q hq k`.

Rewrite `hq`, the goal using `[mem_vertex]`. Take `⟨c, hc, hce⟩` from `hq`. Rewrite using `[hcomp, AddMonoidAlgebra.coeff_single]`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality.

Conclude with `⟨c, hc, by rw [Finsupp.single_eq_same, hce]⟩`. Conclude with `⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hk, map_zero]⟩`. Use `show ∀ p : lauSub P, p ∈ vertex h ^ N → ∀ j, comp p j ∈ vertex h ^ N`. Proceed by induction on `N with`. Consider the case `zero`.

Introduce `p _ j`. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Consider the case `succ n ih`. Introduce `p hp`.

Rewrite `hp` using `[pow_succ]`. Use `Submodule.mul_induction_on (C := fun r => ∀ j, comp r j ∈ vertex h ^ (n + 1)) hp ?_ ?_` and prove the remaining obligations. Introduce `x hx y hy j`. Establish `e : comp (x * y) j = ∑ a ∈ x.1.coeff.support, comp x a * comp y (-a + j)`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[AddSubmonoidClass.coe_finset_sum, hcomp, Subalgebra.coe_mul, single_coeff_mul]`. Both sides reduce to the same expression. Rewrite using `[e, pow_succ]`. Conclude with `Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih x hx a) (base y hy _)`. Introduce `x y hx hy j`.

Establish `e : comp (x + y) j = comp x j + comp y j`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hcomp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.single_add]`. Rewrite using `[e]`. Conclude with `add_mem (hx j) (hy j)`.
-/
theorem UpperTheory.V.Fr.alg_homog :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K] {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) (p : lauSub P), p ∈ vertex h ^ N → ∀ j : ℤ, (⟨AddMonoidAlgebra.single j (p.1.coeff j), single_mem_lauSub P (p.2 j)⟩ : lauSub P) ∈ vertex h ^ N := by
  intro C K _ _ _ _ P _ h N
  let comp : lauSub P → ℤ → lauSub P := fun q k =>
    ⟨AddMonoidAlgebra.single k (q.1.coeff k), single_mem_lauSub P (q.2 k)⟩
  have hcomp : ∀ q k, (comp q k).1 = AddMonoidAlgebra.single k (q.1.coeff k) := fun _ _ => rfl
  have base : ∀ q : lauSub P, q ∈ vertex h → ∀ k : ℤ, comp q k ∈ vertex h := by
    intro q hq k
    rw [mem_vertex] at hq ⊢
    obtain ⟨c, hc, hce⟩ := hq
    rw [hcomp, AddMonoidAlgebra.coeff_single]
    by_cases hk : k = 0
    · subst hk
      exact ⟨c, hc, by rw [Finsupp.single_eq_same, hce]⟩
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hk, map_zero]⟩
  show ∀ p : lauSub P, p ∈ vertex h ^ N → ∀ j, comp p j ∈ vertex h ^ N
  induction N with
  | zero =>
    intro p _ j
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro p hp
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun r => ∀ j, comp r j ∈ vertex h ^ (n + 1)) hp ?_ ?_
    · intro x hx y hy j
      have e : comp (x * y) j =
          ∑ a ∈ x.1.coeff.support, comp x a * comp y (-a + j) := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum, hcomp, Subalgebra.coe_mul, single_coeff_mul]
        rfl
      rw [e, pow_succ]
      exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih x hx a) (base y hy _)
    · intro x y hx hy j
      have e : comp (x + y) j = comp x j + comp y j := by
        apply Subtype.ext
        simp only [hcomp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          AddMonoidAlgebra.single_add]
      rw [e]
      exact add_mem (hx j) (hy j)
