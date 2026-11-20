import Mathlib

open scoped commutatorElement Pointwise

namespace GlobalTheory

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `n hn g`. Establish `h1 : ⁅g, n⁆ ∈ M` using `h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))`. Establish `h2` using `M.mul_mem h1 hn`. Simplify `h2` using `[commutatorElement_def]`.
-/
theorem normal_of_commutator_le {G : Type} [Group G] (M : Subgroup G)
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ M) : M.Normal := by
  constructor
  intro n hn g
  have h1 : ⁅g, n⁆ ∈ M :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
  have h2 := M.mul_mem h1 hn
  simpa [commutatorElement_def] using h2

end GlobalTheory

namespace GlobalTheory

end GlobalTheory
