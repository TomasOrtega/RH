import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
open GlobalTheory.DualWeyl MvPolynomial NumberField Formalism.GradedWeylDivisibility

namespace GlobalTheory.DualWeyl

/- English proof (translation)
Unfold `nabla at hf`. Rewrite `hf` using `[standardMonomialSpanDomain K N N la]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, sz, hsz, I, hshape, rfl⟩` from `hx`.

Introduce `m hm`. Establish `h` using `bidetDominance K N N k sz hsz I m hm`. Rewrite `h` using `[hshape]`. Conclude with `h`. Consider the case `zero`.

Introduce `m hm`. Simplify using `at hm`. Consider the case `add x y _ _ hx hy`. Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases.

Conclude with `hx m h`. Conclude with `hy m h`. Consider the case `smul c x _ hx`. Introduce `m hm`. Conclude with `hx m (support_smul hm)`.
-/
theorem rowDeg_dominated_of_mem_nabla {K : Type} [Field K] {N : ℕ} (la : Fin N → ℕ) (f : Pol N K)
    (hf : f ∈ nabla la K) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, la t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, la t := by
  classical
  unfold nabla at hf
  rw [standardMonomialSpanDomain K N N la] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance K N N k sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : K, f = c • extremal la K := by`. Apply `hwLine K N N le_rfl la hla f hf` to reduce the goal to its premises. Introduce `a b hab k hk`. Assume the negation of the conclusion as `hne`. Establish `hmem` using `rowDivStable K N N la a b k f hf`.

Establish `hht : IsWeightedHomogeneous (lhwinHt N N) f (∑ a : Fin N, (a.val : ℤ) * (la a : ℤ))`. Introduce `d hd`. Rewrite using `[lhwin_weight_ht, hw' hd]`. Establish `hsh` using `lhwin_rowDiv_shift K _ a b k f hht`. Take `⟨d, hd⟩` from `ne_zero_iff.mp hne`.

Establish `e` using `hsh hd`. Rewrite `e` using `[lhwin_weight_ht]`. Simplify using `only [ldrow_weight_rowW] at e`. Establish `dom` using `rowDeg_dominated_of_mem_nabla la _ hmem d (mem_support_iff.mpr hd)`. Establish `hle` using `Formalism.BranchingDeterminantCap.bs_height_le N (rowDeg d) la dom.1 dom.2`.

Establish `hab' : (a.val : ℤ) - b.val ≤ -1`. Establish `: a.val < b.val` using `hab`. Use linear arithmetic over natural numbers and integers. Establish `hk' : (1 : ℤ) ≤ k` using `by exact_mod_cast hk`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : evalAt 1 f = c`. Rewrite using `[hc, map_smul, evalAt_one_extremal, smul_eq_mul, mul_one]`. Rewrite using `[h1]`. Conclude with `hc`.
-/
theorem eq_evalAt_one_smul_extremal_of_rowWeight (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ)
    (hla : Antitone la) (f : Pol N K) (hf : f ∈ nabla la K)
    (hw' : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la) : f = evalAt 1 f • extremal la K := by
  obtain ⟨c, hc⟩ : ∃ c : K, f = c • extremal la K := by
    apply hwLine K N N le_rfl la hla f hf
    intro a b hab k hk
    by_contra hne
    have hmem := rowDivStable K N N la a b k f hf
    have hht : IsWeightedHomogeneous (lhwinHt N N) f (∑ a : Fin N, (a.val : ℤ) * (la a : ℤ)) := by
      intro d hd
      rw [lhwin_weight_ht, hw' hd]
    have hsh := lhwin_rowDiv_shift K _ a b k f hht
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
    have e := hsh hd
    rw [lhwin_weight_ht] at e
    simp only [ldrow_weight_rowW] at e
    have dom := rowDeg_dominated_of_mem_nabla la _ hmem d (mem_support_iff.mpr hd)
    have hle := Formalism.BranchingDeterminantCap.bs_height_le N (rowDeg d) la dom.1 dom.2
    have hab' : (a.val : ℤ) - b.val ≤ -1 := by
      have : a.val < b.val := hab
      omega
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  have h1 : evalAt 1 f = c := by
    rw [hc, map_smul, evalAt_one_extremal, smul_eq_mul, mul_one]
  rw [h1]
  exact hc

end GlobalTheory.DualWeyl
