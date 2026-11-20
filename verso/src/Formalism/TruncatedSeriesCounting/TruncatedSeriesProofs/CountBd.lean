import Formalism.TruncatedSeriesCounting.WindowSeparated

noncomputable section

open Classical

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

open Formalism.WachCohomologyFacts

/- English proof (translation)
Rewrite using `[V2.ClN, Multiset.mem_filter]`. Use `⟨hu, ?_⟩` and prove the remaining obligations. Unfold `V2.InWinN`. Simplify using `only [Bool.false_eq_true, if_false]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma mem_cl {h η : ℕ} {U : Multiset ℤ} {u : ℤ} (hu : u ∈ U) (hc : u < (h : ℤ) - η) :
    u ∈ V2.ClN false h η U := by
  rw [V2.ClN, Multiset.mem_filter]
  refine ⟨hu, ?_⟩
  unfold V2.InWinN
  simp only [Bool.false_eq_true, if_false]
  omega

/- English proof (translation)
Use `hT3 u (mem_cl hu hc) k hk1 hk2` as an intermediate fact. Simplify `this` using `only [Bool.false_eq_true, if_false]`.
-/
private lemma t3 {ℓ h η : ℕ} {σ : ℤ} {U : Multiset ℤ} (hT3 : V2.ResidueAvoidance ℓ false h η σ U) {u : ℤ}
    (hu : u ∈ U) (hc : u < (h : ℤ) - η) (k : ℤ) (hk1 : -2 * σ - 2 ≤ k)
    (hk2 : k ≤ (η : ℤ) + 2 * σ + 3) : ((((h : ℤ) - u : ℤ)) : ZMod ℓ) ≠ ((k : ℤ) : ZMod ℓ) := by
  have := hT3 u (mem_cl hu hc) k hk1 hk2
  simpa only [Bool.false_eq_true, if_false] using this

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[Finset.Icc_eq_empty (by omega)]`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Establish `hs : Finset.Icc a (a - 1 + ((k + 1 : ℕ) : ℤ)) = insert (a + k) (Finset.Icc a (a - 1 + k))`. Use extensionality with `x`. Simplify using `only [Finset.mem_insert, Finset.mem_Icc]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Establish `hn : a + k ∉ Finset.Icc a (a - 1 + k)` using `by rw [Finset.mem_Icc]; omega`. Rewrite using `[hs, Finset.sum_insert hn, Finset.sum_insert hn]`. Establish `e1 : ((((a + ((k + 1 : ℕ) : ℤ)) : ℤ)) : ZMod ℓ) = ((((a + k : ℤ))) : ZMod ℓ) + 1` using `by push_cast; ring`. Rewrite using `[e1]`. Use `hrel ((((a + k : ℤ))) : ZMod ℓ)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
private lemma tele {ℓ : ℕ} (f g M : ZMod ℓ → ℕ) (hrel : ∀ x, f x + M (x + 1) = g x + M x)
    (a : ℤ) (k : ℕ) :
    (∑ n ∈ Finset.Icc a (a - 1 + k), f (((n : ℤ)) : ZMod ℓ)) + M ((((a + k : ℤ))) : ZMod ℓ) =
      (∑ n ∈ Finset.Icc a (a - 1 + k), g (((n : ℤ)) : ZMod ℓ)) + M (((a : ℤ)) : ZMod ℓ) := by
  induction k with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ k ih =>
    have hs : Finset.Icc a (a - 1 + ((k + 1 : ℕ) : ℤ)) = insert (a + k) (Finset.Icc a (a - 1 + k)) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
    have hn : a + k ∉ Finset.Icc a (a - 1 + k) := by rw [Finset.mem_Icc]; omega
    rw [hs, Finset.sum_insert hn, Finset.sum_insert hn]
    have e1 : ((((a + ((k + 1 : ℕ) : ℤ)) : ℤ)) : ZMod ℓ) = ((((a + k : ℤ))) : ZMod ℓ) + 1 := by
      push_cast; ring
    rw [e1]
    have := hrel ((((a + k : ℤ))) : ZMod ℓ)
    omega

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo
