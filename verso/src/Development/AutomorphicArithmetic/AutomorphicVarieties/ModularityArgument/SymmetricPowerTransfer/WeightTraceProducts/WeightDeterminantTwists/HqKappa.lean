import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

open Polynomial
namespace UpperTheory.V.Z.Sym.Wt
/- English proof (translation)
Establish `e : ∀ i, hq (2 + τ) (2 + τ) (i + 2) = (2 + τ) * hq (2 + τ) (2 + τ) (i + 1) - (2 + τ) * hq (2 + τ) (2 + τ) i` using `fun i => hq.eq_3 _ _ i`. Establish `f : ∀ i, hq τ 1 (i + 2) = τ * hq τ 1 (i + 1) - 1 * hq τ 1 i` using `fun i => hq.eq_3 _ _ i`. Proceed by induction on `j with`. Consider the case `zero`. Establish `e2 : hq (2 + τ) (2 + τ) 2 = (2 + τ) * hq (2 + τ) (2 + τ) 1 - (2 + τ) * hq (2 + τ) (2 + τ) 0` using `e 0`.

Establish `e3 : hq (2 + τ) (2 + τ) 3 = (2 + τ) * hq (2 + τ) (2 + τ) 2 - (2 + τ) * hq (2 + τ) (2 + τ) 1` using `e 1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show hq (2 + τ) (2 + τ) 1 = (2 + τ) ^ 1 * hq τ 1 0`. Rewrite using `[hq.eq_2, hq.eq_1]`. Expand and normalize the polynomial expressions, which then agree.

Use `show hq (2 + τ) (2 + τ) 3 = (2 + τ) ^ 2 * hq τ 1 1`. Rewrite using `[e3, e2, hq.eq_2, hq.eq_1, hq.eq_2]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ j ih`. Use `⟨ih.2, ?_⟩` and prove the remaining obligations.

Establish `e5 : hq (2 + τ) (2 + τ) (2 * j + 5) = (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 4) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3)` using `e (2 * j + 3)`. Establish `e4 : hq (2 + τ) (2 + τ) (2 * j + 4) = (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2)` using `e (2 * j + 2)`. Establish `e3 : hq (2 + τ) (2 + τ) (2 * j + 3) = (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 1)` using `e (2 * j + 1)`. Establish `f2 : hq τ 1 (j + 2) = τ * hq τ 1 (j + 1) - 1 * hq τ 1 j` using `f j`. Establish `i0 : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j` using `ih.1`.

Establish `i1 : hq (2 + τ) (2 + τ) (2 * j + 3) = (2 + τ) ^ (j + 2) * hq τ 1 (j + 1)` using `ih.2`. Use `show hq (2 + τ) (2 + τ) (2 * j + 5) = (2 + τ) ^ (j + 3) * hq τ 1 (j + 2)`. Rewrite using `[f2]`. Take the linear combination `e5 + (2 + τ) * e4 + (2 + τ) * e3 + ((2 + τ) ^ 2 - 2 * (2 + τ)) * i1 - (2 + τ) ^ 2 * i0`.
-/
private theorem hq_kap (τ : ℂ) (j : ℕ) : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j ∧ hq (2 + τ) (2 + τ) (2 * (j+1) + 1) = (2 + τ) ^ (j + 2) * hq τ 1 (j+1) := by
  have e : ∀ i, hq (2 + τ) (2 + τ) (i + 2) = (2 + τ) * hq (2 + τ) (2 + τ) (i + 1) - (2 + τ) * hq (2 + τ) (2 + τ) i :=
    fun i => hq.eq_3 _ _ i
  have f : ∀ i, hq τ 1 (i + 2) = τ * hq τ 1 (i + 1) - 1 * hq τ 1 i := fun i => hq.eq_3 _ _ i
  induction j with
  | zero =>
    have e2 : hq (2 + τ) (2 + τ) 2 = (2 + τ) * hq (2 + τ) (2 + τ) 1 - (2 + τ) * hq (2 + τ) (2 + τ) 0 := e 0
    have e3 : hq (2 + τ) (2 + τ) 3 = (2 + τ) * hq (2 + τ) (2 + τ) 2 - (2 + τ) * hq (2 + τ) (2 + τ) 1 := e 1
    refine ⟨?_, ?_⟩
    · show hq (2 + τ) (2 + τ) 1 = (2 + τ) ^ 1 * hq τ 1 0
      rw [hq.eq_2, hq.eq_1]
      ring
    · show hq (2 + τ) (2 + τ) 3 = (2 + τ) ^ 2 * hq τ 1 1
      rw [e3, e2, hq.eq_2, hq.eq_1, hq.eq_2]
      ring
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have e5 : hq (2 + τ) (2 + τ) (2 * j + 5) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 4) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) := e (2 * j + 3)
    have e4 : hq (2 + τ) (2 + τ) (2 * j + 4) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) := e (2 * j + 2)
    have e3 : hq (2 + τ) (2 + τ) (2 * j + 3) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 1) := e (2 * j + 1)
    have f2 : hq τ 1 (j + 2) = τ * hq τ 1 (j + 1) - 1 * hq τ 1 j := f j
    have i0 : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j := ih.1
    have i1 : hq (2 + τ) (2 + τ) (2 * j + 3) = (2 + τ) ^ (j + 2) * hq τ 1 (j + 1) := ih.2
    show hq (2 + τ) (2 + τ) (2 * j + 5) = (2 + τ) ^ (j + 3) * hq τ 1 (j + 2)
    rw [f2]
    linear_combination e5 + (2 + τ) * e4 + (2 + τ) * e3 + ((2 + τ) ^ 2 - 2 * (2 + τ)) * i1 - (2 + τ) ^ 2 * i0
/- English proof (translation)
Introduce `j τ` and use `(hq_kap τ j).1`.
-/
theorem hqKappa : HqKappa := fun j τ => (hq_kap τ j).1
end UpperTheory.V.Z.Sym.Wt
