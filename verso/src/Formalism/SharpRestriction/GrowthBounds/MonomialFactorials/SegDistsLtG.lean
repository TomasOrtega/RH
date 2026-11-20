import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMExists
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RatioConditionOfSegFacts

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
private theorem sort_get_lt_of_lt (s : Finset ℕ) (l u : Fin (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).length)
    (h : l < u) : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l < (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
  have hp := Finset.pairwise_sort s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hn := Finset.sort_nodup s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hle : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≤ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u :=
    hp.rel_get_of_lt h
  have hne : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≠ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
    intro he
    have := (List.nodup_iff_injective_get.mp hn) he
    exact absurd this (ne_of_lt h)
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem segDists_lt {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (l u : Fin (segS TT j)) (h : l < u) :
    (segDists TT j).get l < (segDists TT j).get u := sort_get_lt_of_lt _ l u h

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem segDists_lt_G {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (u : Fin (segS TT j)) :
    (segDists TT j).get u < segG TT j := by
  have hm : (segDists TT j).get u ∈ segDists TT j := List.get_mem _ _
  unfold segDists at hm
  rw [Finset.mem_sort, Finset.mem_image] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  rw [Finset.mem_filter] at hx
  have e : (segDists TT j).get u = cdist (segStart TT j) x := hxe.symm
  rw [e]
  exact hx.2.2.2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem P_step (l u : Fin X.s) (h : l < u) :
    X.p * (X.S C0 CE1 CE2).P X.p u ≤ (X.S C0 CE1 CE2).P X.p l := by
  have h1 := segDists_lt X.L.TT X.j l u h
  have h2 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p * X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u) ≤
    X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get l)
  rw [← pow_succ']
  exact Nat.pow_le_pow_right hp (by omega)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
theorem p_le_P (u : Fin X.s) : X.p ≤ (X.S C0 CE1 CE2).P X.p u := by
  have h1 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p ≤ X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u)
  calc X.p = X.p ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right hp (by omega)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
