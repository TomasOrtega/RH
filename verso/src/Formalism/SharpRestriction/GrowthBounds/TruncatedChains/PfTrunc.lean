import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

/- English proof (translation)
Introduce `K V _ _ _ _ _ n E hE a b hab k hk`. Establish `hs` using `gl_rep_shifts_weights hE`. Take `⟨m, hm⟩` from `findim_weights_bounded E`. Establish `h1 : (E a b) ^ (2 * m + 1) = 0`. Establish `hle : (⊤ : Submodule K V) ≤ LinearMap.ker ((E a b) ^ (2 * m + 1))`.

Rewrite using `[← hE.2.2]`. Use `iSup_le fun ν x hx => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`. Assume the negation of the conclusion as `h0`. Establish `hx0 : weightSp E ν ≠ ⊥`.

Introduce `hb`. Rewrite `hx` using `[hb, Submodule.mem_bot]`. Conclude with `h0 (by rw [hx, map_zero])`. Establish `hw` using `operator_pow_shifts_weight hs a b ν (2 * m + 1) x hx`. Establish `hw0 : weightSp E (ν + ((2 * m + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥`.

Introduce `hb`. Rewrite `hw` using `[hb, Submodule.mem_bot]`. Conclude with `h0 hw`. Establish `b1` using `hm _ hx0 a`. Establish `b2` using `hm _ hw0 a`.

Rewrite `b2` using `[Pi.add_apply, root_multiple_apply_first a b hab]`. Rewrite `b1`, `b2` using `[abs_le]`. Move the coercions through the operations in `at b2`. Use linear arithmetic over natural numbers and integers. Conclude with `LinearMap.ker_eq_top.1 (top_le_iff.1 hle)`.

Establish `h2 : LinearMap.ker ((E a b) ^ k) = ⊤`. Rewrite using `[Module.End.ker_pow_eq_ker_pow_finrank_of_le hk, ← Module.End.ker_pow_eq_ker_pow_finrank_of_le (le_max_left (Module.finrank K V) (2 * m + 1)), pow_eq_zero_of_le (le_max_right _ _) h1]`. Conclude with `LinearMap.ker_zero`. Conclude with `LinearMap.ker_eq_top.1 h2`.
-/
theorem restNil : RestNil := by
  intro K V _ _ _ _ _ n E hE a b hab k hk
  have hs := gl_rep_shifts_weights hE
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  have h1 : (E a b) ^ (2 * m + 1) = 0 := by
    have hle : (⊤ : Submodule K V) ≤ LinearMap.ker ((E a b) ^ (2 * m + 1)) := by
      rw [← hE.2.2]
      refine iSup_le fun ν x hx => ?_
      rw [LinearMap.mem_ker]
      by_contra h0
      have hx0 : weightSp E ν ≠ ⊥ := by
        intro hb
        rw [hb, Submodule.mem_bot] at hx
        exact h0 (by rw [hx, map_zero])
      have hw := operator_pow_shifts_weight hs a b ν (2 * m + 1) x hx
      have hw0 : weightSp E (ν + ((2 * m + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥ := by
        intro hb
        rw [hb, Submodule.mem_bot] at hw
        exact h0 hw
      have b1 := hm _ hx0 a
      have b2 := hm _ hw0 a
      rw [Pi.add_apply, root_multiple_apply_first a b hab] at b2
      rw [abs_le] at b1 b2
      push_cast at b2
      omega
    exact LinearMap.ker_eq_top.1 (top_le_iff.1 hle)
  have h2 : LinearMap.ker ((E a b) ^ k) = ⊤ := by
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hk,
      ← Module.End.ker_pow_eq_ker_pow_finrank_of_le (le_max_left (Module.finrank K V) (2 * m + 1)),
      pow_eq_zero_of_le (le_max_right _ _) h1]
    exact LinearMap.ker_zero
  exact LinearMap.ker_eq_top.1 h2

/- English proof (translation)
Establish `hz : ∀ k, Module.finrank K V ≤ k → divPowE E a b k = 0`. Introduce `k hk`. Unfold `divPowE`. Rewrite using `[restNil K V n E hE a b hab k hk, smul_zero]`. Establish `hsum : ∀ S : ℕ, Module.finrank K V ≤ S → pf E a b c S = pf E a b c (Module.finrank K V)`.

Introduce `S hS`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hS`. Unfold `pf`. Rewrite using `[show Module.finrank K V + m + 1 = (Module.finrank K V + 1) + m by ring, Finset.sum_range_add]`. Establish `h0 : ∑ x ∈ Finset.range m, ((-1 : K) ^ (Module.finrank K V + 1 + x) / ((Nat.choose (c + (Module.finrank K V + 1 + x)) (Module.finrank K V + 1 + x) : ℕ) : K)) • (divPowE E b a (Module.finrank K V + 1 + x) * divPowE E a b (Module.finrank K V + 1 + x)) = 0` using `Finset.sum_eq_zero (fun x _ => by rw [hz _ (by omega), mul_zero, smul_zero])`.

Rewrite using `[h0, add_zero]`. Rewrite using `[hsum T hT, hsum T' hT']`.
-/
theorem pf_trunc {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ}
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (hab : a ≠ b) (c T T' : ℕ)
    (hT : Module.finrank K V ≤ T) (hT' : Module.finrank K V ≤ T') : pf E a b c T = pf E a b c T' := by
  have hz : ∀ k, Module.finrank K V ≤ k → divPowE E a b k = 0 := by
    intro k hk
    unfold divPowE
    rw [restNil K V n E hE a b hab k hk, smul_zero]
  have hsum : ∀ S : ℕ, Module.finrank K V ≤ S → pf E a b c S = pf E a b c (Module.finrank K V) := by
    intro S hS
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hS
    unfold pf
    rw [show Module.finrank K V + m + 1 = (Module.finrank K V + 1) + m by ring, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range m, ((-1 : K) ^ (Module.finrank K V + 1 + x) /
        ((Nat.choose (c + (Module.finrank K V + 1 + x)) (Module.finrank K V + 1 + x) : ℕ) : K)) •
        (divPowE E b a (Module.finrank K V + 1 + x) * divPowE E a b (Module.finrank K V + 1 + x)) = 0 :=
      Finset.sum_eq_zero (fun x _ => by rw [hz _ (by omega), mul_zero, smul_zero])
    rw [h0, add_zero]
  rw [hsum T hT, hsum T' hT']

end Formalism.MainNotions.G.ExtremalProjector
