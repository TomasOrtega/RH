import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP

open IsLocalRing GlobalTheory.UT

namespace GlobalTheory.Poinc

/- English proof (translation)
Introduce `R _ _ _ Ix x s s' ⟨N, _, _, _, h⟩ ⟨N', _, _, _, h'⟩`. Establish `key : ∀ n : ℕ, s - s' ∈ maximalIdeal R ^ n`. Introduce `n`. Take `⟨S, hS⟩` from `h n`. Take `⟨S', hS'⟩` from `h' n`.

Establish `le : ∀ M : Submodule R R, maximalIdeal R ^ n • M ≤ maximalIdeal R ^ n` using `fun M => Submodule.smul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha`. Establish `h1` using `le _ (hS (S ∪ S') Finset.subset_union_left)`. Establish `h2` using `le _ (hS' (S ∪ S') Finset.subset_union_right)`. Establish `h3` using `Ideal.sub_mem _ h1 h2`. Rewrite `h3` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.

Establish `hb : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥` using `Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top`. Establish `: s - s' ∈ ⨅ n : ℕ, maximalIdeal R ^ n` using `Ideal.mem_iInf.2 key`. Rewrite `this` using `[hb, Ideal.mem_bot]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem sumI_maximalIdeal_unique :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (Ix : Type) (x : Ix → R) (s s' : R),
      SumI (maximalIdeal R) x s → SumI (maximalIdeal R) x s' → s = s' := by
  classical
  intro R _ _ _ Ix x s s' ⟨N, _, _, _, h⟩ ⟨N', _, _, _, h'⟩
  have key : ∀ n : ℕ, s - s' ∈ maximalIdeal R ^ n := by
    intro n
    obtain ⟨S, hS⟩ := h n
    obtain ⟨S', hS'⟩ := h' n
    have le : ∀ M : Submodule R R, maximalIdeal R ^ n • M ≤ maximalIdeal R ^ n := fun M =>
      Submodule.smul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
    have h1 := le _ (hS (S ∪ S') Finset.subset_union_left)
    have h2 := le _ (hS' (S ∪ S') Finset.subset_union_right)
    have h3 := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_right] at h3
  have hb : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have : s - s' ∈ ⨅ n : ℕ, maximalIdeal R ^ n := Ideal.mem_iInf.2 key
  rw [hb, Ideal.mem_bot] at this
  exact sub_eq_zero.1 this

end GlobalTheory.Poinc
