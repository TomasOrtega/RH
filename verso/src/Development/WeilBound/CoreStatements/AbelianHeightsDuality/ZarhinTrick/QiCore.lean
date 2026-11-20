import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.CompLmulMapId
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIdem
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiStab
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCharP
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCartier

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

/- English proof (translation)
Introduce `K H _ _ _ _ _ Δ ε hL hR hmul hpts`. Take `⟨m, hm, hpt⟩` from `hpts`. Use `set I : Ideal H := RingHom.ker ε with hI`. Take `⟨k, e, he, hIk, hstab⟩` from `exists_stable_pow (K := K) I`. Establish `hk1 : I ^ (k + 1) = Ideal.span {e}` using `by rw [hstab (k + 1) (Nat.le_succ k), hIk]`.

Establish `heI : e ∈ I`. Establish `: e ∈ I ^ (k + 1)` using `by rw [hk1]; exact Ideal.subset_span rfl`. Conclude with `Ideal.pow_le_self (Nat.succ_ne_zero k) this`. Establish `hs : ∃ s : ℕ, 0 < s ∧ ∀ x ∈ I, pw Δ ε s x ∈ I ^ k`. Take `⟨p, hp⟩` from `CharP.exists K`.

Break down `CharP.char_is_prime_or_zero K p with hpp | hp0` into its components or cases. Establish `: Fact p.Prime` using `⟨hpp⟩`. Use `⟨p ^ k, pow_pos hpp.pos k, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le (pw_charP p Δ ε hL hR hmul k hx)`. Substitute `hp0` using the available equality.

Establish `: CharZero K` using `CharP.charP_to_charZero K`. Establish `h1 : pw Δ ε 1 = AlgHom.id K H` using `hL`. Establish `hle : ∀ j : ℕ, I ≤ I ^ (j + 1)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => rw [zero_add, pow_one]`. Consider the case `succ j ih`. Combine the equalities or inequalities in the displayed calculation. Use `⟨1, one_pos, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `Ideal.pow_le_pow_right (Nat.le_succ k) (hle k hx)`. Take `⟨s, hs0, hsI⟩` from `hs`. Establish `hme : pw Δ ε m e = 0`. Use `idem_eq_zero (K := K) (he.map (pw Δ ε m)) fun x => ?_` and prove the remaining obligations. Use `congrArg (fun f : H →ₐ[K] K => f e) (hpt x)` as an intermediate fact.

Simplify using `only [AlgHom.comp_apply] at this`. Rewrite using `[this]`. Conclude with `heI`. Use `⟨m * s, Nat.mul_pos hm hs0, AlgHom.ext fun x => ?_⟩` and prove the remaining obligations. Establish `hy : x - algebraMap K H (ε x) ∈ I`.

Express the relevant statement in the definitionally equal form `ε (x - algebraMap K H (ε x)) = 0`. Rewrite using `[map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 (hIk ▸ hsI _ hy)`. Establish `key : pw Δ ε (m * s) (x - algebraMap K H (ε x)) = 0`. Rewrite using `[hmul, AlgHom.comp_apply, ← ha, map_mul, hme, mul_zero]`.

Establish `h0 : pw Δ ε 0 (x - algebraMap K H (ε x)) = 0`. Express the relevant statement in the definitionally equal form `algebraMap K H (ε (x - algebraMap K H (ε x))) = 0`. Rewrite using `[show ε (x - algebraMap K H (ε x)) = 0 from hy, map_zero]`. Establish `e1` using `congrArg (· + algebraMap K H (ε x)) key`. Establish `e2` using `congrArg (· + algebraMap K H (ε x)) h0`.

Simplify using `only [map_sub, AlgHom.commutes, sub_add_cancel, zero_add] at e1 e2`. Rewrite using `[e1, e2]`.
-/
theorem killedCore : KilledCore := by
  intro K H _ _ _ _ _ Δ ε hL hR hmul hpts
  obtain ⟨m, hm, hpt⟩ := hpts
  set I : Ideal H := RingHom.ker ε with hI
  obtain ⟨k, e, he, hIk, hstab⟩ := exists_stable_pow (K := K) I

  have hk1 : I ^ (k + 1) = Ideal.span {e} := by rw [hstab (k + 1) (Nat.le_succ k), hIk]
  have heI : e ∈ I := by
    have : e ∈ I ^ (k + 1) := by rw [hk1]; exact Ideal.subset_span rfl
    exact Ideal.pow_le_self (Nat.succ_ne_zero k) this

  have hs : ∃ s : ℕ, 0 < s ∧ ∀ x ∈ I, pw Δ ε s x ∈ I ^ k := by
    obtain ⟨p, hp⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K p with hpp | hp0
    · have : Fact p.Prime := ⟨hpp⟩
      refine ⟨p ^ k, pow_pos hpp.pos k, fun x hx => ?_⟩
      exact Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le (pw_charP p Δ ε hL hR hmul k hx)
    · subst hp0
      have : CharZero K := CharP.charP_to_charZero K
      have h1 : pw Δ ε 1 = AlgHom.id K H := hL
      have hle : ∀ j : ℕ, I ≤ I ^ (j + 1) := by
        intro j
        induction j with
        | zero => rw [zero_add, pow_one]
        | succ j ih =>
          calc I ≤ I ^ 2 := aug_le_sq Δ ε hL hR
            _ = I * I := pow_two I
            _ ≤ I * I ^ (j + 1) := Ideal.mul_mono_right ih
            _ = I ^ (j + 1 + 1) := (pow_succ' I (j + 1)).symm
      refine ⟨1, one_pos, fun x hx => ?_⟩
      rw [h1]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (hle k hx)
  obtain ⟨s, hs0, hsI⟩ := hs

  have hme : pw Δ ε m e = 0 := by
    refine idem_eq_zero (K := K) (he.map (pw Δ ε m)) fun x => ?_
    have := congrArg (fun f : H →ₐ[K] K => f e) (hpt x)
    simp only [AlgHom.comp_apply] at this
    rw [this]
    exact heI
  refine ⟨m * s, Nat.mul_pos hm hs0, AlgHom.ext fun x => ?_⟩
  have hy : x - algebraMap K H (ε x) ∈ I := by
    change ε (x - algebraMap K H (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hIk ▸ hsI _ hy)
  have key : pw Δ ε (m * s) (x - algebraMap K H (ε x)) = 0 := by
    rw [hmul, AlgHom.comp_apply, ← ha, map_mul, hme, mul_zero]
  have h0 : pw Δ ε 0 (x - algebraMap K H (ε x)) = 0 := by
    change algebraMap K H (ε (x - algebraMap K H (ε x))) = 0
    rw [show ε (x - algebraMap K H (ε x)) = 0 from hy, map_zero]
  have e1 := congrArg (· + algebraMap K H (ε x)) key
  have e2 := congrArg (· + algebraMap K H (ε x)) h0
  simp only [map_sub, AlgHom.commutes, sub_add_cancel, zero_add] at e1 e2
  rw [e1, e2]

end PositivityTheory.PrwZar.Qi
