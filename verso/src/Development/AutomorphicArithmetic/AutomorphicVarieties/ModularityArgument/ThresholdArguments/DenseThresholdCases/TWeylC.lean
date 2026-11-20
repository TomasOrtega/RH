import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WeylC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh
/- English proof (translation)
Introduce `_ E _ _ _ n`. Use `⟨((n + 1) ^ 2) ^ (n * n * Fintype.card (E →+* ℂ)), n * n * Fintype.card (E →+* ℂ), fun m hm H hH => ?_⟩` and prove the remaining obligations. Establish `hb` using `fun i => abs_le.1 (hH i)`. Set `ν : Fin n → ℕ` to `fun k => ((k : ℕ) + 1 + H - m k.rev : ℤ).toNat`. Establish `hν : ∀ k, (ν k : ℤ) = (k : ℕ) + 1 + H - m k.rev` using `fun k => Int.toNat_of_nonneg (by have := hb k.rev; omega)`.

Establish `hanti : Antitone ν`. Consider the cases of `n with`. Consider the case `zero => exact fun i => i.elim0`. Consider the case `succ n`. Use `Fin.antitone_iff_succ_le.2 fun i => ?_` and prove the remaining obligations.

Establish `h1` using `hν i.succ`. Establish `h2` using `hν i.castSucc`. Establish `h3 : m i.castSucc.rev < m i.succ.rev` using `hm (Fin.rev_lt_rev.2 Fin.castSucc_lt_succ)`. Simplify using `only [Fin.val_succ, Fin.val_castSucc] at h1 h2`. Use linear arithmetic over natural numbers and integers.

Establish `hle : ∀ k, ν k ≤ n + 2 * H` using `fun k => by`. Establish `h1` using `hν k`. Establish `h2` using `hb k.rev`. Establish `h3` using `k.2`. Use linear arithmetic over natural numbers and integers.

Take `⟨P, hP, hd, hw⟩` from `UpperTheory.V.Weyl.existsScalar n ν hanti _ hle`. Take `⟨Ξ, h1, h2⟩` from `UpperTheory.V.WeylC.exists_tens (E := E) P hP _ hw (n + H)`. Use `⟨Ξ, fun τ => (UpperTheory.V.WeylC.algInfChar_iff _ _ _).2 ⟨by simp [UpperTheory.V.Af.infOf], fun u => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, UpperTheory.V.Af.infOf, Multiset.map_map, Multiset.map_map]`. Use `congr 1`.

Use `(Fintype.prod_equiv Fin.revPerm _ _ fun k => ?_)` and prove the remaining obligations. Establish `h3 : ((ν k : ℕ) : ℂ) = (k : ℕ) + 1 + H - m k.rev` using `by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (hν k)`. Simplify using `only [Function.comp_apply, Fin.revPerm_apply, h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `h1.trans ((Nat.pow_le_pow_left hd _).trans ?_)` and prove the remaining obligations. Rewrite using `[← pow_mul, ← mul_pow]`. Conclude with `Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (n * n * H), Nat.zero_le H, Nat.zero_le n]) _`.
-/
theorem UpperTheory.V.Af.weyl_complex_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WeylC := by
  intro _ E _ _ _ n
  refine ⟨((n + 1) ^ 2) ^ (n * n * Fintype.card (E →+* ℂ)), n * n * Fintype.card (E →+* ℂ), fun m hm H hH => ?_⟩
  have hb := fun i => abs_le.1 (hH i)
  let ν : Fin n → ℕ := fun k => ((k : ℕ) + 1 + H - m k.rev : ℤ).toNat
  have hν : ∀ k, (ν k : ℤ) = (k : ℕ) + 1 + H - m k.rev := fun k => Int.toNat_of_nonneg (by have := hb k.rev; omega)
  have hanti : Antitone ν := by
    cases n with
    | zero => exact fun i => i.elim0
    | succ n =>
      refine Fin.antitone_iff_succ_le.2 fun i => ?_
      have h1 := hν i.succ
      have h2 := hν i.castSucc
      have h3 : m i.castSucc.rev < m i.succ.rev := hm (Fin.rev_lt_rev.2 Fin.castSucc_lt_succ)
      simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
  have hle : ∀ k, ν k ≤ n + 2 * H := fun k => by
    have h1 := hν k
    have h2 := hb k.rev
    have h3 := k.2
    omega
  obtain ⟨P, hP, hd, hw⟩ := UpperTheory.V.Weyl.existsScalar n ν hanti _ hle
  obtain ⟨Ξ, h1, h2⟩ := UpperTheory.V.WeylC.exists_tens (E := E) P hP _ hw (n + H)
  refine ⟨Ξ, fun τ => (UpperTheory.V.WeylC.algInfChar_iff _ _ _).2 ⟨by simp [UpperTheory.V.Af.infOf], fun u => ?_⟩, ?_⟩
  · rw [h2, UpperTheory.V.Af.infOf, Multiset.map_map, Multiset.map_map]
    congr 1
    refine (Fintype.prod_equiv Fin.revPerm _ _ fun k => ?_)
    have h3 : ((ν k : ℕ) : ℂ) = (k : ℕ) + 1 + H - m k.rev := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (hν k)
    simp only [Function.comp_apply, Fin.revPerm_apply, h3]
    push_cast
    ring
  · refine h1.trans ((Nat.pow_le_pow_left hd _).trans ?_)
    rw [← pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (n * n * H), Nat.zero_le H, Nat.zero_le n]) _
end
