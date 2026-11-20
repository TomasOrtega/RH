import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecond

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.PairCount

/- English proof (translation)
Introduce `C _ V d _ I J _ _ X g a' hs U' hU N ψ _ hp hind hk`. Take `⟨s, hsi, hs1⟩` from `X.pair_onto g`. Establish `h` using `GlobalTheory.RowKernel.card_add_le (V := V) (fun k : I (1 - g) => (X.G (1 - g)).ty (Sum.inl k) = a') (fun ν k => ∑ κ, ψ ν κ * X.pair g κ k) U' ?_ ?_ hU.1 (fun μ k hk => hU.2 μ k hk) ?_`. Establish `h2` using `X.rk_big (1 - g) a' ((X.big_compl g a').2 hs)`. Establish `h3 : N + X.n ≤ X.n + X.j`.

Rewrite using `[← h2]`. Use `h` and compare the differences between its conclusion and the goal. Use linear arithmetic over natural numbers and integers. Introduce `c hc hm`. Use `hind c hc fun κ' => ?_` and prove the remaining obligations.

Establish `e : ∑ ν, c ν * ψ ν κ' = ∑ k, (∑ ν, c ν * ∑ κ, ψ ν κ * X.pair g κ k) * s k κ'`. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Establish `e1 : ψ ν κ' = ∑ κ, ψ ν κ * ∑ k, X.pair g κ k * s k κ'`.

Simplify using `[hs1]`. Rewrite using `[e1]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun κ _ => by ring`.

Rewrite using `[e]`. Conclude with `GlobalTheory.RowKernel.mm_sum fun k _ => GlobalTheory.RowKernel.mm_mul_int (hm k) (hsi k κ')`. Introduce `ν k hk'`. Use `Finset.sum_eq_zero fun κ _ => ?_` and prove the remaining obligations. Distinguish the cases in `hκ : (X.G g).ty (Sum.inr κ) = a'`.

Rewrite using `[X.pair_type g κ k (fun h => hk' (h ▸ hκ)), mul_zero]`. Rewrite using `[hp ν κ hκ, zero_mul]`. Introduce `ν μ`. Establish `h` using `hk ν μ`. Rewrite `h` using `[Finset.sum_comm]`.

Simplify `h` using `only [Finset.sum_mul]`.
-/
theorem pair_kernel_le : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a' : ZMod d), ¬ X.big g a' → ∀ U' : Fin X.n → I (1 - g) → C, X.SatIn (1 - g) a' U' → ∀ (N : ℕ) (ψ : Fin N → J g → C), (∀ ν κ, V.Ge 0 (ψ ν κ)) → (∀ ν κ, (X.G g).ty (Sum.inr κ) ≠ a' → ψ ν κ = 0) → IndepMod V ψ → (∀ ν b, V.MM (∑ κ : J g, ∑ k : I (1 - g), ψ ν κ * X.pair g κ k * U' b k)) → N ≤ X.j := by
  intro C _ V d _ I J _ _ X g a' hs U' hU N ψ _ hp hind hk
  obtain ⟨s, hsi, hs1⟩ := X.pair_onto g
  have h := GlobalTheory.RowKernel.card_add_le (V := V) (fun k : I (1 - g) => (X.G (1 - g)).ty (Sum.inl k) = a')
    (fun ν k => ∑ κ, ψ ν κ * X.pair g κ k) U' ?_ ?_ hU.1 (fun μ k hk => hU.2 μ k hk) ?_
  · have h2 := X.rk_big (1 - g) a' ((X.big_compl g a').2 hs)
    have h3 : N + X.n ≤ X.n + X.j := by
      rw [← h2]
      convert h
    omega
  · intro c hc hm
    refine hind c hc fun κ' => ?_
    have e : ∑ ν, c ν * ψ ν κ' = ∑ k, (∑ ν, c ν * ∑ κ, ψ ν κ * X.pair g κ k) * s k κ' := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have e1 : ψ ν κ' = ∑ κ, ψ ν κ * ∑ k, X.pair g κ k * s k κ' := by
        simp [hs1]
      rw [e1]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun κ _ => by ring
    rw [e]
    exact GlobalTheory.RowKernel.mm_sum fun k _ => GlobalTheory.RowKernel.mm_mul_int (hm k) (hsi k κ')
  · intro ν k hk'
    refine Finset.sum_eq_zero fun κ _ => ?_
    by_cases hκ : (X.G g).ty (Sum.inr κ) = a'
    · rw [X.pair_type g κ k (fun h => hk' (h ▸ hκ)), mul_zero]
    · rw [hp ν κ hκ, zero_mul]
  · intro ν μ
    have h := hk ν μ
    rw [Finset.sum_comm] at h
    simpa only [Finset.sum_mul] using h

end GlobalTheory.PairCount
