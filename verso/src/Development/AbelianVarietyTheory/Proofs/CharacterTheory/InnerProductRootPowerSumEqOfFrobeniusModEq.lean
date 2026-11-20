import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumEqTorusSumStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Establish `: Fintype F` using `Fintype.ofFinite F`. Use `⟨FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F) ^ i, fun α => ?_⟩` and prove the remaining obligations. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← pow_mul, Nat.card_eq_fintype_card, ← pow_succ]`.
-/
theorem exists_algEquiv_pow_card_pow (F : Type) [Field F] [Finite F] (i : ℕ) :
    ∃ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ α, σ α = α ^ (Nat.card F ^ i) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F) ^ i, fun α => ?_⟩
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← pow_mul,
      Nat.card_eq_fintype_card, ← pow_succ]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_algEquiv_pow_card_pow F i`. Rewrite using `[GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn k, GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn l]`. Use `set N := Nat.card F ^ Module.finrank F V - 1 with hN`. Establish `hmem : ∀ α : AlgebraicClosure F, α ^ N = 1 ↔ σ α ^ N = 1`. Introduce `α`.

Rewrite using `[← map_pow]`. Conclude with `⟨fun h => by rw [h, map_one], fun h => σ.injective (by rw [h, map_one])⟩`. Establish `hbij : Set.BijOn σ {α : AlgebraicClosure F | α ^ N = 1} {α : AlgebraicClosure F | α ^ N = 1}`. Use `⟨fun α hα => (hmem α).1 hα, σ.injective.injOn, fun β hβ => ⟨σ.symm β, ?_, σ.apply_symm_apply β⟩⟩` and prove the remaining obligations. Use `show (σ.symm β) ^ N = 1`.

Rewrite using `[hmem, σ.apply_symm_apply]`. Conclude with `hβ`. Use `(finsum_mem_eq_of_bijOn σ hbij fun α hα => ?_).symm` and prove the remaining obligations. Establish `hα' : α ^ N = 1` using `hα`. Establish `hm : minpoly F (σ α) = minpoly F α` using `minpoly.algEquiv_eq σ α`.

Establish `hθ : θ α ^ N = 1` using `by rw [← map_pow, hα', map_one]`. Establish `key : ∀ a : ℕ, θ α ^ a = θ α ^ (a % N)`. Introduce `a`. Use `conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hθ, one_pow, mul_one]`. Establish `hpow : θ α ^ (Nat.card F ^ i * k) = θ α ^ l`.

Rewrite using `[key, key l, mul_comm]`. Conclude with `congrArg _ h`. Rewrite using `[hm, hσ, map_pow, ← pow_mul, hpow]`.
-/
theorem ipGL_rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ) (hc : IsClassFn φ)
    (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V) (k l i : ℕ)
    (h : k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)]) :
    ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) =
      ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_algEquiv_pow_card_pow F i
  rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn k, GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn l]
  set N := Nat.card F ^ Module.finrank F V - 1 with hN
  have hmem : ∀ α : AlgebraicClosure F, α ^ N = 1 ↔ σ α ^ N = 1 := by
    intro α
    rw [← map_pow]
    exact ⟨fun h => by rw [h, map_one], fun h => σ.injective (by rw [h, map_one])⟩
  have hbij : Set.BijOn σ {α : AlgebraicClosure F | α ^ N = 1} {α : AlgebraicClosure F | α ^ N = 1} := by
    refine ⟨fun α hα => (hmem α).1 hα, σ.injective.injOn, fun β hβ => ⟨σ.symm β, ?_, σ.apply_symm_apply β⟩⟩
    show (σ.symm β) ^ N = 1
    rw [hmem, σ.apply_symm_apply]
    exact hβ
  refine (finsum_mem_eq_of_bijOn σ hbij fun α hα => ?_).symm
  have hα' : α ^ N = 1 := hα
  have hm : minpoly F (σ α) = minpoly F α := minpoly.algEquiv_eq σ α
  have hθ : θ α ^ N = 1 := by rw [← map_pow, hα', map_one]
  have key : ∀ a : ℕ, θ α ^ a = θ α ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hθ, one_pow, mul_one]
  have hpow : θ α ^ (Nat.card F ^ i * k) = θ α ^ l := by
    rw [key, key l, mul_comm]
    exact congrArg _ h
  rw [hm, hσ, map_pow, ← pow_mul, hpow]

end GlobalTheory.CuspGL
