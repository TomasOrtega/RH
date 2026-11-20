import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetOrth

def twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) : Representation ℂ H V where
  toFun x := ((η x : ℂ) ^ a) • ρ x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, Units.val_mul, mul_pow, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm]

/- English proof (translation)
Use `show LinearMap.trace ℂ V (((η x : ℂ) ^ a) • ρ x) = _`. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`.
-/
theorem trace_twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) (x : H) :
    LinearMap.trace ℂ V (twist η a ρ x) = LinearMap.trace ℂ V (ρ x) * (η x : ℂ) ^ a := by
  show LinearMap.trace ℂ V (((η x : ℂ) ^ a) • ρ x) = _
  rw [map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Establish `hne : (Nat.card H : ℂ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Use `haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hne`. Establish `h` using `FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of σ) (FDRep.of ρ)`. Use `⟨Module.finrank ℂ (FDRep.of σ ⟶ FDRep.of ρ), ?_⟩` and prove the remaining obligations. Rewrite using `[← h, mul_inv_cancel_left₀ hne]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.BadShare.ZCalc.character_inv]`. Both sides reduce to the same expression.
-/
theorem sum_trace_mul_star_nat {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    ∃ k : ℕ, ∑ x, LinearMap.trace ℂ V (ρ x) * star (LinearMap.trace ℂ W (σ x)) = (Nat.card H : ℂ) * k := by
  have hne : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hne
  have h := FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of σ) (FDRep.of ρ)
  refine ⟨Module.finrank ℂ (FDRep.of σ ⟶ FDRep.of ρ), ?_⟩
  rw [← h, mul_inv_cancel_left₀ hne]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.BadShare.ZCalc.character_inv]
  rfl

end GlobalTheory.Shin.CosetOrth

open GlobalTheory.Shin.CosetOrth in
/- English proof (translation)
Introduce `G Γ _ _ _ _ φ s hp hs X Y hX hY h0`. Use `haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩`. Establish `gen : ∀ t : Γ, t ∈ Subgroup.zpowers s`. Introduce `t`. Rewrite using `[zpowers_eq_top_of_prime_card rfl hs]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hl0 : Nat.card Γ ≠ 0` using `hp.ne_zero`. Take `⟨η, -, -, hF⟩` from `GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s gen _ (Complex.isPrimitiveRoot_exp _ hl0)`. Take `⟨e1, e2⟩` from `hF X Y`. Use `haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm`.

Use `letI : Fintype (G ⋊[φ] Γ) := Fintype.ofFinite _`. Establish `hm : ∀ a : ℕ, ∃ k : ℕ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card (G ⋊[φ] Γ) : ℂ) * k`. Introduce `a`. Take `⟨n, ρ, hρ⟩` from `hX`. Take `⟨m, σ, hσ⟩` from `hY`.

Take `⟨k, hk⟩` from `sum_trace_mul_star_nat ρ (twist η a σ)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_fintype, ← hk]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[trace_twist, hρ x, hσ x]`.

Both sides reduce to the same expression. Use `choose k hk using hm`. Establish `hH : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Establish `hsum : ∑ a ∈ Finset.range (Nat.card Γ), k a = 0`. Rewrite `e1` using `[h0, mul_zero]`.

Rewrite `e1` using `[hk]`. Rewrite `e1` using `[← Finset.mul_sum]`. Use `(mul_eq_zero.mp e1.symm).resolve_left hH` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hk0 : ∀ a ∈ Finset.range (Nat.card Γ), k a = 0` using `Finset.sum_eq_zero_iff.mp hsum`.

Establish `hR : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = 0`. Use `Finset.sum_eq_zero fun a ha => ?_` and prove the remaining obligations. Rewrite using `[hk a, hk0 a ha]`. Simplify using the standard rewrite rules. Rewrite `e2` using `[hR]`.

Conclude with `(mul_eq_zero.mp e2).resolve_left (by exact_mod_cast hl0)`.
-/
theorem GlobalTheory.Shin.finsum_coset_mul_star_eq_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  intro G Γ _ _ _ _ φ s hp hs X Y hX hY h0
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have gen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hl0 : Nat.card Γ ≠ 0 := hp.ne_zero
  obtain ⟨η, -, -, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s gen _ (Complex.isPrimitiveRoot_exp _ hl0)
  obtain ⟨e1, e2⟩ := hF X Y
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  letI : Fintype (G ⋊[φ] Γ) := Fintype.ofFinite _
  have hm : ∀ a : ℕ, ∃ k : ℕ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card (G ⋊[φ] Γ) : ℂ) * k := by
    intro a
    obtain ⟨n, ρ, hρ⟩ := hX
    obtain ⟨m, σ, hσ⟩ := hY
    obtain ⟨k, hk⟩ := sum_trace_mul_star_nat ρ (twist η a σ)
    refine ⟨k, ?_⟩
    rw [finsum_eq_sum_of_fintype, ← hk]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [trace_twist, hρ x, hσ x]
    rfl
  choose k hk using hm
  have hH : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum : ∑ a ∈ Finset.range (Nat.card Γ), k a = 0 := by
    rw [h0, mul_zero] at e1
    simp_rw [hk] at e1
    rw [← Finset.mul_sum] at e1
    have := (mul_eq_zero.mp e1.symm).resolve_left hH
    exact_mod_cast this
  have hk0 : ∀ a ∈ Finset.range (Nat.card Γ), k a = 0 := Finset.sum_eq_zero_iff.mp hsum
  have hR : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hk a, hk0 a ha]; simp
  rw [hR] at e2
  exact (mul_eq_zero.mp e2).resolve_left (by exact_mod_cast hl0)
