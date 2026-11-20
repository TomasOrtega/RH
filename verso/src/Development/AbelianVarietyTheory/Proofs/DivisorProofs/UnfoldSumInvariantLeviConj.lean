import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK hL F hF k hk y`. Use `set c := s k with hc_def`. Establish `hc : c ∈ KP` using `hsK k hk`. Establish `hπu : ∀ X, π (u X) = 1` using `fun X => (hker _).2 ⟨X, rfl⟩`. Establish `hex : ∀ (d : P), ∀ X, ∃ Y, u Y = d * u X * d⁻¹`.

Introduce `d X`. Conclude with `(hker _).1 (by simp [map_mul, map_inv, hπu])`. Use `choose φ hφ using hex c`. Use `choose ψ hψ using hex c⁻¹`. Establish `h1 : ∀ X, φ (ψ X) = X` using `fun X => hu (by rw [hφ, hψ]; group)`.

Establish `h2 : ∀ X, ψ (φ X) = X` using `fun X => hu (by rw [hψ, hφ]; group)`. Establish `hconj : ∀ z, c * z * c⁻¹ ∈ KP ↔ z ∈ KP`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `KP.mul_mem (KP.mul_mem (KP.inv_mem hc) h) hc` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `h`. Conclude with `KP.mul_mem (KP.mul_mem hc h) (KP.inv_mem hc)`. Set `eN : N ≃ N` to `⟨φ, ψ, h2, h1⟩`.

Set `e : N ⧸ L ≃ N ⧸ L` to `Quotient.congr eN (by`. Introduce `a b`. Rewrite using `[QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hL, ← hL]`. Simplify using `only [eN, Equiv.coe_fn_mk, map_mul, map_inv, hφ]`. Rewrite using `[← hconj]`.

Apply the tactic sequence `constructor <;> intro h <;> convert h using 1 <;> group)`. Use `conv_rhs => rw [← finsum_comp_equiv e]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `x`. Use `set X := Quotient.out x with hX`.

Establish `hex' : e x = (QuotientGroup.mk (φ X) : N ⧸ L)` using `by conv_lhs => rw [← Quotient.out_eq x]`. Both sides reduce to the same expression. Use `set Z := Quotient.out (e x) with hZ`. Establish `hZL : Z⁻¹ * φ X ∈ L`. Apply `QuotientGroup.eq.mp` to reduce the goal to its premises.

Rewrite using `[← hex']`. Conclude with `Quotient.out_eq _`. Establish `hw : u (Z⁻¹ * φ X) ∈ KP` using `(hL _).2 hZL`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Rewrite using `[hφ]`. Use `group`. Use `_ = F ((u (φ X))⁻¹ * y * u (φ X)) := hF c hc _`. Use `_ = F ((u Z * u (Z⁻¹ * φ X))⁻¹ * y * (u Z * u (Z⁻¹ * φ X))) := by`. Rewrite using `[← map_mul, mul_inv_cancel_left]`.

Use `_ = F ((u (Z⁻¹ * φ X))⁻¹ * ((u Z)⁻¹ * y * u Z) * u (Z⁻¹ * φ X)) := by`. Use `congr 1`. Use `group`. Use `_ = F ((u Z)⁻¹ * y * u Z) := hF _ hw _`.
-/
theorem unfold_sum_conj_invariant : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK hL F hF k hk y
  set c := s k with hc_def
  have hc : c ∈ KP := hsK k hk
  have hπu : ∀ X, π (u X) = 1 := fun X => (hker _).2 ⟨X, rfl⟩
  have hex : ∀ (d : P), ∀ X, ∃ Y, u Y = d * u X * d⁻¹ := by
    intro d X
    exact (hker _).1 (by simp [map_mul, map_inv, hπu])
  choose φ hφ using hex c
  choose ψ hψ using hex c⁻¹
  have h1 : ∀ X, φ (ψ X) = X := fun X => hu (by rw [hφ, hψ]; group)
  have h2 : ∀ X, ψ (φ X) = X := fun X => hu (by rw [hψ, hφ]; group)
  have hconj : ∀ z, c * z * c⁻¹ ∈ KP ↔ z ∈ KP := by
    intro z
    constructor
    · intro h
      have := KP.mul_mem (KP.mul_mem (KP.inv_mem hc) h) hc
      simpa [mul_assoc] using this
    · intro h
      exact KP.mul_mem (KP.mul_mem hc h) (KP.inv_mem hc)
  let eN : N ≃ N := ⟨φ, ψ, h2, h1⟩
  let e : N ⧸ L ≃ N ⧸ L := Quotient.congr eN (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hL, ← hL]
    simp only [eN, Equiv.coe_fn_mk, map_mul, map_inv, hφ]
    rw [← hconj]
    constructor <;> intro h <;> convert h using 1 <;> group)
  conv_rhs => rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro x
  set X := Quotient.out x with hX
  have hex' : e x = (QuotientGroup.mk (φ X) : N ⧸ L) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  set Z := Quotient.out (e x) with hZ
  have hZL : Z⁻¹ * φ X ∈ L := by
    apply QuotientGroup.eq.mp
    rw [← hex']
    exact Quotient.out_eq _
  have hw : u (Z⁻¹ * φ X) ∈ KP := (hL _).2 hZL
  calc F ((u X)⁻¹ * (c⁻¹ * y * c) * u X) = F (c⁻¹ * ((u (φ X))⁻¹ * y * u (φ X)) * c) := by
        congr 1; rw [hφ]; group
    _ = F ((u (φ X))⁻¹ * y * u (φ X)) := hF c hc _
    _ = F ((u Z * u (Z⁻¹ * φ X))⁻¹ * y * (u Z * u (Z⁻¹ * φ X))) := by
        rw [← map_mul, mul_inv_cancel_left]
    _ = F ((u (Z⁻¹ * φ X))⁻¹ * ((u Z)⁻¹ * y * u Z) * u (Z⁻¹ * φ X)) := by
        congr 1; group
    _ = F ((u Z)⁻¹ * y * u Z) := hF _ hw _

end GlobalTheory
