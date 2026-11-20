import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Use `conv_rhs => rw [← Nat.mod_add_div v m]`. Use `push_cast`. Establish `: 2 * Real.pi * Complex.I * ((v % m : ℕ) + (m : ℂ) * (v / m : ℕ)) / (m : ℂ) = 2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ) + ((v / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]`.
-/
theorem exp_val_mod (m v : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (m : ℂ)) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  conv_rhs => rw [← Nat.mod_add_div v m]
  push_cast
  have : 2 * Real.pi * Complex.I * ((v % m : ℕ) + (m : ℂ) * (v / m : ℕ)) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ) + ((v / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/- English proof (translation)
Take `⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hrel⟩` from `h`. Use `set k := (PadicInt.toZModPow n c).val with hk`. Use `⟨f ^ k, fun z => a z ^ k, fun z => b z ^ k, M, hM, ?_, ⟨ha.pow k, hb.pow k, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hx, ((GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.2.2.2.1 c f)]`. Introduce `h0`.

Apply `hb0` to reduce the goal to its premises. Establish `e1` using `((GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties).1 (fun z => b z ^ k) (fun _ => 0) (hb.pow k) (differentiableOn_const 0)).1 h0`. Establish `e2 : ∀ z ∈ Hs, b z = 0` using `fun z hz => (pow_eq_zero_iff' (M₀ := ℂ)).1 (e1 z hz) |>.1`. Conclude with `((GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties).1 b (fun _ => 0) hb (differentiableOn_const 0)).2 e2`. Establish `e : ∀ (g : ℂ → ℂ), ((fun z => g z ^ k : ℂ → ℂ) : Mero) = (g : Mero) ^ k` using `fun g => rfl`.

Rewrite using `[e, e, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, mul_comm k, pow_mul, ← mul_pow, hr, ← pow_mul, ← pow_mul, mul_comm k]`. Introduce `δ hδ z hz`. Establish `hl : 0 < l ^ n` using `pow_pos (Fact.out : l.Prime).pos n`. Use `haveI : NeZero (l ^ n) := ⟨hl.ne'⟩`. Simplify using `only`.

Rewrite using `[← mul_pow, hrel δ hδ z hz, mul_pow, mul_pow, ZMod.val_mul]`. Use `push_cast`. Establish `em` using `exp_val_mod (l ^ n) (k * (χ δ).val) hl`. Move the coercions through the operations in `at em`. Rewrite using `[em, ← Complex.exp_nat_mul]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kum_smul (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) (h : Kum X l n x χ) :
    Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hrel⟩ := h
  set k := (PadicInt.toZModPow n c).val with hk
  refine ⟨f ^ k, fun z => a z ^ k, fun z => b z ^ k, M, hM, ?_, ⟨ha.pow k, hb.pow k, ?_, ?_⟩, ?_⟩
  · rw [map_smul, hx, ((GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.2.2.2.1 c f)]
  · intro h0
    apply hb0
    have e1 := ((GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties).1 (fun z => b z ^ k) (fun _ => 0) (hb.pow k) (differentiableOn_const 0)).1 h0
    have e2 : ∀ z ∈ Hs, b z = 0 := fun z hz => (pow_eq_zero_iff' (M₀ := ℂ)).1 (e1 z hz) |>.1
    exact ((GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties).1 b (fun _ => 0) hb (differentiableOn_const 0)).2 e2
  · have e : ∀ (g : ℂ → ℂ), ((fun z => g z ^ k : ℂ → ℂ) : Mero) = (g : Mero) ^ k := fun g => rfl
    rw [e, e, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, mul_comm k, pow_mul, ← mul_pow, hr, ← pow_mul, ← pow_mul,
      mul_comm k]
  · intro δ hδ z hz
    have hl : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    haveI : NeZero (l ^ n) := ⟨hl.ne'⟩
    simp only
    rw [← mul_pow, hrel δ hδ z hz, mul_pow, mul_pow, ZMod.val_mul]
    push_cast
    have em := exp_val_mod (l ^ n) (k * (χ δ).val) hl
    push_cast at em
    rw [em, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

end GlobalTheory.KZ.H3
