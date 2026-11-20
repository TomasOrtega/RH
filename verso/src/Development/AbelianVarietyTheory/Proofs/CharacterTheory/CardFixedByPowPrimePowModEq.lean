import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `: Fintype X` using `Fintype.ofFinite X`. Set `f : Function.End (MulAction.fixedBy X (x ^ p ^ k))` to `fun y => ⟨x • (y : X), by`. Establish `hy : (x ^ p ^ k) • (y : X) = y` using `y.2`. Use `show (x ^ p ^ k) • x • (y : X) = x • (y : X)`.

Rewrite using `[← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩`. Establish `hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`.

Rewrite using `[pow_zero, pow_zero, one_smul]`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `y`. Rewrite using `[pow_succ', pow_succ', mul_smul, ← ih y]`.

Both sides reduce to the same expression. Establish `h1 : f ^ p ^ k = 1`. Use function extensionality and compare the values at `y`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hf]`.

Conclude with `y.2`. Establish `h2` using `Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1`. Establish `e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x` using `{ toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩ invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by`. Rewrite using `[zpow_natCast] at h⟩, Subtype.ext y.2⟩` and apply the resulting hypothesis. Use `left_inv := fun _ => rfl`.

Use `right_inv := fun _ => rfl }`. Rewrite using `[← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`. Use `h2` and compare the differences between its conclusion and the goal.
-/
theorem card_fixedBy_pow_prime_pow_modEq (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End (MulAction.fixedBy X (x ^ p ^ k)) := fun y => ⟨x • (y : X), by
    have hy : (x ^ p ^ k) • (y : X) = y := y.2
    show (x ^ p ^ k) • x • (y : X) = x • (y : X)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩
  have hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X) := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_smul, ← ih y]
      rfl
  have h1 : f ^ p ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hf]
    exact y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1
  have e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x :=
    { toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩
      invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by
          rwa [zpow_natCast] at h⟩, Subtype.ext y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2

end GlobalTheory
