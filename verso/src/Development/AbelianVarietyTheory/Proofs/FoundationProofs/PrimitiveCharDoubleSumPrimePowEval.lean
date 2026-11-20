import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

open GlobalTheory.KummerEisensteinGalois Finset

namespace GlobalTheory.KummerEisensteinGalois.ChSum

/- English proof (translation)
Establish `step : ∀ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') = ∑ s : ZMod M, ψ s * e (s * (w * D')) * e (a * (D + w * n₂ * D'))`. Introduce `a`. Set `f : ZMod M ≃ ZMod M` to `{ toFun := fun s => w * (s + n₂ * a) invFun := fun b => n₁ * b - n₂ * a left_inv := fun s => by simp only; linear_combination (s + n₂ * a) * hw right_inv := fun b => by simp only; linear_combination b * hw }`. Rewrite using `[← Equiv.sum_comp f]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Simplify using `only [f, Equiv.coe_fn_mk]`. Establish `h1 : n₁ * (w * (s + n₂ * a)) - n₂ * a = s` using `by linear_combination (s + n₂ * a) * hw`. Establish `h2 : a * D + w * (s + n₂ * a) * D' = s * (w * D') + a * (D + w * n₂ * D')` using `by ring`. Rewrite using `[h1, h2, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hG : ∑ s : ZMod M, ψ s * e (s * (w * D')) = ψ⁻¹ (w * D') * gaussSum ψ e`. Rewrite using `[← gaussSum_mulShift_of_isPrimitive e hψ]`. Unfold `gaussSum`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.mulShift_apply, mul_comm s]`.

Rewrite using `[Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum]`. Rewrite using `[AddChar.sum_mulShift _ he, ← Finset.sum_mul, hG, ZMod.card]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem core {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      (if D + w * n₂ * D' = 0 then (M : K) else 0) * (ψ⁻¹ (w * D') * gaussSum ψ e) := by
  have step : ∀ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      ∑ s : ZMod M, ψ s * e (s * (w * D')) * e (a * (D + w * n₂ * D')) := by
    intro a
    let f : ZMod M ≃ ZMod M :=
      { toFun := fun s => w * (s + n₂ * a)
        invFun := fun b => n₁ * b - n₂ * a
        left_inv := fun s => by simp only; linear_combination (s + n₂ * a) * hw
        right_inv := fun b => by simp only; linear_combination b * hw }
    rw [← Equiv.sum_comp f]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [f, Equiv.coe_fn_mk]
    have h1 : n₁ * (w * (s + n₂ * a)) - n₂ * a = s := by linear_combination (s + n₂ * a) * hw
    have h2 : a * D + w * (s + n₂ * a) * D' = s * (w * D') + a * (D + w * n₂ * D') := by ring
    rw [h1, h2, AddChar.map_add_eq_mul]; ring
  have hG : ∑ s : ZMod M, ψ s * e (s * (w * D')) = ψ⁻¹ (w * D') * gaussSum ψ e := by
    rw [← gaussSum_mulShift_of_isPrimitive e hψ]
    unfold gaussSum
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddChar.mulShift_apply, mul_comm s]
  rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [AddChar.sum_mulShift _ he, ← Finset.sum_mul, hG, ZMod.card]
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[core ψ hψ e he n₁ n₂ w D D' hw]`. Use `⟨fun u hD hD' => ?_, fun hno => ?_⟩` and prove the remaining obligations. Establish `h0 : D + w * n₂ * D' = 0` using `by rw [hD, hD']; linear_combination (u : ZMod M) * n₂ * hw`. Establish `hl : w * D' = u` using `by rw [hD']; linear_combination (u : ZMod M) * hw`. Rewrite using `[if_pos h0, hl]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hc : D + w * n₂ * D' = 0`. Establish `hnu : ¬ IsUnit (w * D')`. Introduce and unpack `⟨v, hv⟩`. Use `hno ⟨v, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hv]`. Take the linear combination `hc`. Rewrite using `[hv]`. Take the linear combination `(-D') * hw`. Rewrite using `[if_pos hc, MulChar.map_nonunit _ hnu]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hc, zero_mul]`.
-/
theorem eval {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    (∀ u : (ZMod M)ˣ, D = u * (-n₂) → D' = u * n₁ →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
        (M : K) * ψ⁻¹ (u : ZMod M) * gaussSum ψ e) ∧
    ((¬ ∃ u : (ZMod M)ˣ, D = u * (-n₂) ∧ D' = u * n₁) →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') = 0) := by
  rw [core ψ hψ e he n₁ n₂ w D D' hw]
  refine ⟨fun u hD hD' => ?_, fun hno => ?_⟩
  · have h0 : D + w * n₂ * D' = 0 := by rw [hD, hD']; linear_combination (u : ZMod M) * n₂ * hw
    have hl : w * D' = u := by rw [hD']; linear_combination (u : ZMod M) * hw
    rw [if_pos h0, hl]; ring
  · by_cases hc : D + w * n₂ * D' = 0
    · have hnu : ¬ IsUnit (w * D') := by
        rintro ⟨v, hv⟩
        refine hno ⟨v, ?_, ?_⟩
        · rw [hv]; linear_combination hc
        · rw [hv]; linear_combination (-D') * hw
      rw [if_pos hc, MulChar.map_nonunit _ hnu]; ring
    · rw [if_neg hc, zero_mul]

/- English proof (translation)
Establish `hne : ζ ≠ 0` using `hζ.ne_zero (NeZero.ne M)`. Rewrite using `[AddChar.zmodChar_apply, ← zpow_natCast, ZMod.val_intCast]`. Use `conv_lhs => rw [← Int.emod_add_mul_ediv z M]`. Rewrite using `[zpow_add₀ hne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]`.
-/
theorem zpow_eq {M : ℕ} [NeZero M] {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) (z : ℤ) :
    ζ ^ z = AddChar.zmodChar M hζ.pow_eq_one (z : ZMod M) := by
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
  rw [AddChar.zmodChar_apply, ← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv z M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]

/- English proof (translation)
Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hc : IsCoprime n ((p : ℤ) ^ m)` using `(((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h).pow_left).symm`. Take `⟨u, v, huv⟩` from `hc`. Use `⟨(u : ZMod (p ^ m)), ?_⟩` and prove the remaining obligations. Use `congrArg (fun z : ℤ => (z : ZMod (p ^ m))) huv` as an intermediate fact.

Simplify using `only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at this`. Rewrite `this` using `[← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero]`. Rewrite using `[mul_comm]`. Conclude with `this`.
-/
theorem unit_of_not_dvd (p m : ℕ) (hp : p.Prime) (n : ℤ) (h : ¬ (p : ℤ) ∣ n) :
    ∃ w : ZMod (p ^ m), (n : ZMod (p ^ m)) * w = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc : IsCoprime n ((p : ℤ) ^ m) :=
    (((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h).pow_left).symm
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨(u : ZMod (p ^ m)), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod (p ^ m))) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at this
  rw [← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact this

/- English proof (translation)
Introduce `p m _ K _ _ ψ ζm _ hψ hζ n₁ n₂ d d' hn`. Establish `hp : p.Prime` using `Fact.out`. Establish `he` using `AddChar.zmodChar_primitive_of_primitive_root (p ^ m) hζ`. Use `set e := AddChar.zmodChar (p ^ m) hζ.pow_eq_one with he_def`. Establish `hG : gaussS p m ψ ζm = gaussSum ψ e` using `rfl`.

Establish `hz : ∀ a b : ZMod (p ^ m), ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m)))`. Introduce `a b`. Rewrite using `[zpow_eq hζ]`. Use `congr 1`. Simplify using `only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]`.

Simplify using `only [hz, hG]`. Rewrite using `[← Nat.cast_pow]`. Distinguish the cases in `h1 : (p : ℤ) ∣ n₁`. Establish `h2 : ¬ (p : ℤ) ∣ n₂` using `fun h => hn ⟨h1, h⟩`. Take `⟨w, hw⟩` from `unit_of_not_dvd p m hp n₂ h2`.

Establish `hw' : (-(n₂ : ZMod (p ^ m))) * (-w) = 1` using `by rw [neg_mul_neg, hw]`. Establish `key` using `eval ψ hψ e he (-(n₂ : ZMod (p ^ m))) (-(n₁ : ZMod (p ^ m))) (-w) (d' : ZMod (p ^ m)) (d : ZMod (p ^ m)) hw'`. Establish `hswap : ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) = ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ (-(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a) * e (a * (d' : ZMod (p ^ …`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[show -(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a = (n₁ : ZMod (p ^ m)) * a - (n₂ : ZMod (p ^ m)) * b by ring, add_comm (a * (d' : ZMod (p ^ m)))]`. Rewrite using `[hswap]`. Rewrite `key` using `[neg_neg]`. Conclude with `⟨fun u hd hd' => key.1 u hd' hd, fun hno => key.2 fun ⟨u, hd', hd⟩ => hno ⟨u, hd, hd'⟩⟩`. Take `⟨w, hw⟩` from `unit_of_not_dvd p m hp n₁ h1`.

Conclude with `eval ψ hψ e he _ _ w _ _ hw`.
-/
theorem charSum : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  intro p m _ K _ _ ψ ζm _ hψ hζ n₁ n₂ d d' hn
  have hp : p.Prime := Fact.out
  have he := AddChar.zmodChar_primitive_of_primitive_root (p ^ m) hζ
  set e := AddChar.zmodChar (p ^ m) hζ.pow_eq_one with he_def
  have hG : gaussS p m ψ ζm = gaussSum ψ e := rfl
  have hz : ∀ a b : ZMod (p ^ m), ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') =
      e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) := by
    intro a b
    rw [zpow_eq hζ]
    congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [hz, hG]
  rw [← Nat.cast_pow]
  by_cases h1 : (p : ℤ) ∣ n₁
  · have h2 : ¬ (p : ℤ) ∣ n₂ := fun h => hn ⟨h1, h⟩
    obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₂ h2
    have hw' : (-(n₂ : ZMod (p ^ m))) * (-w) = 1 := by rw [neg_mul_neg, hw]
    have key := eval ψ hψ e he (-(n₂ : ZMod (p ^ m))) (-(n₁ : ZMod (p ^ m))) (-w)
      (d' : ZMod (p ^ m)) (d : ZMod (p ^ m)) hw'
    have hswap : ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
          e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) =
        ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ (-(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a) *
          e (a * (d' : ZMod (p ^ m)) + b * (d : ZMod (p ^ m))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show -(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a =
        (n₁ : ZMod (p ^ m)) * a - (n₂ : ZMod (p ^ m)) * b by ring, add_comm (a * (d' : ZMod (p ^ m)))]
    rw [hswap]
    rw [neg_neg] at key
    exact ⟨fun u hd hd' => key.1 u hd' hd,
      fun hno => key.2 fun ⟨u, hd', hd⟩ => hno ⟨u, hd, hd'⟩⟩
  · obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₁ h1
    exact eval ψ hψ e he _ _ w _ _ hw

end GlobalTheory.KummerEisensteinGalois.ChSum
