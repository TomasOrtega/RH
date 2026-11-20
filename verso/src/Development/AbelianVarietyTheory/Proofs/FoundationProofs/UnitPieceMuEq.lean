import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DropConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharacterEntrySumEisensteinProductStatement

open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Unfold `pieceTRaw cmul`. Use `congr 1`. Simplify using `only [mul_sum]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `h` using `drop_const p m N k hm hpN hk ψ hψ ζ x y 0 0 i (r - i)`. Simplify using `only [mul_zero, add_zero] at h`. Rewrite using `[← h]`. Establish `e` using `sum_unitSet p m ψ (fun u a v b => eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i * eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i))`. Rewrite using `[← e]`.

Use `sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Simplify using `[rowT]`.
-/
theorem pieceTRaw_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y : ℤ) (r : ℕ) :
    pieceTRaw N p m m k ψ (x, 0) (y, 0) ζ (unitSet p m) r = -((p : K) ^ ((m : ℤ) * ((k : ℤ) - 4))) *
      ∑ i ∈ range (r + 1),
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i)) := by
  unfold pieceTRaw cmul
  congr 1
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h := drop_const p m N k hm hpN hk ψ hψ ζ x y 0 0 i (r - i)
  simp only [mul_zero, add_zero] at h
  rw [← h]
  have e := sum_unitSet p m ψ (fun u a v b =>
    eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i))
  rw [← e]
  refine sum_congr rfl fun γ _ => ?_
  simp [rowT]

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hpK : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hNK : (N : K) ≠ 0` using `by exact_mod_cast hN.ne'`. Rewrite using `[pieceTRaw_eq p m N k hm hpN hk ψ hψ ζ]`. Rewrite using `[sum_congr rfl fun i hi => by`.

Rewrite using `[GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product p m N k K hm hN hpN hk ψ hψ ζ hζ a₀ b₀ t ht, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]]`. Use `split_ifs with h`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 2` from `⟨k - 2, by omega⟩`. Establish `e' : (p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m * ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹ = (p : K) ^ (-(m : ℤ)) * (N : K) ^ ((2 : ℤ) - ((k' + 2 : ℕ) : ℤ))`. Rewrite using `[Nat.add_sub_cancel, zpow_mul]`.

Use `push_cast`. Rewrite using `[show ((k' : ℤ) + 2 - 4) = (k' : ℤ) - 2 by ring, show (2 : ℤ) - (k' + 2) = -(k' : ℤ) by ring, zpow_sub₀ (zpow_ne_zero _ hpK), zpow_neg, zpow_neg]`. Simplify using `only [zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Unfold `coPtMu cmul`. Rewrite using `[mul_sum, mul_sum]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using the standard rewrite rules.
-/
theorem coef_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (r : ℕ) :
    pieceTRaw N p m m k ψ (a₀ * t, 0) (b₀ * t, 0) ζ (unitSet p m) r =
      if p ^ m ∣ r then -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
        (N : K) ^ ((2 : ℤ) - k) * coPtMu N p m k ψ a₀ b₀ r else 0 := by
  have hp : p.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [pieceTRaw_eq p m N k hm hpN hk ψ hψ ζ]
  rw [sum_congr rfl fun i hi => by
    rw [GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product p m N k K hm hN hpN hk ψ hψ ζ hζ a₀ b₀ t ht,
      Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]]
  split_ifs with h
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have e' : (p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹ = (p : K) ^ (-(m : ℤ)) * (N : K) ^ ((2 : ℤ) - ((k' + 2 : ℕ) : ℤ)) := by
      rw [Nat.add_sub_cancel, zpow_mul]
      push_cast
      rw [show ((k' : ℤ) + 2 - 4) = (k' : ℤ) - 2 by ring, show (2 : ℤ) - (k' + 2) = -(k' : ℤ) by ring,
        zpow_sub₀ (zpow_ne_zero _ hpK), zpow_neg, zpow_neg]
      simp only [zpow_natCast]
      field_simp
      ring
    unfold coPtMu cmul
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    calc _ = -((p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
          (ffMu N p m (k' + 2) ψ a₀ i * eeMu N p m ψ b₀ (r - i)) := by ring
      _ = _ := by rw [e']; ring
  · simp

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu

/- English proof (translation)
Introduce `p _ N m k K _ _ ψ a b t ζ _ hζ hN hpN hm hk hψ ht`. Use `⟨fun r hr => ?_, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_neg hr]`. Unfold `toQ up`. Rewrite using `[GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_pos (dvd_mul_right _ _)]`.
-/
theorem GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (a b t : ℤ) (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N → 1 ≤ m → 3 ≤ k → ψ.IsPrimitive → (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → Integral (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) ∧ ∀ r : ℕ, toQ (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) r = -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (N : K) ^ ((2 : ℤ) - k) * up (p ^ m) (coPtMu N p m k ψ a b) r := by
  intro p _ N m k K _ _ ψ a b t ζ _ hζ hN hpN hm hk hψ ht
  refine ⟨fun r hr => ?_, fun r => ?_⟩
  · rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_neg hr]
  · unfold toQ up
    rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_pos (dvd_mul_right _ _)]
