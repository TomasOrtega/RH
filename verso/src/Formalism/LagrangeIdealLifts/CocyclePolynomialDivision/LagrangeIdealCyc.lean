import Formalism.LagrangeIdealLifts.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.LIFT

open Polynomial Finset

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, n = a' + 1 + k` from `⟨n - (a' + 1), by omega⟩`. Use `clear ha`. Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[add_zero, Finset.range_add_one, Finset.erase_insert Finset.notMem_range_self, Nat.sub_self, Nat.factorial_zero, mul_one, ← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect (fun x => x + 1) a']`.

Use `Finset.prod_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite `hm` using `[Finset.mem_range]`. Rewrite using `[show ((a' : ℤ) - (m : ℤ)) = (((a' - 1 - m) + 1 : ℕ) : ℤ) by omega, Int.natAbs_natCast]`. Consider the case `succ k ih`. Establish `hne : a' + 1 + k ∉ (range (a' + 1 + k)).erase a'` using `by simp`.

Rewrite using `[show a' + 1 + (k + 1) = (a' + 1 + k) + 1 by ring, Finset.range_add_one, Finset.erase_insert_of_ne (by omega : a' + 1 + k ≠ a'), Finset.prod_insert hne, ih]`. Rewrite using `[show a' + 1 + k + 1 - (a' + 1) = k + 1 by omega, show a' + 1 + k - (a' + 1) = k by omega, Nat.factorial_succ]`. Rewrite using `[show (a' : ℤ) - ((a' + 1 + k : ℕ) : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_neg, Int.natAbs_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem prod_natAbs_sub_erase (n a' : ℕ) (ha : a' < n) :
    ∏ m ∈ (range n).erase a', ((a' : ℤ) - m).natAbs = a'.factorial * (n - (a' + 1)).factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, n = a' + 1 + k := ⟨n - (a' + 1), by omega⟩
  clear ha
  induction k with
  | zero =>
    rw [add_zero, Finset.range_add_one, Finset.erase_insert Finset.notMem_range_self, Nat.sub_self,
      Nat.factorial_zero, mul_one, ← Finset.prod_range_add_one_eq_factorial,
      ← Finset.prod_range_reflect (fun x => x + 1) a']
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [show ((a' : ℤ) - (m : ℤ)) = (((a' - 1 - m) + 1 : ℕ) : ℤ) by omega, Int.natAbs_natCast]
  | succ k ih =>
    have hne : a' + 1 + k ∉ (range (a' + 1 + k)).erase a' := by simp
    rw [show a' + 1 + (k + 1) = (a' + 1 + k) + 1 by ring, Finset.range_add_one,
      Finset.erase_insert_of_ne (by omega : a' + 1 + k ≠ a'), Finset.prod_insert hne, ih]
    rw [show a' + 1 + k + 1 - (a' + 1) = k + 1 by omega, show a' + 1 + k - (a' + 1) = k by omega,
      Nat.factorial_succ]
    rw [show (a' : ℤ) - ((a' + 1 + k : ℕ) : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_neg,
      Int.natAbs_natCast]
    ring

/- English proof (translation)
Establish `h1` using `Finset.add_sum_erase (range (2 * a)) f (mem_range.2 (by omega : a' < 2 * a))`. Establish `h2` using `Finset.add_sum_erase (range a) f (mem_range.2 ha)`. Establish `h3` using `Finset.sum_range_add_sum_Ico f (by omega : a ≤ 2 * a)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_Ico_add_sum_erase (a a' : ℕ) (ha : a' < a) (f : ℕ → ℕ) :
    (∑ b ∈ Ico a (2 * a), f b) + ∑ m ∈ (range a).erase a', f m =
      ∑ m ∈ (range (2 * a)).erase a', f m := by
  have h1 := Finset.add_sum_erase (range (2 * a)) f (mem_range.2 (by omega : a' < 2 * a))
  have h2 := Finset.add_sum_erase (range a) f (mem_range.2 ha)
  have h3 := Finset.sum_range_add_sum_Ico f (by omega : a ≤ 2 * a)
  omega

/- English proof (translation)
Rewrite using `[sum_Ico_add_sum_erase a a' ha, sum_add_distrib, sum_const, card_erase_of_mem (mem_range.2 (by omega)), card_range, smul_eq_mul]`. Establish `hdvd : ℓ ^ (∑ m ∈ (range (2 * a)).erase a', padicValInt ℓ ((a' : ℤ) - m)) ∣ (2 * a).factorial`. Rewrite using `[← prod_pow_eq_pow_sum]`. Use `(prod_dvd_prod_of_dvd (fun m : ℕ => ℓ ^ padicValInt ℓ ((a' : ℤ) - m)) (fun m : ℕ => ((a' : ℤ) - m).natAbs) fun m _ => pow_padicValNat_dvd).trans ?_` and prove the remaining obligations. Rewrite using `[prod_natAbs_sub_erase (2 * a) a' (by omega)]`.

Conclude with `(Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial (by omega))`. Establish `h1` using `(padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).1 hdvd`. Establish `h2 : (2 * a - 1) * s ≤ 2 * a * s` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exponent_bound (ℓ : ℕ) [Fact ℓ.Prime] (s a a' : ℕ) (ha : a' < a) :
    (∑ b ∈ Ico a (2 * a), (s + padicValInt ℓ ((a' : ℤ) - b))) +
        ∑ m ∈ (range a).erase a', (s + padicValInt ℓ ((a' : ℤ) - m)) ≤
      2 * a * s + padicValNat ℓ (2 * a).factorial := by
  rw [sum_Ico_add_sum_erase a a' ha, sum_add_distrib, sum_const,
    card_erase_of_mem (mem_range.2 (by omega)), card_range, smul_eq_mul]
  have hdvd : ℓ ^ (∑ m ∈ (range (2 * a)).erase a', padicValInt ℓ ((a' : ℤ) - m)) ∣
      (2 * a).factorial := by
    rw [← prod_pow_eq_pow_sum]
    refine (prod_dvd_prod_of_dvd (fun m : ℕ => ℓ ^ padicValInt ℓ ((a' : ℤ) - m)) (fun m : ℕ => ((a' : ℤ) - m).natAbs)
      fun m _ => pow_padicValNat_dvd).trans ?_
    rw [prod_natAbs_sub_erase (2 * a) a' (by omega)]
    exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial (by omega))
  have h1 := (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).1 hdvd
  have h2 : (2 * a - 1) * s ≤ 2 * a * s := Nat.mul_le_mul_right _ (by omega)
  omega

/- English proof (translation)
Use `set u := PadicInt.unitCoeff hx with hu`. Establish `e : x = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ x.valuation` using `PadicInt.unitCoeff_spec hx`. Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1 : x * ↑u⁻¹ = (u : ℤ_[ℓ]) * ↑u⁻¹ * (ℓ : ℤ_[ℓ]) ^ x.valuation` using `by conv_lhs => rw [e]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, Units.mul_inv, one_mul]`.
-/
private theorem associated_val {ℓ : ℕ} [Fact ℓ.Prime] {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    Associated x ((ℓ : ℤ_[ℓ]) ^ x.valuation) := by
  set u := PadicInt.unitCoeff hx with hu
  have e : x = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ x.valuation := PadicInt.unitCoeff_spec hx
  refine ⟨u⁻¹, ?_⟩
  have h1 : x * ↑u⁻¹ = (u : ℤ_[ℓ]) * ↑u⁻¹ * (ℓ : ℤ_[ℓ]) ^ x.valuation := by
    conv_lhs => rw [e]
    ring
  rw [h1, Units.mul_inv, one_mul]

/- English proof (translation)
Establish `hk : (i : ℤ) - j ≠ 0` using `by omega`. Take `⟨hx0, hxv⟩` from `Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs hs2 hv _ hk`. Establish `hi : (u : ℤ_[ℓ]) ^ i = ((u ^ ((i : ℤ) - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (u : ℤ_[ℓ]) ^ j`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast u j, ← zpow_add, sub_add_cancel, zpow_natCast]`. Establish `he : (u : ℤ_[ℓ]) ^ i - (u : ℤ_[ℓ]) ^ j = (((u ^ ((i : ℤ) - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) * ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])`.

Rewrite using `[hi, Units.val_pow_eq_pow_val]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, ← hxv]`. Conclude with `(associated_mul_unit_left _ _ (Units.isUnit _)).trans (associated_val hx0)`.
-/
private theorem associated_pow_sub_pow (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : ℓ = 2 → 2 ≤ s) (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (i j : ℕ)
    (hij : i ≠ j) :
    Associated ((u : ℤ_[ℓ]) ^ i - (u : ℤ_[ℓ]) ^ j)
      ((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ ((i : ℤ) - j))) := by
  have hk : (i : ℤ) - j ≠ 0 := by omega
  obtain ⟨hx0, hxv⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs hs2 hv _ hk
  have hi : (u : ℤ_[ℓ]) ^ i = ((u ^ ((i : ℤ) - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (u : ℤ_[ℓ]) ^ j := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      ← zpow_natCast u j, ← zpow_add, sub_add_cancel, zpow_natCast]
  have he : (u : ℤ_[ℓ]) ^ i - (u : ℤ_[ℓ]) ^ j =
      (((u ^ ((i : ℤ) - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) * ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
    rw [hi, Units.val_pow_eq_pow_val]; ring
  rw [he, ← hxv]
  exact (associated_mul_unit_left _ _ (Units.isUnit _)).trans (associated_val hx0)

/- English proof (translation)
Introduce `ℓ _ u s hs hs2 hv a`. Establish `hdisj : Disjoint (range a) (Ico a (2 * a))`. Rewrite using `[disjoint_left]`. Introduce `x hx hx'`. Rewrite `hx` using `[mem_range]`.

Rewrite `hx'` using `[mem_Ico]`. Use linear arithmetic over natural numbers and integers. Establish `hass : ∀ i ∈ range a, ∀ j ∈ range a ∪ Ico a (2 * a), i ≠ j → Associated ((u : ℤ_[ℓ]) ^ i - (u : ℤ_[ℓ]) ^ j) ((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ ((i : ℤ) - j)))` using `fun i _ j _ hij => associated_pow_sub_pow ℓ u s hs hs2 hv i j hij`. Establish `key` using `h ℤ_[ℓ] (ℓ : ℤ_[ℓ]) ℕ (range a) (Ico a (2 * a)) (fun i => (u : ℤ_[ℓ]) ^ i) (fun i j => s + padicValInt ℓ ((i : ℤ) - j)) hdisj hass`. Establish `hle : ((range a).sup fun a' => (∑ b ∈ Ico a (2 * a), (s + padicValInt ℓ ((a' : ℤ) - b))) + ∑ m ∈ (range a).erase a', (s + padicValInt ℓ ((a' : ℤ) - m))) ≤ 2 * a * s + padicValNat ℓ (2 * a).factorial` using `Finset.sup_le fun a' ha' => exponent_bound ℓ s a a' (mem_range.1 ha')`.

Rewrite using `[← Nat.sub_add_cancel hle, pow_add, C_mul]`. Conclude with `Ideal.mul_mem_left _ _ key`.
-/
theorem lagrangeIdealCyc_of (h : LagrangeIdeal) : LagrangeIdealCyc := by
  intro ℓ _ u s hs hs2 hv a
  have hdisj : Disjoint (range a) (Ico a (2 * a)) := by
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_range] at hx
    rw [mem_Ico] at hx'
    omega
  have hass : ∀ i ∈ range a, ∀ j ∈ range a ∪ Ico a (2 * a), i ≠ j →
      Associated ((u : ℤ_[ℓ]) ^ i - (u : ℤ_[ℓ]) ^ j)
        ((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ ((i : ℤ) - j))) :=
    fun i _ j _ hij => associated_pow_sub_pow ℓ u s hs hs2 hv i j hij
  have key := h ℤ_[ℓ] (ℓ : ℤ_[ℓ]) ℕ (range a) (Ico a (2 * a)) (fun i => (u : ℤ_[ℓ]) ^ i)
    (fun i j => s + padicValInt ℓ ((i : ℤ) - j)) hdisj hass
  have hle : ((range a).sup fun a' => (∑ b ∈ Ico a (2 * a), (s + padicValInt ℓ ((a' : ℤ) - b))) +
      ∑ m ∈ (range a).erase a', (s + padicValInt ℓ ((a' : ℤ) - m))) ≤
      2 * a * s + padicValNat ℓ (2 * a).factorial :=
    Finset.sup_le fun a' ha' => exponent_bound ℓ s a a' (mem_range.1 ha')
  rw [← Nat.sub_add_cancel hle, pow_add, C_mul]
  exact Ideal.mul_mem_left _ _ key

end Formalism.LIFT
