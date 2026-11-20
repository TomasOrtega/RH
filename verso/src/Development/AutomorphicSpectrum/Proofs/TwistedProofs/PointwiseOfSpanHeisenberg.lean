import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertLen

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `only [mul_zero, zero_le']`. Take `⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k` from `⟨WithZero.log x, (WithZero.exp_log hx).symm⟩`. Rewrite using `[← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exp_inv_mul_le (n e : ℕ) (x : WithZero (Multiplicative ℤ)) :
    (WithZero.exp (n : ℤ))⁻¹ * x ≤ WithZero.exp (e : ℤ) ↔ x ≤ WithZero.exp ((n + e : ℕ) : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [mul_zero, zero_le']
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    push_cast
    omega

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `only [mul_zero]`. Apply the tactic sequence `constructor <;> intro h`. Conclude with `absurd h.symm WithZero.exp_ne_zero`. Conclude with `absurd h.symm WithZero.exp_ne_zero`.

Take `⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k` from `⟨WithZero.log x, (WithZero.exp_log hx).symm⟩`. Rewrite using `[← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj, WithZero.exp_inj]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem exp_inv_mul_eq (n e : ℕ) (x : WithZero (Multiplicative ℤ)) :
    (WithZero.exp (n : ℤ))⁻¹ * x = WithZero.exp (e : ℤ) ↔ x = WithZero.exp ((n + e : ℕ) : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [mul_zero]
    constructor <;> intro h
    · exact absurd h.symm WithZero.exp_ne_zero
    · exact absurd h.symm WithZero.exp_ne_zero
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_inj, WithZero.exp_inj]
    push_cast
    omega

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Conclude with `zero_le'`. Take `⟨k', rfl⟩ : ∃ k' : ℤ, x = WithZero.exp k'` from `⟨WithZero.log x, (WithZero.exp_log hx).symm⟩`. Rewrite `h` using `[WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Move the coercions through the operations in `at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_lt_exp {x : WithZero (Multiplicative ℤ)} {k : ℕ} (h : x < WithZero.exp ((k + 1 : ℕ) : ℤ)) :
    x ≤ WithZero.exp (k : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨k', rfl⟩ : ∃ k' : ℤ, x = WithZero.exp k' := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    push_cast at h
    omega

/- English proof (translation)
Rewrite using `[map_pow, hϖ, ← WithZero.exp_nsmul, ← WithZero.exp_neg]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem v_pow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (t : ℕ) :
    Valued.v (ϖ ^ t) = (WithZero.exp (t : ℤ))⁻¹ := by
  rw [map_pow, hϖ, ← WithZero.exp_nsmul, ← WithZero.exp_neg]
  congr 1
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ϖ ^ t * x ∈ (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ↔ _`. Rewrite using `[Valuation.mem_integer_iff, map_mul, v_pow hϖ]`. Establish `h` using `exp_inv_mul_le t 0 (Valued.v x)`. Simplify using `using h`.
-/
theorem mem_int_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (t : ℕ) (x : L) :
    ϖ ^ t * x ∈ intL L ↔ Valued.v x ≤ WithZero.exp (t : ℤ) := by
  change ϖ ^ t * x ∈ (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ↔ _
  rw [Valuation.mem_integer_iff, map_mul, v_pow hϖ]
  have h := exp_inv_mul_le t 0 (Valued.v x)
  simpa using h

/- English proof (translation)
Take `⟨i₀, -, hi₀⟩` from `Finset.exists_max_image Finset.univ (fun i => Valued.v (ρ i)) Finset.univ_nonempty`. Distinguish the cases in `h : Valued.v (ρ i₀) ≤ WithZero.exp ((0 : ℕ) : ℤ)`. Conclude with `⟨0, fun i => (hi₀ i (Finset.mem_univ _)).trans h, Or.inl rfl⟩`. Use `push_neg at h`. Establish `hne : Valued.v (ρ i₀) ≠ 0` using `ne_of_gt (lt_of_le_of_lt zero_le' h)`.

Establish `hk : WithZero.exp (WithZero.log (Valued.v (ρ i₀))) = Valued.v (ρ i₀)` using `WithZero.exp_log hne`. Establish `hk0 : (0 : ℤ) < WithZero.log (Valued.v (ρ i₀))`. Rewrite `h` using `[← hk, WithZero.exp_lt_exp]`. Conclude with `h` after adjusting the coercions. Use `⟨(WithZero.log (Valued.v (ρ i₀))).toNat, fun i => ?_, Or.inr ⟨i₀, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[Int.toNat_of_nonneg hk0.le, hk]`. Conclude with `hi₀ i (Finset.mem_univ _)`. Rewrite using `[Int.toNat_of_nonneg hk0.le, hk]`.
-/
theorem exists_bound {ι : Type} [Fintype ι] [Nonempty ι] (ρ : ι → L) :
    ∃ e : ℕ, (∀ i, Valued.v (ρ i) ≤ WithZero.exp (e : ℤ)) ∧ (e = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e : ℤ)) := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (ρ i)) Finset.univ_nonempty
  by_cases h : Valued.v (ρ i₀) ≤ WithZero.exp ((0 : ℕ) : ℤ)
  · exact ⟨0, fun i => (hi₀ i (Finset.mem_univ _)).trans h, Or.inl rfl⟩
  · push_neg at h
    have hne : Valued.v (ρ i₀) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' h)
    have hk : WithZero.exp (WithZero.log (Valued.v (ρ i₀))) = Valued.v (ρ i₀) := WithZero.exp_log hne
    have hk0 : (0 : ℤ) < WithZero.log (Valued.v (ρ i₀)) := by
      rw [← hk, WithZero.exp_lt_exp] at h
      exact_mod_cast h
    refine ⟨(WithZero.log (Valued.v (ρ i₀))).toNat, fun i => ?_, Or.inr ⟨i₀, ?_⟩⟩
    · rw [Int.toNat_of_nonneg hk0.le, hk]
      exact hi₀ i (Finset.mem_univ _)
    · rw [Int.toNat_of_nonneg hk0.le, hk]

/- English proof (translation)
Set `g : Option (Fin N ⊕ Fin N) → L` to `fun o => o.elim (ϖ ^ (-(A : ℤ))) (Sum.elim f₁ f₂)`. Establish `hg0 : Valued.v (g none) = WithZero.exp (A : ℤ)` using `by show Valued.v (ϖ ^ (-(A : ℤ))) = _`. Rewrite using `[map_zpow₀, hϖ, ← WithZero.exp_zsmul]`. Use `congr 1`. Simplify using the standard rewrite rules.

Take `⟨k, -, hk⟩` from `Finset.exists_max_image Finset.univ (fun o => Valued.v (g o)) Finset.univ_nonempty`. Use `⟨g k, hg0.ge.trans (hk none (Finset.mem_univ _)), fun i => hk (some (Sum.inl i)) (Finset.mem_univ _), fun i => hk (some (Sum.inr i)) (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Break down `k with _ | (i | i)` into its components or cases. Conclude with `Or.inl hg0`. Conclude with `Or.inr (Or.inl ⟨i, rfl⟩)`.

Conclude with `Or.inr (Or.inr ⟨i, rfl⟩)`.
-/
theorem exists_gen {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N : ℕ} (A : ℕ) (f₁ f₂ : Fin N → L) :
    ∃ y : L, WithZero.exp (A : ℤ) ≤ Valued.v y ∧ (∀ i, Valued.v (f₁ i) ≤ Valued.v y) ∧
      (∀ i, Valued.v (f₂ i) ≤ Valued.v y) ∧
      (Valued.v y = WithZero.exp (A : ℤ) ∨ (∃ i, Valued.v y = Valued.v (f₁ i)) ∨ ∃ i, Valued.v y = Valued.v (f₂ i)) := by
  classical
  let g : Option (Fin N ⊕ Fin N) → L := fun o => o.elim (ϖ ^ (-(A : ℤ))) (Sum.elim f₁ f₂)
  have hg0 : Valued.v (g none) = WithZero.exp (A : ℤ) := by
    show Valued.v (ϖ ^ (-(A : ℤ))) = _
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
    congr 1
    simp
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun o => Valued.v (g o)) Finset.univ_nonempty
  refine ⟨g k, hg0.ge.trans (hk none (Finset.mem_univ _)), fun i => hk (some (Sum.inl i)) (Finset.mem_univ _),
    fun i => hk (some (Sum.inr i)) (Finset.mem_univ _), ?_⟩
  rcases k with _ | (i | i)
  · exact Or.inl hg0
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

/- English proof (translation)
Establish `key : ∀ a b : ℕ, WithZero.exp (a : ℤ) ≤ WithZero.exp (b : ℤ) ↔ a ≤ b` using `fun a b => by`. Rewrite using `[WithZero.exp_le_exp]`. Conclude with `Nat.cast_le`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hY2 : Y ≤ A + j / 2`. Break down `hYs with rfl | ⟨i₀, hi₀⟩` into its components or cases. Use linear arithmetic over natural numbers and integers. Use `(key _ _).1 (hi₀.symm.le.trans (he₁ i₀))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `⟨fun i => (hY i).trans ((key _ _).2 hY2), he₂.trans ((key _ _).2 (by omega))⟩`. Introduce and unpack `⟨hR, hT⟩`. Establish `hY2 : Y ≤ A + j / 2`. Break down `hYs with rfl | ⟨i₀, hi₀⟩` into its components or cases. Use linear arithmetic over natural numbers and integers.

Conclude with `(key _ _).1 (hi₀.symm.le.trans (hR i₀))`. Break down `he₃ with rfl | ⟨i₁, hi₁⟩ | hT'` into its components or cases. Use linear arithmetic over natural numbers and integers. Use `(key _ _).1 (hi₁.symm.le.trans (hR i₁))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `(key _ _).1 (hT'.symm.le.trans hT)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem excess_iff {ι : Type} (R : ι → WithZero (Multiplicative ℤ)) (T : WithZero (Multiplicative ℤ)) (A Y e j : ℕ)
    (hAY : A ≤ Y) (hY : ∀ i, R i ≤ WithZero.exp (Y : ℤ)) (hYs : Y = A ∨ ∃ i, R i = WithZero.exp (Y : ℤ))
    (he₁ : ∀ i, R i ≤ WithZero.exp ((A + e : ℕ) : ℤ)) (he₂ : T ≤ WithZero.exp ((A + Y + e : ℕ) : ℤ))
    (he₃ : e = 0 ∨ (∃ i, R i = WithZero.exp ((A + e : ℕ) : ℤ)) ∨ T = WithZero.exp ((A + Y + e : ℕ) : ℤ)) :
    Y + e ≤ A + j ↔ (∀ i, R i ≤ WithZero.exp ((A + j / 2 : ℕ) : ℤ)) ∧ T ≤ WithZero.exp ((2 * A + j : ℕ) : ℤ) := by
  have key : ∀ a b : ℕ, WithZero.exp (a : ℤ) ≤ WithZero.exp (b : ℤ) ↔ a ≤ b := fun a b => by
    rw [WithZero.exp_le_exp]
    exact Nat.cast_le
  constructor
  · intro h
    have hY2 : Y ≤ A + j / 2 := by
      rcases hYs with rfl | ⟨i₀, hi₀⟩
      · omega
      · have := (key _ _).1 (hi₀.symm.le.trans (he₁ i₀))
        omega
    exact ⟨fun i => (hY i).trans ((key _ _).2 hY2), he₂.trans ((key _ _).2 (by omega))⟩
  · rintro ⟨hR, hT⟩
    have hY2 : Y ≤ A + j / 2 := by
      rcases hYs with rfl | ⟨i₀, hi₀⟩
      · omega
      · exact (key _ _).1 (hi₀.symm.le.trans (hR i₀))
    rcases he₃ with rfl | ⟨i₁, hi₁⟩ | hT'
    · omega
    · have := (key _ _).1 (hi₁.symm.le.trans (hR i₁))
      omega
    · have := (key _ _).1 (hT'.symm.le.trans hT)
      omega

end Val

section Blocks

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

/- English proof (translation)
Establish `hmul : ∀ i j, mat (m * u) i j = ∑ k, mat m i k * mat u k j` using `fun i j => by`. Rewrite using `[show mat (m * u) = mat m * mat u from rfl, Matrix.mul_apply]`. Establish `hL : ∀ i j, blk N i ≠ blk N j → mat m i j = 0` using `hm.1`. Establish `hR : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j` using `hu`. Establish `hm00 : mat m 0 0 = ϖ ^ a` using `hm.2.1`.

Establish `hmll : mat m (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a)` using `hm.2.2.1`. Establish `hmmm : ∀ i j, mat m (mid i) (mid j) = mat g₀ i j` using `hm.2.2.2`. Establish `h0mid : ∀ k, mat m 0 (mid k) = 0` using `fun k => hL _ _ (by rw [blk_zero, blk_mid]; decide)`. Establish `h0last : mat m 0 (Fin.last (N + 1)) = 0` using `hL _ _ (by rw [blk_zero, blk_last]; decide)`. Establish `hmid0 : ∀ i, mat m (mid i) 0 = 0` using `fun i => hL _ _ (by rw [blk_zero, blk_mid]; decide)`.

Establish `hmidl : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0` using `fun i => hL _ _ (by rw [blk_last, blk_mid]; decide)`. Establish `hl0 : mat m (Fin.last (N + 1)) 0 = 0` using `hL _ _ (by rw [blk_zero, blk_last]; decide)`. Establish `hlmid : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0` using `fun j => hL _ _ (by rw [blk_last, blk_mid]; decide)`. Establish `hu00 : mat u 0 0 = 1` using `by rw [hR 0 0 le_rfl, Matrix.one_apply_eq]`. Establish `humid0 : ∀ k, mat u (mid k) 0 = 0` using `fun k => by`.

Rewrite using `[hR _ _ (by rw [blk_zero]; exact Nat.zero_le _), Matrix.one_apply_ne (mid_ne_zero k)]`. Establish `hul0 : mat u (Fin.last (N + 1)) 0 = 0`. Rewrite using `[hR _ _ (by rw [blk_zero]; exact Nat.zero_le _), Matrix.one_apply_ne last_ne_zero]`. Establish `hummid : ∀ k j, mat u (mid k) (mid j) = if k = j then 1 else 0` using `fun k j => by`. Rewrite using `[hR _ _ (by rw [blk_mid, blk_mid])]`.

Simplify using `only [Matrix.one_apply, mid_injective.eq_iff]`. Establish `hulmid : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0` using `fun j => by`. Rewrite using `[hR _ _ (by rw [blk_last, blk_mid]; decide), Matrix.one_apply_ne (mid_ne_last j).symm]`. Establish `hull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1` using `by rw [hR _ _ le_rfl, Matrix.one_apply_eq]`. Use `⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmul, sum_idx]`. Simplify using `[hm00, h0mid, h0last, hu00]`. Rewrite using `[hmul, sum_idx]`. Simplify using `[hm00, h0mid, h0last, rowOf]`. Rewrite using `[hmul, sum_idx]`.

Simplify using `[hm00, h0mid, h0last, cornerOf]`. Rewrite using `[hmul, sum_idx]`. Simplify using `[hmid0, humid0, hmidl]`. Rewrite using `[hmul, sum_idx]`. Simplify using `[hmid0, hmmm, hummid, hmidl]`.

Rewrite using `[hmul, sum_idx]`. Simplify using `[hmid0, hmmm, hmidl, Matrix.mulVec, dotProduct, colOf]`. Rewrite using `[hmul, sum_idx]`. Simplify using `[hl0, hlmid, hul0]`. Rewrite using `[hmul, sum_idx]`.

Simplify using `[hl0, hlmid, hulmid]`. Rewrite using `[hmul, sum_idx]`. Simplify using `[hl0, hlmid, hmll, hull]`.
-/
theorem entries {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m) {u : GU σ (N + 2)}
    (hu : u ∈ radQ σ N) :
    mat (m * u) 0 0 = ϖ ^ a ∧ (∀ j, mat (m * u) 0 (mid j) = ϖ ^ a * rowOf u j) ∧
    mat (m * u) 0 (Fin.last (N + 1)) = ϖ ^ a * cornerOf u ∧ (∀ i, mat (m * u) (mid i) 0 = 0) ∧
    (∀ i j, mat (m * u) (mid i) (mid j) = mat g₀ i j) ∧
    (∀ i, mat (m * u) (mid i) (Fin.last (N + 1)) = (mat g₀ *ᵥ colOf u) i) ∧
    mat (m * u) (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, mat (m * u) (Fin.last (N + 1)) (mid j) = 0) ∧
    mat (m * u) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := by
  have hmul : ∀ i j, mat (m * u) i j = ∑ k, mat m i k * mat u k j := fun i j => by
    rw [show mat (m * u) = mat m * mat u from rfl, Matrix.mul_apply]
  have hL : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm.1
  have hR : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  have hm00 : mat m 0 0 = ϖ ^ a := hm.2.1
  have hmll : mat m (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := hm.2.2.1
  have hmmm : ∀ i j, mat m (mid i) (mid j) = mat g₀ i j := hm.2.2.2
  have h0mid : ∀ k, mat m 0 (mid k) = 0 := fun k => hL _ _ (by rw [blk_zero, blk_mid]; decide)
  have h0last : mat m 0 (Fin.last (N + 1)) = 0 := hL _ _ (by rw [blk_zero, blk_last]; decide)
  have hmid0 : ∀ i, mat m (mid i) 0 = 0 := fun i => hL _ _ (by rw [blk_zero, blk_mid]; decide)
  have hmidl : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0 := fun i => hL _ _ (by rw [blk_last, blk_mid]; decide)
  have hl0 : mat m (Fin.last (N + 1)) 0 = 0 := hL _ _ (by rw [blk_zero, blk_last]; decide)
  have hlmid : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0 := fun j => hL _ _ (by rw [blk_last, blk_mid]; decide)
  have hu00 : mat u 0 0 = 1 := by rw [hR 0 0 le_rfl, Matrix.one_apply_eq]
  have humid0 : ∀ k, mat u (mid k) 0 = 0 := fun k => by
    rw [hR _ _ (by rw [blk_zero]; exact Nat.zero_le _), Matrix.one_apply_ne (mid_ne_zero k)]
  have hul0 : mat u (Fin.last (N + 1)) 0 = 0 := by
    rw [hR _ _ (by rw [blk_zero]; exact Nat.zero_le _), Matrix.one_apply_ne last_ne_zero]
  have hummid : ∀ k j, mat u (mid k) (mid j) = if k = j then 1 else 0 := fun k j => by
    rw [hR _ _ (by rw [blk_mid, blk_mid])]
    simp only [Matrix.one_apply, mid_injective.eq_iff]
  have hulmid : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0 := fun j => by
    rw [hR _ _ (by rw [blk_last, blk_mid]; decide), Matrix.one_apply_ne (mid_ne_last j).symm]
  have hull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by rw [hR _ _ le_rfl, Matrix.one_apply_eq]
  refine ⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩
  · rw [hmul, sum_idx]; simp [hm00, h0mid, h0last, hu00]
  · rw [hmul, sum_idx]; simp [hm00, h0mid, h0last, rowOf]
  · rw [hmul, sum_idx]; simp [hm00, h0mid, h0last, cornerOf]
  · rw [hmul, sum_idx]; simp [hmid0, humid0, hmidl]
  · rw [hmul, sum_idx]; simp [hmid0, hmmm, hummid, hmidl]
  · rw [hmul, sum_idx]; simp [hmid0, hmmm, hmidl, Matrix.mulVec, dotProduct, colOf]
  · rw [hmul, sum_idx]; simp [hl0, hlmid, hul0]
  · rw [hmul, sum_idx]; simp [hl0, hlmid, hulmid]
  · rw [hmul, sum_idx]; simp [hl0, hlmid, hmll, hull]

end Blocks

/- English proof (translation)
Introduce `hAdd hDual hSpan hHeis L instF instV ϖ σ q N hun a g₀ m hm U V C l hfrac hC u hu`. Establish `hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hun.2.2.2.1`. Establish `hrb : ∀ j, rowOf u j = -σ (colOf u j.rev)` using `((hHeis L ϖ σ q N hun).1 u hu).1`. Take `⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩` from `entries hm hu`. Take `⟨y, hyA, hy₁, hy₂, hyor⟩` from `exists_gen hϖ a.toNat ((C * V * mat g₀) *ᵥ colOf u) ((mat g₀ * C * U) *ᵥ colOf u)`.

Take `⟨P, ρ, hP, hρ0, hρmid, hρlast, hspan⟩` from `hSpan L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u) (colOf u) (cornerOf u) y hϖ hfrac e1 e2 e3 e4 e5 e6 e7 e8 e9 hyA hy₁ hy₂ hyor`. Establish `hy0 : Valued.v y ≠ 0`. Introduce `h`. Rewrite `hyA` using `[h]`. Conclude with `WithZero.exp_ne_zero (le_antisymm hyA zero_le')`.

Establish `hlog : ((a.toNat : ℕ) : ℤ) ≤ WithZero.log (Valued.v y)`. Rewrite using `[← WithZero.exp_le_exp, WithZero.exp_log hy0]`. Conclude with `hyA`. Take `⟨Y, hvy⟩ : ∃ Y : ℕ, Valued.v y = WithZero.exp (Y : ℤ)` from `⟨(WithZero.log (Valued.v y)).toNat, by`. Rewrite using `[Int.toNat_of_nonneg (le_trans (Nat.cast_nonneg _) hlog), WithZero.exp_log hy0]⟩`.

Establish `hAY : a.toNat ≤ Y`. Establish `h` using `hlog`. Rewrite `h` using `[hvy, WithZero.log_exp]`. Conclude with `h` after adjusting the coercions. Take `⟨e, hρe, heor⟩` from `exists_bound ρ`.

Establish `hdet : Valued.v P.det = WithZero.exp (((-a).toNat : ℤ) + (l : ℤ) + (Y : ℤ))`. Rewrite using `[hP, hC, hvy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]`. Establish `hLat` using `hAdd L (N + 2) P (((-a).toNat : ℤ) + (l : ℤ) + (Y : ℤ)) ρ e hdet hρe heor`. Rewrite `hLat` using `[← hspan]`. Establish `hHas : HasLen (mat (m * u)) ((-a).toNat + l + Y + e)` using `hasLen_of_latLen (by push_cast; exact hLat)`.

Establish `hlen` using `hHas.len_eq`. Establish `tr : ∀ s : ℕ, (∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp (s : ℤ)) ↔ (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp (s : ℤ)) ∧ (∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp (s : ℤ))`. Introduce `s`. Establish `h` using `hDual L ϖ σ q N hun g₀ U V C hfrac (rowOf u) (colOf u) (ϖ ^ s) hrb`. Simplify using `only [mem_int_iff hϖ] at h`.

Conclude with `h`. Establish `hY : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp (Y : ℤ)` using `(tr Y).2 ⟨fun i => (hy₁ i).trans hvy.le, fun i => (hy₂ i).trans hvy.le⟩`. Establish `hYs : Y = a.toNat ∨ ∃ j, Valued.v (Matrix.vecMul (rowOf u) C j) = WithZero.exp (Y : ℤ)`. Distinguish the cases in `hYA : Y = a.toNat`. Conclude with `Or.inl hYA`.

Use `right`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hlt : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp ((Y - 1 : ℕ) : ℤ)`. Introduce `j`.

Apply `le_of_lt_exp` to reduce the goal to its premises. Establish `h1 : Y - 1 + 1 = Y` using `by omega`. Rewrite using `[h1]`. Conclude with `lt_of_le_of_ne (hY j) (hne j)`. Establish `hf` using `(tr (Y - 1)).1 hlt`.

Establish `hbig : WithZero.exp (Y : ℤ) ≤ WithZero.exp ((Y - 1 : ℕ) : ℤ)`. Break down `hyor with h | ⟨i, h⟩ | ⟨i, h⟩` into its components or cases. It suffices to derive a contradiction. Apply `hYA` to reduce the goal to its premises. Rewrite `h` using `[hvy]`.

Conclude with `WithZero.exp_inj.1 h` after adjusting the coercions. Rewrite using `[← hvy, h]`. Conclude with `hf.1 i`. Rewrite using `[← hvy, h]`. Conclude with `hf.2 i`.

Rewrite `hbig` using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hvρmid : ∀ j, Valued.v (ρ (mid j)) = (WithZero.exp (a.toNat : ℤ))⁻¹ * Valued.v (Matrix.vecMul (rowOf u) C j)` using `fun j => by`. Rewrite using `[hρmid j, map_mul, v_pow hϖ]`. Establish `hvρlast : Valued.v (ρ (Fin.last (N + 1))) = (WithZero.exp ((a.toNat + Y : ℕ) : ℤ))⁻¹ * Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u)`.

Rewrite using `[hρlast, map_div₀, map_mul, v_pow hϖ, hvy, Nat.cast_add, WithZero.exp_add, mul_inv, div_eq_mul_inv, mul_right_comm]`. Establish `he₁ : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)` using `fun j => by`. Establish `h` using `hρe (mid j)`. Rewrite `h` using `[hvρmid j]`. Conclude with `(exp_inv_mul_le _ _ _).1 h`.

Establish `he₂ : Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) ≤ WithZero.exp ((a.toNat + Y + e : ℕ) : ℤ)`. Establish `h` using `hρe (Fin.last (N + 1))`. Rewrite `h` using `[hvρlast]`. Conclude with `(exp_inv_mul_le _ _ _).1 h`. Establish `he₃ : e = 0 ∨ (∃ j, Valued.v (Matrix.vecMul (rowOf u) C j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∨ Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) = WithZero.exp ((a.toNat + Y + e : ℕ) : ℤ)`.

Break down `heor with h | ⟨i, hi⟩` into its components or cases. Conclude with `Or.inl h`. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Rewrite `hi` using `[hρ0, map_zero]`. Conclude with `absurd hi.symm WithZero.exp_ne_zero`.

Rewrite `hi` using `[hvρmid j]`. Conclude with `Or.inr (Or.inl ⟨j, (exp_inv_mul_eq _ _ _).1 hi⟩)`. Rewrite `hi` using `[hvρlast]`. Conclude with `Or.inr (Or.inr ((exp_inv_mul_eq _ _ _).1 hi))`. Establish `hnat : a.natAbs = a.toNat + (-a).toNat` using `by omega`.

Use `⟨by rw [hlen]; omega, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hlen]`. Establish `hex` using `excess_iff (fun i => Valued.v (Matrix.vecMul (rowOf u) C i)) (Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u)) a.toNat Y e j hAY hY hYs he₁ he₂ he₃`. Establish `hsm : GlobalTheory.InertZeta.Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔ ((∀ i, Valued.v (Matrix.vecMul (rowOf u) C i) ≤ WithZero.exp ((a.toNat + j / 2 : ℕ) : ℤ)) ∧ Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) ≤ WithZero.exp ((2 * a.toNat …`. Unfold `GlobalTheory.InertZeta.Small`.

Simplify using `only [mem_int_iff hϖ]`. Conclude with `⟨fun h => hsm.2 (hex.1 (by omega)), fun h => by have h' := hex.2 (hsm.1 h); omega⟩`.
-/
theorem pointwise : AddVec → Dual → SpanEq → Heis → Pointwise := by
  intro hAdd hDual hSpan hHeis L instF instV ϖ σ q N hun a g₀ m hm U V C l hfrac hC u hu
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hun.2.2.2.1
  have hrb : ∀ j, rowOf u j = -σ (colOf u j.rev) := ((hHeis L ϖ σ q N hun).1 u hu).1
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := entries hm hu
  obtain ⟨y, hyA, hy₁, hy₂, hyor⟩ :=
    exists_gen hϖ a.toNat ((C * V * mat g₀) *ᵥ colOf u) ((mat g₀ * C * U) *ᵥ colOf u)
  obtain ⟨P, ρ, hP, hρ0, hρmid, hρlast, hspan⟩ := hSpan L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u)
    (colOf u) (cornerOf u) y hϖ hfrac e1 e2 e3 e4 e5 e6 e7 e8 e9 hyA hy₁ hy₂ hyor
  have hy0 : Valued.v y ≠ 0 := by
    intro h
    rw [h] at hyA
    exact WithZero.exp_ne_zero (le_antisymm hyA zero_le')
  have hlog : ((a.toNat : ℕ) : ℤ) ≤ WithZero.log (Valued.v y) := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hy0]
    exact hyA
  obtain ⟨Y, hvy⟩ : ∃ Y : ℕ, Valued.v y = WithZero.exp (Y : ℤ) :=
    ⟨(WithZero.log (Valued.v y)).toNat, by
      rw [Int.toNat_of_nonneg (le_trans (Nat.cast_nonneg _) hlog), WithZero.exp_log hy0]⟩
  have hAY : a.toNat ≤ Y := by
    have h := hlog
    rw [hvy, WithZero.log_exp] at h
    exact_mod_cast h
  obtain ⟨e, hρe, heor⟩ := exists_bound ρ
  have hdet : Valued.v P.det = WithZero.exp (((-a).toNat : ℤ) + (l : ℤ) + (Y : ℤ)) := by
    rw [hP, hC, hvy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]
  have hLat := hAdd L (N + 2) P (((-a).toNat : ℤ) + (l : ℤ) + (Y : ℤ)) ρ e hdet hρe heor
  rw [← hspan] at hLat
  have hHas : HasLen (mat (m * u)) ((-a).toNat + l + Y + e) := hasLen_of_latLen (by push_cast; exact hLat)
  have hlen := hHas.len_eq
  have tr : ∀ s : ℕ, (∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp (s : ℤ)) ↔
      (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp (s : ℤ)) ∧
      (∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp (s : ℤ)) := by
    intro s
    have h := hDual L ϖ σ q N hun g₀ U V C hfrac (rowOf u) (colOf u) (ϖ ^ s) hrb
    simp only [mem_int_iff hϖ] at h
    exact h
  have hY : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp (Y : ℤ) :=
    (tr Y).2 ⟨fun i => (hy₁ i).trans hvy.le, fun i => (hy₂ i).trans hvy.le⟩
  have hYs : Y = a.toNat ∨ ∃ j, Valued.v (Matrix.vecMul (rowOf u) C j) = WithZero.exp (Y : ℤ) := by
    by_cases hYA : Y = a.toNat
    · exact Or.inl hYA
    · right
      by_contra hne
      push_neg at hne
      have hlt : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp ((Y - 1 : ℕ) : ℤ) := by
        intro j
        apply le_of_lt_exp
        have h1 : Y - 1 + 1 = Y := by omega
        rw [h1]
        exact lt_of_le_of_ne (hY j) (hne j)
      have hf := (tr (Y - 1)).1 hlt
      have hbig : WithZero.exp (Y : ℤ) ≤ WithZero.exp ((Y - 1 : ℕ) : ℤ) := by
        rcases hyor with h | ⟨i, h⟩ | ⟨i, h⟩
        · exfalso
          apply hYA
          rw [hvy] at h
          exact_mod_cast WithZero.exp_inj.1 h
        · rw [← hvy, h]
          exact hf.1 i
        · rw [← hvy, h]
          exact hf.2 i
      rw [WithZero.exp_le_exp] at hbig
      omega
  have hvρmid : ∀ j, Valued.v (ρ (mid j)) =
      (WithZero.exp (a.toNat : ℤ))⁻¹ * Valued.v (Matrix.vecMul (rowOf u) C j) := fun j => by
    rw [hρmid j, map_mul, v_pow hϖ]
  have hvρlast : Valued.v (ρ (Fin.last (N + 1))) = (WithZero.exp ((a.toNat + Y : ℕ) : ℤ))⁻¹ *
      Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) := by
    rw [hρlast, map_div₀, map_mul, v_pow hϖ, hvy, Nat.cast_add, WithZero.exp_add, mul_inv, div_eq_mul_inv,
      mul_right_comm]
  have he₁ : ∀ j, Valued.v (Matrix.vecMul (rowOf u) C j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun j => by
    have h := hρe (mid j)
    rw [hvρmid j] at h
    exact (exp_inv_mul_le _ _ _).1 h
  have he₂ : Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) ≤
      WithZero.exp ((a.toNat + Y + e : ℕ) : ℤ) := by
    have h := hρe (Fin.last (N + 1))
    rw [hvρlast] at h
    exact (exp_inv_mul_le _ _ _).1 h
  have he₃ : e = 0 ∨ (∃ j, Valued.v (Matrix.vecMul (rowOf u) C j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∨
      Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) =
        WithZero.exp ((a.toNat + Y + e : ℕ) : ℤ) := by
    rcases heor with h | ⟨i, hi⟩
    · exact Or.inl h
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [hρ0, map_zero] at hi
        exact absurd hi.symm WithZero.exp_ne_zero
      · rw [hvρmid j] at hi
        exact Or.inr (Or.inl ⟨j, (exp_inv_mul_eq _ _ _).1 hi⟩)
      · rw [hvρlast] at hi
        exact Or.inr (Or.inr ((exp_inv_mul_eq _ _ _).1 hi))
  have hnat : a.natAbs = a.toNat + (-a).toNat := by omega
  refine ⟨by rw [hlen]; omega, fun j => ?_⟩
  rw [hlen]
  have hex := excess_iff (fun i => Valued.v (Matrix.vecMul (rowOf u) C i))
    (Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u)) a.toNat Y e j hAY hY hYs he₁ he₂ he₃
  have hsm : GlobalTheory.InertZeta.Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔
      ((∀ i, Valued.v (Matrix.vecMul (rowOf u) C i) ≤ WithZero.exp ((a.toNat + j / 2 : ℕ) : ℤ)) ∧
        Valued.v (cornerOf u - rowOf u ⬝ᵥ (C * V * mat g₀) *ᵥ colOf u) ≤
          WithZero.exp ((2 * a.toNat + j : ℕ) : ℤ)) := by
    unfold GlobalTheory.InertZeta.Small
    simp only [mem_int_iff hϖ]
  exact ⟨fun h => hsm.2 (hex.1 (by omega)), fun h => by have h' := hex.2 (hsm.1 h); omega⟩

end GlobalTheory.CompanionTheory.InertLen

end
