import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardSpacedDetectedLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZetaZeroDetect
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumTruncConv

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroCells

/- English proof (translation)
Take `⟨k, hk⟩` from `Int.ModEq.dvd hpar`. Establish `hx1` using `Int.floor_le x`. Establish `hx2` using `Int.lt_floor_add_one x`. Establish `hy1` using `Int.floor_le y`. Establish `hy2` using `Int.lt_floor_add_one y`.

Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `h2 : ⌊x⌋ + 2 ≤ ⌊y⌋` using `by omega`. Establish `h2' : (⌊x⌋ : ℝ) + 2 ≤ ⌊y⌋` using `by exact_mod_cast h2`. Rewrite using `[le_abs]`. Use `right`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ⌊y⌋ + 2 ≤ ⌊x⌋` using `by omega`. Establish `h2' : (⌊y⌋ : ℝ) + 2 ≤ ⌊x⌋` using `by exact_mod_cast h2`. Rewrite using `[le_abs]`. Use `left`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_le_abs_sub_of_floor {x y : ℝ} (hne : ⌊x⌋ ≠ ⌊y⌋) (hpar : ⌊x⌋ % 2 = ⌊y⌋ % 2) :
    1 ≤ |x - y| := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hpar
  have hx1 := Int.floor_le x
  have hx2 := Int.lt_floor_add_one x
  have hy1 := Int.floor_le y
  have hy2 := Int.lt_floor_add_one y
  rcases lt_or_gt_of_ne hne with h | h
  · have h2 : ⌊x⌋ + 2 ≤ ⌊y⌋ := by omega
    have h2' : (⌊x⌋ : ℝ) + 2 ≤ ⌊y⌋ := by exact_mod_cast h2
    rw [le_abs]
    right
    linarith
  · have h2 : ⌊y⌋ + 2 ≤ ⌊x⌋ := by omega
    have h2' : (⌊y⌋ : ℝ) + 2 ≤ ⌊x⌋ := by exact_mod_cast h2
    rw [le_abs]
    left
    linarith

/- English proof (translation)
Introduce and unpack `rfl`. Rewrite `h` using `[isPrimitive_def, conductor_one]`. Use linear arithmetic over natural numbers and integers.
-/
lemma ne_one_of_primitive {N : ℕ} (hN : N ≠ 0) {χ : DirichletCharacter ℂ (N + 1)}
    (h : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  rw [isPrimitive_def, conductor_one] at h
  omega

/- English proof (translation)
Establish `hback : ∀ r ∈ (U.image f).image (Function.invFunOn f ↑U), Function.invFunOn f ↑U (f r) = r`. Introduce `r hr`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hr`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hc`. Rewrite using `[Function.invFunOn_eq (f := f) (s := ↑U) ⟨p, hp, rfl⟩]`.

Use `⟨(U.image f).image (Function.invFunOn f ↑U), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hr`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hc`. Conclude with `Function.invFunOn_mem ⟨p, hp, rfl⟩`.

Use `(Finset.card_image_of_injOn ?_).symm` and prove the remaining obligations. Introduce `c hc c' hc' h`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hc)`. Take `⟨p', hp', rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hc')`. Combine the equalities or inequalities in the displayed calculation.

Introduce `r hr r' hr' h`. Rewrite using `[← hback r hr, ← hback r' hr', h]`.
-/
private theorem exists_subset_injOn_card_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Nonempty α] (U : Finset α) (f : α → β) :
    ∃ R ⊆ U, (U.image f).card = R.card ∧ ∀ r ∈ R, ∀ r' ∈ R, f r = f r' → r = r' := by
  have hback : ∀ r ∈ (U.image f).image (Function.invFunOn f ↑U),
      Function.invFunOn f ↑U (f r) = r := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    rw [Function.invFunOn_eq (f := f) (s := ↑U) ⟨p, hp, rfl⟩]
  refine ⟨(U.image f).image (Function.invFunOn f ↑U), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    exact Function.invFunOn_mem ⟨p, hp, rfl⟩
  · refine (Finset.card_image_of_injOn ?_).symm
    intro c hc c' hc' h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc')
    calc f p = f (Function.invFunOn f ↑U (f p)) :=
          (Function.invFunOn_eq (f := f) (s := ↑U) ⟨p, hp, rfl⟩).symm
      _ = f (Function.invFunOn f ↑U (f p')) := by rw [h]
      _ = f p' := Function.invFunOn_eq (f := f) (s := ↑U) ⟨p', hp', rfl⟩
  · intro r hr r' hr' h
    rw [← hback r hr, ← hback r' hr', h]

/- English proof (translation)
Take `⟨Q₁, hQ₁⟩` from `GlobalTheory.ZeroDetect.zero_detect`. Take `⟨Q₂, hQ₂⟩` from `GlobalTheory.ZeroDetect.zeta_zero_detect`. Take `⟨C₁, hC₁, hsp⟩` from `GlobalTheory.SpacedDetected.card_spaced_detected_le`. Use `⟨(2 * C₁ + 5) * ((Q₁ + Q₂ + 2 : ℕ) : ℝ), by positivity, ?_⟩` and prove the remaining obligations. Introduce `Q hQ T hT`.

Use `set Qn : ℕ := max (max Q₁ Q₂) ⌈Q⌉₊ with hQn_def`. Establish `hceil3 : 2 < ⌈Q⌉₊` using `Nat.lt_ceil.2 (by push_cast; linarith)`. Establish `hQn2 : 2 ≤ Qn` using `le_trans (by omega : 2 ≤ ⌈Q⌉₊) (le_max_right _ _)`. Establish `hQle : Q ≤ (Qn : ℝ)` using `(Nat.le_ceil Q).trans (by exact_mod_cast le_max_right _ _)`. Establish `hQn1 : (1 : ℝ) ≤ Qn` using `by exact_mod_cast (by omega : 1 ≤ Qn)`.

Establish `hQnpos : (0 : ℝ) < Qn` using `by linarith`. Establish `hQnle : (Qn : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q`. Establish `h1 : Qn ≤ Q₁ + Q₂ + ⌈Q⌉₊` using `max_le (max_le (by omega) (by omega)) (by omega)`. Establish `h2 : (⌈Q⌉₊ : ℝ) < Q + 1` using `Nat.ceil_lt_add_one (by linarith)`. Establish `h1' : (Qn : ℝ) ≤ Q₁ + Q₂ + ⌈Q⌉₊` using `by exact_mod_cast h1`.

Establish `h3 : (0 : ℝ) ≤ Q₁` using `Nat.cast_nonneg _`. Establish `h4 : (0 : ℝ) ≤ Q₂` using `Nat.cast_nonneg _`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpow : (Qn : ℝ) ^ ((1 : ℝ) / 8) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8)`.

Establish `hB : (1 : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ Q₁ + Q₂ + 2)`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hA : ∀ p ∈ T, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) → p.1 + 1 ≤ Qn ∧ p.2.1.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ p.2.2.re ≤ 1 ∧ |p.2.2.im| ≤ Qn ∧ (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : …`. Introduce and unpack `⟨N, χ, ρ⟩ hp hns`.

Take `⟨hlev, hprim, hL, hre, him⟩ : ((N + 1 : ℕ) : ℝ) ≤ Q ∧ χ.IsPrimitive ∧ LFunction χ ρ = 0 ∧ 1 - 1 / 400 ≤ ρ.re ∧ |ρ.im| ≤ Q` from `hT _ hp`. Establish `hlevN : N + 1 ≤ Qn`. Establish `: ((N + 1 : ℕ) : ℝ) ≤ (Qn : ℝ)` using `hlev.trans hQle`. Conclude with `this` after adjusting the coercions. Establish `him' : |ρ.im| ≤ (Qn : ℝ)` using `him.trans hQle`.

Establish `hre1 : ρ.re ≤ 1`. Assume the negation of the conclusion as `hgt`. Rewrite `hgt` using `[not_le]`. Establish `hne : ρ ≠ 1`. Introduce `h`.

Rewrite `hgt` using `[h, Complex.one_re]`. Conclude with `lt_irrefl _ hgt`. Conclude with `LFunction_ne_zero_of_one_le_re χ (.inr hne) hgt.le hL`. Use `⟨hlevN, hprim, hre, hre1, him', ?_⟩` and prove the remaining obligations. Distinguish the cases in `hN : N = 0`.

Substitute `hN` using the available equality. Establish `hpos : 0 < (Qn : ℝ) ^ ((1 : ℝ) / 20)` using `Real.rpow_pos_of_pos hQnpos _`. Establish `hbig : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ |ρ.im|`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`.

Conclude with `hns ⟨rfl, h⟩`. Establish `hne1 : ρ ≠ 1`. Introduce `h`. Rewrite `hbig` using `[h, Complex.one_im, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hrelt : ρ.re < 1`. Break down `lt_or_eq_of_le hre1 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd hL (LFunction_ne_zero_of_one_le_re χ (.inr hne1) h.ge)`. Establish `hz : riemannZeta ρ = 0`.

Establish `e : LFunction χ ρ = riemannZeta ρ` using `congrFun LFunction_modOne_eq ρ`. Rewrite using `[← e]`. Conclude with `hL`. Establish `key` using `hQ₂ Qn (le_trans (le_max_right _ _) (le_max_left _ _)) ρ hre hrelt hbig him' hz`. Establish `: Subsingleton (ZMod (0 + 1))` using `ZMod.subsingleton_iff.2 rfl`.

Establish `hχ : ∀ a : ZMod (0 + 1), χ a = 1` using `fun a => by`. Rewrite using `[Subsingleton.elim a 1, MulChar.map_one]`. Use `show (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * χ (n : ZMod (0 + 1)) * (n : ℂ) ^ (-ρ)‖`. Simplify using `only [hχ]`. Conclude with `key`.

Conclude with `hQ₁ Qn (le_trans (le_max_left _ _) (le_max_left _ _)) (N + 1) χ (ne_one_of_primitive hN hprim) hlevN ρ hre him' hL`. Rewrite using `[← Finset.coe_image, Set.ncard_coe_finset]`. Use `set f : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) := fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hf`. Establish `: Nonempty (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)` using `⟨⟨0, 1, 0⟩⟩`. Establish `hcount : ∀ U ⊆ T, (∀ p ∈ U, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) → (∀ p ∈ U, ∀ p' ∈ U, ⌊p.2.2.im⌋ % 2 = ⌊p'.2.2.im⌋ % 2) → ((U.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8)`.

Introduce `U hU hns hpar`. Take `⟨R, hRU, hcard, hinj⟩` from `exists_subset_injOn_card_image U f`. Rewrite using `[hcard]`. Use `hsp Qn hQn2 R ?_ ?_` and prove the remaining obligations. Introduce `p hp`.

Conclude with `hA p (hU (hRU hp)) (hns p (hRU hp))`. Introduce `N χ ρ ρ' h1 h2 hne`. Distinguish the cases in `hfl : ⌊ρ.im⌋ = ⌊ρ'.im⌋`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises.

Establish `e` using `hinj _ h1 _ h2 (by show (⟨N, χ, ⌊ρ.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) = ⟨N, χ, ⌊ρ'.im⌋⟩`. Rewrite using `[hfl])`. Conclude with `congrArg (fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => p.2.2) e`. Conclude with `one_le_abs_sub_of_floor hfl (hpar _ (hRU h1) _ (hRU h2))`. Use `set Ts := T.filter (fun p => p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) with hTs`.

Use `set Tb := T.filter (fun p => ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) with hTb`. Use `set T0 := Tb.filter (fun p => ⌊p.2.2.im⌋ % 2 = 0) with hT0`. Use `set T1 := Tb.filter (fun p => ¬ ⌊p.2.2.im⌋ % 2 = 0) with hT1`. Establish `hsub : T.image f ⊆ Ts.image f ∪ (T0.image f ∪ T1.image f)`. Introduce `c hc`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hc`. Distinguish the cases in `h1 : p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)`. Conclude with `Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hp, h1⟩))`. Distinguish the cases in `h2 : ⌊p.2.2.im⌋ % 2 = 0`. Conclude with `Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))`.

Conclude with `Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))`. Establish `hb0 : ((T0.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8)` using `hcount T0 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1) (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2) (fun p hp p' hp' => by rw [(Finset.mem_filter.1 hp).2, (Finset.mem_filter.1 hp').2])`. Establish `hb1 : ((T1.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8)` using `hcount T1 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1) (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2) (fun p hp p' hp' => by`. Establish `e1` using `(Finset.mem_filter.1 hp).2`. Establish `e2` using `(Finset.mem_filter.1 hp').2`.

Use the proof step `omega)`. Use `set M : ℕ := ⌈(Qn : ℝ) ^ ((1 : ℝ) / 20)⌉₊ with hM`. Establish `: Subsingleton (DirichletCharacter ℂ (0 + 1))` using `(inferInstance : Subsingleton (DirichletCharacter ℂ 1))`. Establish `hsmallsub : Ts.image f ⊆ (Finset.range (2 * M + 1)).image (fun k : ℕ => (⟨0, 1, (k : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ))`. Introduce `c hc`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hc`. Take `⟨N, χ, ρ⟩` from `p`. Take `⟨-, hN0, hlt⟩` from `Finset.mem_filter.1 hp`. Establish `hN : N = 0` using `hN0`. Substitute `hN` using the available equality.

Establish `hlt' : |ρ.im| < (M : ℝ)` using `lt_of_lt_of_le hlt (Nat.le_ceil _)`. Establish `hfl1 : (⌊ρ.im⌋ : ℝ) ≤ ρ.im` using `Int.floor_le _`. Establish `hfl2 : ρ.im < ⌊ρ.im⌋ + 1` using `Int.lt_floor_add_one _`. Establish `ha` using `abs_lt.1 hlt'`. Establish `hA1 : ⌊ρ.im⌋ < (M : ℤ)`.

Establish `: (⌊ρ.im⌋ : ℝ) < ((M : ℤ) : ℝ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `hA2 : -(M : ℤ) < ⌊ρ.im⌋ + 1`. Establish `: ((-(M : ℤ) : ℤ) : ℝ) < ((⌊ρ.im⌋ + 1 : ℤ) : ℝ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions.

Establish `ht : (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) = ⌊ρ.im⌋ + M` using `Int.toNat_of_nonneg (by omega)`. Use `Finset.mem_image.2 ⟨(⌊ρ.im⌋ + M).toNat, Finset.mem_range.2 (by omega), ?_⟩` and prove the remaining obligations. Establish `hχ : χ = 1` using `Subsingleton.elim _ _`. Substitute `hχ` using the available equality. Use `show (⟨0, 1, (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) = ⟨0, 1, ⌊ρ.im⌋⟩`.

Rewrite using `[ht, add_sub_cancel_right]`. Establish `hsmallcard : ((Ts.image f).card : ℝ) ≤ 2 * (M : ℝ) + 1`. Establish `h` using `(Finset.card_le_card hsmallsub).trans Finset.card_image_le`. Rewrite `h` using `[Finset.card_range]`. Conclude with `h` after adjusting the coercions.

Establish `hcard : ((T.image f).card : ℝ) ≤ (Ts.image f).card + ((T0.image f).card + (T1.image f).card)`. Establish `h` using `(Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (add_le_add (le_refl _) (Finset.card_union_le _ _)))`. Conclude with `h` after adjusting the coercions. Establish `hM1 : (M : ℝ) < (Qn : ℝ) ^ ((1 : ℝ) / 20) + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `he1 : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8)` using `Real.rpow_le_rpow_of_exponent_le hQn1 (by norm_num)`.

Establish `he2 : (1 : ℝ) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8)` using `Real.one_le_rpow hQn1 (by norm_num)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ncard_cells_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((((fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => (⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) '' (T : Set (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))).ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 8) := by
  classical
  obtain ⟨Q₁, hQ₁⟩ := GlobalTheory.ZeroDetect.zero_detect
  obtain ⟨Q₂, hQ₂⟩ := GlobalTheory.ZeroDetect.zeta_zero_detect
  obtain ⟨C₁, hC₁, hsp⟩ := GlobalTheory.SpacedDetected.card_spaced_detected_le
  refine ⟨(2 * C₁ + 5) * ((Q₁ + Q₂ + 2 : ℕ) : ℝ), by positivity, ?_⟩
  intro Q hQ T hT
  set Qn : ℕ := max (max Q₁ Q₂) ⌈Q⌉₊ with hQn_def
  have hceil3 : 2 < ⌈Q⌉₊ := Nat.lt_ceil.2 (by push_cast; linarith)
  have hQn2 : 2 ≤ Qn := le_trans (by omega : 2 ≤ ⌈Q⌉₊) (le_max_right _ _)
  have hQle : Q ≤ (Qn : ℝ) := (Nat.le_ceil Q).trans (by exact_mod_cast le_max_right _ _)
  have hQn1 : (1 : ℝ) ≤ Qn := by exact_mod_cast (by omega : 1 ≤ Qn)
  have hQnpos : (0 : ℝ) < Qn := by linarith
  have hQnle : (Qn : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q := by
    have h1 : Qn ≤ Q₁ + Q₂ + ⌈Q⌉₊ := max_le (max_le (by omega) (by omega)) (by omega)
    have h2 : (⌈Q⌉₊ : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
    have h1' : (Qn : ℝ) ≤ Q₁ + Q₂ + ⌈Q⌉₊ := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ Q₁ := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ Q₂ := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hpow : (Qn : ℝ) ^ ((1 : ℝ) / 8) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by
    have hB : (1 : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q₁ + Q₂ + 2)
    calc (Qn : ℝ) ^ ((1 : ℝ) / 8) ≤ (((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q) ^ ((1 : ℝ) / 8) :=
          Real.rpow_le_rpow hQnpos.le hQnle (by norm_num)
      _ = ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) :=
          Real.mul_rpow (by positivity) (by linarith)
      _ ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by
          gcongr
          calc ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
            _ = _ := Real.rpow_one _
  have hA : ∀ p ∈ T, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) →
      p.1 + 1 ≤ Qn ∧ p.2.1.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ p.2.2.re ≤ 1 ∧
        |p.2.2.im| ≤ Qn ∧ (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
            p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2)‖ := by
    rintro ⟨N, χ, ρ⟩ hp hns
    obtain ⟨hlev, hprim, hL, hre, him⟩ : ((N + 1 : ℕ) : ℝ) ≤ Q ∧ χ.IsPrimitive ∧
        LFunction χ ρ = 0 ∧ 1 - 1 / 400 ≤ ρ.re ∧ |ρ.im| ≤ Q := hT _ hp
    have hlevN : N + 1 ≤ Qn := by
      have : ((N + 1 : ℕ) : ℝ) ≤ (Qn : ℝ) := hlev.trans hQle
      exact_mod_cast this
    have him' : |ρ.im| ≤ (Qn : ℝ) := him.trans hQle
    have hre1 : ρ.re ≤ 1 := by
      by_contra hgt
      rw [not_le] at hgt
      have hne : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hgt
        exact lt_irrefl _ hgt
      exact LFunction_ne_zero_of_one_le_re χ (.inr hne) hgt.le hL
    refine ⟨hlevN, hprim, hre, hre1, him', ?_⟩
    by_cases hN : N = 0
    · subst hN
      have hpos : 0 < (Qn : ℝ) ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hQnpos _
      have hbig : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ |ρ.im| := by
        by_contra h
        rw [not_le] at h
        exact hns ⟨rfl, h⟩
      have hne1 : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_im, abs_zero] at hbig
        linarith
      have hrelt : ρ.re < 1 := by
        rcases lt_or_eq_of_le hre1 with h | h
        · exact h
        · exact absurd hL (LFunction_ne_zero_of_one_le_re χ (.inr hne1) h.ge)
      have hz : riemannZeta ρ = 0 := by
        have e : LFunction χ ρ = riemannZeta ρ := congrFun LFunction_modOne_eq ρ
        rw [← e]
        exact hL
      have key := hQ₂ Qn (le_trans (le_max_right _ _) (le_max_left _ _)) ρ hre hrelt hbig him' hz
      have : Subsingleton (ZMod (0 + 1)) := ZMod.subsingleton_iff.2 rfl
      have hχ : ∀ a : ZMod (0 + 1), χ a = 1 := fun a => by
        rw [Subsingleton.elim a 1, MulChar.map_one]
      show (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
            χ (n : ZMod (0 + 1)) * (n : ℂ) ^ (-ρ)‖
      simp only [hχ]
      exact key
    · exact hQ₁ Qn (le_trans (le_max_left _ _) (le_max_left _ _)) (N + 1) χ
        (ne_one_of_primitive hN hprim) hlevN ρ hre him' hL
  rw [← Finset.coe_image, Set.ncard_coe_finset]
  set f : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) :=
    fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hf
  have : Nonempty (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) := ⟨⟨0, 1, 0⟩⟩
  have hcount : ∀ U ⊆ T, (∀ p ∈ U, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) →
      (∀ p ∈ U, ∀ p' ∈ U, ⌊p.2.2.im⌋ % 2 = ⌊p'.2.2.im⌋ % 2) →
      ((U.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) := by
    intro U hU hns hpar
    obtain ⟨R, hRU, hcard, hinj⟩ := exists_subset_injOn_card_image U f
    rw [hcard]
    refine hsp Qn hQn2 R ?_ ?_
    · intro p hp
      exact hA p (hU (hRU hp)) (hns p (hRU hp))
    · intro N χ ρ ρ' h1 h2 hne
      by_cases hfl : ⌊ρ.im⌋ = ⌊ρ'.im⌋
      · exfalso
        apply hne
        have e := hinj _ h1 _ h2 (by
          show (⟨N, χ, ⌊ρ.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) = ⟨N, χ, ⌊ρ'.im⌋⟩
          rw [hfl])
        exact congrArg (fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => p.2.2) e
      · exact one_le_abs_sub_of_floor hfl (hpar _ (hRU h1) _ (hRU h2))
  set Ts := T.filter (fun p => p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) with hTs
  set Tb := T.filter (fun p => ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) with hTb
  set T0 := Tb.filter (fun p => ⌊p.2.2.im⌋ % 2 = 0) with hT0
  set T1 := Tb.filter (fun p => ¬ ⌊p.2.2.im⌋ % 2 = 0) with hT1
  have hsub : T.image f ⊆ Ts.image f ∪ (T0.image f ∪ T1.image f) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    by_cases h1 : p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hp, h1⟩))
    · by_cases h2 : ⌊p.2.2.im⌋ % 2 = 0
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f
          (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem f
          (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))
  have hb0 : ((T0.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    hcount T0 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2)
      (fun p hp p' hp' => by rw [(Finset.mem_filter.1 hp).2, (Finset.mem_filter.1 hp').2])
  have hb1 : ((T1.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    hcount T1 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2)
      (fun p hp p' hp' => by
        have e1 := (Finset.mem_filter.1 hp).2
        have e2 := (Finset.mem_filter.1 hp').2
        omega)
  set M : ℕ := ⌈(Qn : ℝ) ^ ((1 : ℝ) / 20)⌉₊ with hM
  have : Subsingleton (DirichletCharacter ℂ (0 + 1)) :=
    (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
  have hsmallsub : Ts.image f ⊆ (Finset.range (2 * M + 1)).image
      (fun k : ℕ => (⟨0, 1, (k : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨N, χ, ρ⟩ := p
    obtain ⟨-, hN0, hlt⟩ := Finset.mem_filter.1 hp
    have hN : N = 0 := hN0
    subst hN
    have hlt' : |ρ.im| < (M : ℝ) := lt_of_lt_of_le hlt (Nat.le_ceil _)
    have hfl1 : (⌊ρ.im⌋ : ℝ) ≤ ρ.im := Int.floor_le _
    have hfl2 : ρ.im < ⌊ρ.im⌋ + 1 := Int.lt_floor_add_one _
    have ha := abs_lt.1 hlt'
    have hA1 : ⌊ρ.im⌋ < (M : ℤ) := by
      have : (⌊ρ.im⌋ : ℝ) < ((M : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hA2 : -(M : ℤ) < ⌊ρ.im⌋ + 1 := by
      have : ((-(M : ℤ) : ℤ) : ℝ) < ((⌊ρ.im⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have ht : (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) = ⌊ρ.im⌋ + M := Int.toNat_of_nonneg (by omega)
    refine Finset.mem_image.2 ⟨(⌊ρ.im⌋ + M).toNat, Finset.mem_range.2 (by omega), ?_⟩
    have hχ : χ = 1 := Subsingleton.elim _ _
    subst hχ
    show (⟨0, 1, (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) =
      ⟨0, 1, ⌊ρ.im⌋⟩
    rw [ht, add_sub_cancel_right]
  have hsmallcard : ((Ts.image f).card : ℝ) ≤ 2 * (M : ℝ) + 1 := by
    have h := (Finset.card_le_card hsmallsub).trans Finset.card_image_le
    rw [Finset.card_range] at h
    exact_mod_cast h
  have hcard : ((T.image f).card : ℝ) ≤
      (Ts.image f).card + ((T0.image f).card + (T1.image f).card) := by
    have h := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (add_le_add (le_refl _) (Finset.card_union_le _ _)))
    exact_mod_cast h
  have hM1 : (M : ℝ) < (Qn : ℝ) ^ ((1 : ℝ) / 20) + 1 := Nat.ceil_lt_add_one (by positivity)
  have he1 : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hQn1 (by norm_num)
  have he2 : (1 : ℝ) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hQn1 (by norm_num)
  calc ((T.image f).card : ℝ) ≤ (2 * C₁ + 5) * (Qn : ℝ) ^ ((1 : ℝ) / 8) := by linarith
    _ ≤ (2 * C₁ + 5) * (((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
    _ = (2 * C₁ + 5) * ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by ring

end GlobalTheory.ZeroCells
