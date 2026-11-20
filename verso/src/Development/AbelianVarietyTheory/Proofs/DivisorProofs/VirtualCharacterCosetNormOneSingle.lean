import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzeroStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Use `letI S : Setoid ι := ⟨R, hR⟩`. Set `rep : Quotient S → ι` to `Quotient.out`. Establish `hrep : ∀ t : ι, R t (rep ⟦t⟧)` using `fun t => hR.symm (Quotient.mk_out t)`. Use `choose a ha hfa using fun t => hrel t _ (hrep t)`. Set `n : Quotient S → ℕ → ℤ` to `fun i b => ∑ t, if (⟦t⟧ : Quotient S) = i ∧ a t = b then c t else 0`.

Set `C : Quotient S → ℂ` to `fun i => ∑ b ∈ Finset.range l, (n i b : ℂ) * ζ ^ b`. Establish `hF : ∀ g, ∑ t, (c t : ℂ) * f t g = ∑ i, C i * f (rep i) g`. Introduce `g`. Establish `h1 : ∀ i, C i * f (rep i) g = ∑ t, if (⟦t⟧ : Quotient S) = i then (c t : ℂ) * (ζ ^ a t * f (rep i) g) else 0`. Introduce `i`.

Simplify using `only [C, n, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (⟦t⟧ : Quotient S) = i`. Simplify using `only [h, true_and, if_true]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_range, ha t, if_true]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `[hfa t g]`. Establish `hort : ∀ i j, i ≠ j → ∑ g, f (rep i) g * star (f (rep j) g) = 0`.

Introduce `i j hij`. Assume the negation of the conclusion as `h`. Apply `hij` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq i, ← Quotient.out_eq j]`. Conclude with `Quotient.sound (horth _ _ h)`.

Establish `hexp : ∀ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) = ∑ i, ∑ j, C i * star (C j) * (f (rep i) g * star (f (rep j) g))`. Introduce `g`. Rewrite using `[star_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul']`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∑ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) = (∑ i, C i * star (C i)) * Fintype.card G`. Repeatedly rewrite using `[hexp]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm, Finset.sum_eq_single i]`. Rewrite using `[← Finset.mul_sum, hnorm]`. Introduce `j _ hji`. Rewrite using `[← Finset.mul_sum, hort i j (Ne.symm hji), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Rewrite `hsum` using `[hF]`. Rewrite `hsum` using `[h2]`. Establish `h3 : ∑ i, C i * star (C i) = 1`.

Use `hsum` as an intermediate fact. Rewrite `this` using `[← one_mul (Fintype.card G : ℂ)]`. Conclude with `mul_right_cancel₀ hG (by simpa using this)`. Take `⟨i₀, -, hi₀⟩` from `GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero l ζ hl hζ (Quotient S) Finset.univ n h3`. Use `⟨rep i₀, C i₀, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[hF, Finset.sum_eq_single i₀]`. Introduce `i _ hi`. Establish `: C i = 0` using `hi₀ i (Finset.mem_univ i) hi`. Rewrite using `[this, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i₀) h`.
-/
theorem int_comb_unit_norm_single {ι G : Type} [Fintype ι] [Fintype G] (l : ℕ) (hl : l.Prime)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ l) (f : ι → G → ℂ) (c : ι → ℤ) (R : ι → ι → Prop)
    (hR : Equivalence R) (hG : (Fintype.card G : ℂ) ≠ 0)
    (hnorm : ∀ i, ∑ g, f i g * star (f i g) = Fintype.card G)
    (horth : ∀ i j, ∑ g, f i g * star (f j g) ≠ 0 → R i j)
    (hrel : ∀ i j, R i j → ∃ a < l, ∀ g, f i g = ζ ^ a * f j g)
    (hsum : ∑ g, (∑ i, (c i : ℂ) * f i g) * star (∑ i, (c i : ℂ) * f i g) = Fintype.card G) :
    ∃ i₀ e, ∀ g, ∑ i, (c i : ℂ) * f i g = e * f i₀ g := by
  letI S : Setoid ι := ⟨R, hR⟩
  let rep : Quotient S → ι := Quotient.out
  have hrep : ∀ t : ι, R t (rep ⟦t⟧) := fun t => hR.symm (Quotient.mk_out t)
  choose a ha hfa using fun t => hrel t _ (hrep t)
  let n : Quotient S → ℕ → ℤ := fun i b => ∑ t, if (⟦t⟧ : Quotient S) = i ∧ a t = b then c t else 0
  let C : Quotient S → ℂ := fun i => ∑ b ∈ Finset.range l, (n i b : ℂ) * ζ ^ b
  have hF : ∀ g, ∑ t, (c t : ℂ) * f t g = ∑ i, C i * f (rep i) g := by
    intro g
    have h1 : ∀ i, C i * f (rep i) g =
        ∑ t, if (⟦t⟧ : Quotient S) = i then (c t : ℂ) * (ζ ^ a t * f (rep i) g) else 0 := by
      intro i
      simp only [C, n, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : (⟦t⟧ : Quotient S) = i
      · simp only [h, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_range, ha t, if_true]
        ring
      · simp [h]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp [hfa t g]
  have hort : ∀ i j, i ≠ j → ∑ g, f (rep i) g * star (f (rep j) g) = 0 := by
    intro i j hij
    by_contra h
    apply hij
    rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound (horth _ _ h)
  have hexp : ∀ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      ∑ i, ∑ j, C i * star (C j) * (f (rep i) g * star (f (rep j) g)) := by
    intro g
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have h2 : ∑ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      (∑ i, C i * star (C i)) * Fintype.card G := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · rw [← Finset.mul_sum, hnorm]
    · intro j _ hji
      rw [← Finset.mul_sum, hort i j (Ne.symm hji), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hF] at hsum
  rw [h2] at hsum
  have h3 : ∑ i, C i * star (C i) = 1 := by
    have := hsum
    rw [← one_mul (Fintype.card G : ℂ)] at this
    exact mul_right_cancel₀ hG (by simpa using this)
  obtain ⟨i₀, -, hi₀⟩ := GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero l ζ hl hζ (Quotient S) Finset.univ n h3
  refine ⟨rep i₀, C i₀, fun g => ?_⟩
  rw [hF, Finset.sum_eq_single i₀]
  · intro i _ hi
    have : C i = 0 := hi₀ i (Finset.mem_univ i) hi
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i₀) h

end GlobalTheory.Shin

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `G Γ _ _ _ _ φ s hp hs X hX hXn`. Use `haveI : Fintype G := Fintype.ofFinite G`. Use `haveI : Finite (G ⋊[φ] Γ) := Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right)) (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))`. Take `⟨c, hirr, hXc, -⟩` from `GlobalTheory.BI.virt_expand (G ⋊[φ] Γ) X hX`. Set `T` to `c.support.filter (fun χ : G ⋊[φ] Γ → ℂ => ¬ ∀ δ, χ (inl δ * inr s) = 0)`.

Establish `hT : ∀ t : T, IsIrrChar ℂ ℂ t.1 ∧ ¬ ∀ δ, t.1 (inl δ * inr s) = 0` using `fun t => ⟨hirr _ (Finset.mem_filter.1 t.2).1, (Finset.mem_filter.1 t.2).2⟩`. Set `f : T → G → ℂ` to `fun t g => t.1 (inl g * inr s)`. Establish `hX' : ∀ g, X (inl g * inr s) = ∑ t : T, (c t.1 : ℂ) * f t g`. Introduce `g`. Rewrite using `[hXc, Finsupp.sum, Finset.sum_apply]`.

Simplify using `only [Pi.smul_apply, zsmul_eq_mul]`. Rewrite using `[Finset.sum_coe_sort T (fun χ => (c χ : ℂ) * χ (inl g * inr s))]`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun χ _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Rewrite using `[h g, mul_zero]`. Both sides reduce to the same expression. Set `R : T → T → Prop` to `fun t u => ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, t.1 x = u.1 x * (η x : ℂ)`. Establish `hR : Equivalence R`. Use `⟨fun t => ⟨1, fun g => rfl, fun x => by simp⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `t u ⟨η, h1, h2⟩`. Use `⟨η⁻¹, fun g => by simp [h1 g], fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[h2 x, MonoidHom.inv_apply, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]`. Introduce and unpack `t u v ⟨η, h1, h2⟩ ⟨η', h1', h2'⟩`. Use `⟨η' * η, fun g => by simp [h1 g, h1' g], fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[h2 x, h2' x, MonoidHom.mul_apply, Units.val_mul, mul_assoc]`. Use `haveI : NeZero (Nat.card Γ) := ⟨hp.ne_zero⟩`. Establish `hζ` using `Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero`. Establish `hnorm : ∀ t, ∑ g, f t g * star (f t g) = Fintype.card G`. Introduce `t`.

Break down `GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t.1 (hT t).1 with h | ⟨-, h⟩` into its components or cases. Conclude with `absurd h (hT t).2`. Rewrite `h` using `[finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]`. Conclude with `h`. Establish `horth : ∀ t u, ∑ g, f t g * star (f u g) ≠ 0 → R t u`.

Introduce `t u h`. Break down `GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist G Γ φ s hp hs t.1 u.1 (hT t).1 (hT u).1 with h' | h'` into its components or cases. Rewrite `h'` using `[finsum_eq_sum_of_fintype]`. Conclude with `absurd h' h`. Conclude with `h'`.

Establish `hrel : ∀ t u, R t u → ∃ a < Nat.card Γ, ∀ g, f t g = Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) ^ a * f u g`. Introduce and unpack `t u ⟨η, h1, h2⟩`. Establish `hpow : ((η (inr s) : ℂˣ) : ℂ) ^ Nat.card Γ = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one, Units.val_one]`. Take `⟨a, ha, hb⟩` from `hζ.eq_pow_of_pow_eq_one hpow`.

Use `⟨a, ha, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [f]`. Rewrite using `[h2, map_mul, h1, one_mul, hb, mul_comm]`. Establish `hsum : ∑ g, (∑ t : T, (c t.1 : ℂ) * f t g) * star (∑ t : T, (c t.1 : ℂ) * f t g) = Fintype.card G`. Rewrite `hXn` using `[finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]`.

Repeatedly rewrite using `[← hX']`. Conclude with `hXn`. Take `⟨t₀, e, he⟩` from `int_comb_unit_norm_single (Nat.card Γ) hp _ hζ f (fun t => c t.1) R hR (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hnorm horth hrel hsum`. Use `⟨t₀.1, e, (hT t₀).1, ?_, fun δ => by rw [hX', he]⟩` and prove the remaining obligations. Break down `GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t₀.1 (hT t₀).1 with h | ⟨h, -⟩` into its components or cases.

Conclude with `absurd h (hT t₀).2`. Conclude with `h`.
-/
theorem virt_coset_norm_one_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ),
    ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
    ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
      ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  intro G Γ _ _ _ _ φ s hp hs X hX hXn
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  obtain ⟨c, hirr, hXc, -⟩ := GlobalTheory.BI.virt_expand (G ⋊[φ] Γ) X hX
  let T := c.support.filter (fun χ : G ⋊[φ] Γ → ℂ => ¬ ∀ δ, χ (inl δ * inr s) = 0)
  have hT : ∀ t : T, IsIrrChar ℂ ℂ t.1 ∧ ¬ ∀ δ, t.1 (inl δ * inr s) = 0 := fun t =>
    ⟨hirr _ (Finset.mem_filter.1 t.2).1, (Finset.mem_filter.1 t.2).2⟩
  let f : T → G → ℂ := fun t g => t.1 (inl g * inr s)
  have hX' : ∀ g, X (inl g * inr s) = ∑ t : T, (c t.1 : ℂ) * f t g := by
    intro g
    rw [hXc, Finsupp.sum, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    rw [Finset.sum_coe_sort T (fun χ => (c χ : ℂ) * χ (inl g * inr s))]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rw [h g, mul_zero]
    · rfl
  let R : T → T → Prop := fun t u => ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧
    ∀ x, t.1 x = u.1 x * (η x : ℂ)
  have hR : Equivalence R := by
    refine ⟨fun t => ⟨1, fun g => rfl, fun x => by simp⟩, ?_, ?_⟩
    · rintro t u ⟨η, h1, h2⟩
      refine ⟨η⁻¹, fun g => by simp [h1 g], fun x => ?_⟩
      rw [h2 x, MonoidHom.inv_apply, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
    · rintro t u v ⟨η, h1, h2⟩ ⟨η', h1', h2'⟩
      refine ⟨η' * η, fun g => by simp [h1 g, h1' g], fun x => ?_⟩
      rw [h2 x, h2' x, MonoidHom.mul_apply, Units.val_mul, mul_assoc]
  haveI : NeZero (Nat.card Γ) := ⟨hp.ne_zero⟩
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  have hnorm : ∀ t, ∑ g, f t g * star (f t g) = Fintype.card G := by
    intro t
    rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t.1 (hT t).1 with h | ⟨-, h⟩
    · exact absurd h (hT t).2
    · rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at h
      exact h
  have horth : ∀ t u, ∑ g, f t g * star (f u g) ≠ 0 → R t u := by
    intro t u h
    rcases GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist G Γ φ s hp hs t.1 u.1 (hT t).1 (hT u).1 with h' | h'
    · rw [finsum_eq_sum_of_fintype] at h'
      exact absurd h' h
    · exact h'
  have hrel : ∀ t u, R t u → ∃ a < Nat.card Γ, ∀ g,
      f t g = Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) ^ a * f u g := by
    rintro t u ⟨η, h1, h2⟩
    have hpow : ((η (inr s) : ℂˣ) : ℂ) ^ Nat.card Γ = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one,
        Units.val_one]
    obtain ⟨a, ha, hb⟩ := hζ.eq_pow_of_pow_eq_one hpow
    refine ⟨a, ha, fun g => ?_⟩
    simp only [f]
    rw [h2, map_mul, h1, one_mul, hb, mul_comm]
  have hsum : ∑ g, (∑ t : T, (c t.1 : ℂ) * f t g) * star (∑ t : T, (c t.1 : ℂ) * f t g) =
      Fintype.card G := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at hXn
    simp_rw [← hX']
    exact hXn
  obtain ⟨t₀, e, he⟩ := int_comb_unit_norm_single (Nat.card Γ) hp _ hζ f (fun t => c t.1) R hR
    (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hnorm horth hrel hsum
  refine ⟨t₀.1, e, (hT t₀).1, ?_, fun δ => by rw [hX', he]⟩
  rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t₀.1 (hT t₀).1 with h | ⟨h, -⟩
  · exact absurd h (hT t₀).2
  · exact h

end GlobalTheory.Shin
