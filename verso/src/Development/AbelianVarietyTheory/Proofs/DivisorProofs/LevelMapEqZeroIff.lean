import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SUCong.LevKer

variable {A : Type} [CommRing A]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Apply `ih` to reduce the goal to its premises. Establish `h' : ϖ * (ϖ ^ k * a - ϖ ^ k * b) = 0`.

Rewrite using `[mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]`. Conclude with `sub_eq_zero.mp (hϖ _ h')`.
-/
theorem pow_cancel (ϖ : A) (hϖ : ∀ a : A, ϖ * a = 0 → a = 0) (k : ℕ) (a b : A)
    (h : ϖ ^ k * a = ϖ ^ k * b) : a = b := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have h' : ϖ * (ϖ ^ k * a - ϖ ^ k * b) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
    exact sub_eq_zero.mp (hϖ _ h')

/- English proof (translation)
Establish `e : {x : S | (x : A) = ϖ} = {(⟨ϖ, hϖ⟩ : S)}`. Use extensionality with `x`. Simplify using `[Subtype.ext_iff]`. Unfold `piIdeal`. Rewrite using `[e, Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨a, a.2, by rw [← ha, Subring.coe_mul, mul_comm]⟩`. Introduce and unpack `⟨t, ht, e'⟩`. Conclude with `⟨⟨t, ht⟩, Subtype.ext (by rw [Subring.coe_mul, e', mul_comm])⟩`.
-/
theorem mem_piIdeal_iff (S : Subring A) (ϖ : A) (hϖ : ϖ ∈ S) (s : S) :
    s ∈ piIdeal S ϖ ↔ ∃ t ∈ S, (s : A) = ϖ * t := by
  have e : {x : S | (x : A) = ϖ} = {(⟨ϖ, hϖ⟩ : S)} := by
    ext x; simp [Subtype.ext_iff]
  unfold piIdeal
  rw [e, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, a.2, by rw [← ha, Subring.coe_mul, mul_comm]⟩
  · rintro ⟨t, ht, e'⟩
    exact ⟨⟨t, ht⟩, Subtype.ext (by rw [Subring.coe_mul, e', mul_comm])⟩

/- English proof (translation)
Unfold `red`. Rewrite using `[dif_pos hs, Ideal.Quotient.eq_zero_iff_mem, mem_piIdeal_iff S ϖ hϖ]`.
-/
theorem red_eq_zero_iff (S : Subring A) (ϖ : A) (hϖ : ϖ ∈ S) (s : A) (hs : s ∈ S) :
    red S ϖ s = 0 ↔ ∃ t ∈ S, s = ϖ * t := by
  unfold red
  rw [dif_pos hs, Ideal.Quotient.eq_zero_iff_mem, mem_piIdeal_iff S ϖ hϖ]

end GlobalTheory.SUCong.LevKer

namespace GlobalTheory.SUCong

/- English proof (translation)
Introduce `A _ n _ _ S σ H ϖ q k hR g hg`. Establish `hϖS : ϖ ∈ S` using `hR.2.2.1`. Establish `hnzd : ∀ a : A, ϖ * a = 0 → a = 0` using `hR.2.2.2.2.1`. Take `⟨h1, h2, h3, h4, h5⟩` from `hg`. Establish `key : ∀ i j, (levMap S ϖ k (g : Matrix n n A) i j = 0 ↔ InPow S ϖ (k + 1) (((g : Matrix n n A) - 1) i j))`.

Introduce `i j`. Establish `hk` using `h5 i j`. Establish `hs` using `(Classical.choose_spec hk).1`. Establish `he` using `(Classical.choose_spec hk).2`. Simplify using `only [levMap, dif_pos hk]`.

Rewrite using `[LevKer.red_eq_zero_iff S ϖ hϖS _ hs]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, et⟩`. Conclude with `⟨t, ht, by rw [he, et, pow_succ, mul_assoc]⟩`. Introduce and unpack `⟨t, ht, et⟩`.

Use `⟨t, ht, LevKer.pow_cancel ϖ hnzd k _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[← he, et, pow_succ, mul_assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Use `⟨h1, h2, h3, h4, fun i j => (key i j).1 ?_⟩` and prove the remaining obligations.

Rewrite using `[h0]`. Both sides reduce to the same expression. Introduce and unpack `⟨-, -, -, -, h6⟩`. Use extensionality with `i j`. Conclude with `(key i j).2 (h6 i j)`.
-/
theorem levMap_eq_zero_iff_mem_succ : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ), GoodRing S σ ϖ q → ∀ (g : GL n A), g ∈ congSU S σ H ϖ k → (levMap S ϖ k (g : Matrix n n A) = 0 ↔ g ∈ congSU S σ H ϖ (k + 1)) := by
  intro A _ n _ _ S σ H ϖ q k hR g hg
  have hϖS : ϖ ∈ S := hR.2.2.1
  have hnzd : ∀ a : A, ϖ * a = 0 → a = 0 := hR.2.2.2.2.1
  obtain ⟨h1, h2, h3, h4, h5⟩ := hg
  have key : ∀ i j, (levMap S ϖ k (g : Matrix n n A) i j = 0 ↔
      InPow S ϖ (k + 1) (((g : Matrix n n A) - 1) i j)) := by
    intro i j
    have hk := h5 i j
    have hs := (Classical.choose_spec hk).1
    have he := (Classical.choose_spec hk).2
    simp only [levMap, dif_pos hk]
    rw [LevKer.red_eq_zero_iff S ϖ hϖS _ hs]
    constructor
    · rintro ⟨t, ht, et⟩
      exact ⟨t, ht, by rw [he, et, pow_succ, mul_assoc]⟩
    · rintro ⟨t, ht, et⟩
      refine ⟨t, ht, LevKer.pow_cancel ϖ hnzd k _ _ ?_⟩
      rw [← he, et, pow_succ, mul_assoc]
  constructor
  · intro h0
    refine ⟨h1, h2, h3, h4, fun i j => (key i j).1 ?_⟩
    rw [h0]; rfl
  · rintro ⟨-, -, -, -, h6⟩
    ext i j
    exact (key i j).2 (h6 i j)

end GlobalTheory.SUCong
