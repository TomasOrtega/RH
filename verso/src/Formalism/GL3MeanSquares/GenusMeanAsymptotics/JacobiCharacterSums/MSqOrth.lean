import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

/- English proof (translation)
Rewrite using `[jacobiSym.mod_left (a : ℤ), jacobiSym.mod_left (b : ℤ)]`. Establish `h' : a % s = b % s` using `h`. Rewrite using `[← Int.natCast_mod, ← Int.natCast_mod, h']`.
-/
theorem jacobi_congr {a b s : ℕ} (h : a ≡ b [MOD s]) : jacobiSym (a : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [jacobiSym.mod_left (a : ℤ), jacobiSym.mod_left (b : ℤ)]
  have h' : a % s = b % s := h
  rw [← Int.natCast_mod, ← Int.natCast_mod, h']

/- English proof (translation)
Establish `hinj : ∀ x ∈ S, ∀ y ∈ S, (c * x) % M = (c * y) % M → x = y`. Introduce `x hx y hy hxy`. Establish `h1 : c * x ≡ c * y [MOD M]` using `hxy`. Establish `h2 : x ≡ y [MOD M]` using `Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hc) h1`. Establish `h3 : x % M = y % M` using `h2`.

Rewrite `h3` using `[Nat.mod_eq_of_lt (hS x hx), Nat.mod_eq_of_lt (hS y hy)]`. Then use the resulting hypothesis. Establish `himg : S.image (fun b => (c * b) % M) = S'`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `y hy`. Take `⟨b, hb, rfl⟩` from `Finset.mem_image.mp hy`.

Conclude with `hmap b hb`. Rewrite using `[Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]`. Conclude with `hcard`. Rewrite using `[← himg, Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)]`.
-/
theorem sum_perm {R : Type*} [AddCommMonoid R] (M c : ℕ) (hc : c.Coprime M) (S S' : Finset ℕ)
    (hS : ∀ b ∈ S, b < M) (hmap : ∀ b ∈ S, (c * b) % M ∈ S') (hcard : S'.card ≤ S.card) (f : ℕ → R) :
    ∑ b ∈ S', f b = ∑ b ∈ S, f ((c * b) % M) := by
  have hinj : ∀ x ∈ S, ∀ y ∈ S, (c * x) % M = (c * y) % M → x = y := by
    intro x hx y hy hxy
    have h1 : c * x ≡ c * y [MOD M] := hxy
    have h2 : x ≡ y [MOD M] := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hc) h1
    have h3 : x % M = y % M := h2
    rwa [Nat.mod_eq_of_lt (hS x hx), Nat.mod_eq_of_lt (hS y hy)] at h3
  have himg : S.image (fun b => (c * b) % M) = S' := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hmap b hb
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
      exact hcard
  rw [← himg, Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)]

/- English proof (translation)
Take `⟨p, hp, hpt⟩` from `Nat.exists_prime_and_dvd (show t ≠ 1 by omega)`. Use `haveI := Fact.mk hp`. Take `⟨t', rfl⟩` from `hpt`. Establish `ht0 : t' ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h1`. Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `(Nat.not_even_iff_odd.mpr ht) (even_two_mul t')`. Establish `hpt' : ¬ p ∣ t'`.

Introduce and unpack `⟨k, rfl⟩`. Use `hsq p ⟨k, by ring⟩` as an intermediate fact. Conclude with `hp.one_lt.ne' (Nat.isUnit_iff.mp this)`. Establish `hcp : p.Coprime t'` using `(Nat.Prime.coprime_iff_not_dvd hp).mpr hpt'`. Establish `hpm : p.Coprime m` using `Nat.Coprime.coprime_dvd_left (Dvd.intro t' rfl) hc`.

Take `⟨a, ha⟩` from `FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)`. Take `⟨k, hk1, hk2⟩` from `Nat.chineseRemainder (Nat.Coprime.mul_right hcp hpm) a.val 1`. Use `⟨k, Nat.ModEq.of_mul_left t' hk2, ?_⟩` and prove the remaining obligations. Use `haveI : NeZero t' := ⟨ht0⟩`. Rewrite using `[jacobiSym.mul_right, jacobi_congr hk1, jacobi_congr (Nat.ModEq.of_mul_right m hk2), ← jacobiSym.legendreSym.to_jacobiSym p, (legendreSym.eq_neg_one_iff p).mpr (by simpa using ha)]`.

Simplify using the standard rewrite rules.
-/
theorem exists_jacobi_neg_one (m t : ℕ) (ht : Odd t) (hsq : Squarefree t) (h1 : 1 < t)
    (hc : t.Coprime m) : ∃ u : ℕ, u ≡ 1 [MOD m] ∧ jacobiSym (u : ℤ) t = -1 := by
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
  haveI := Fact.mk hp
  obtain ⟨t', rfl⟩ := hpt
  have ht0 : t' ≠ 0 := by
    rintro rfl
    simp at h1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr ht) (even_two_mul t')
  have hpt' : ¬ p ∣ t' := by
    rintro ⟨k, rfl⟩
    have := hsq p ⟨k, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hcp : p.Coprime t' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpt'
  have hpm : p.Coprime m := Nat.Coprime.coprime_dvd_left (Dvd.intro t' rfl) hc
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.mul_right hcp hpm) a.val 1
  refine ⟨k, Nat.ModEq.of_mul_left t' hk2, ?_⟩
  haveI : NeZero t' := ⟨ht0⟩
  rw [jacobiSym.mul_right, jacobi_congr hk1, jacobi_congr (Nat.ModEq.of_mul_right m hk2),
    ← jacobiSym.legendreSym.to_jacobiSym p, (legendreSym.eq_neg_one_iff p).mpr (by simpa using ha)]
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hnd`. Establish `hs1 : s₁ ≠ 0`. Introduce and unpack `rfl`. Conclude with `(Nat.not_even_iff_odd.mpr h1) ⟨0, rfl⟩`. Establish `hs2 : s₂ ≠ 0`.

Introduce and unpack `rfl`. Conclude with `(Nat.not_even_iff_odd.mpr h2) ⟨0, rfl⟩`. Establish `hgd : Nat.gcd s₁ s₂ ∣ s₁` using `Nat.gcd_dvd_left s₁ s₂`. Establish `hg0 : Nat.gcd s₁ s₂ ≠ 0` using `Nat.gcd_ne_zero_left hs1`. Establish `hga : Nat.gcd s₁ s₂ * (s₁ / Nat.gcd s₁ s₂) = s₁` using `Nat.mul_div_cancel' hgd`.

Establish `hgb : Nat.gcd s₁ s₂ * (s₂ / Nat.gcd s₁ s₂) = s₂` using `Nat.mul_div_cancel' (Nat.gcd_dvd_right s₁ s₂)`. Use `set g := Nat.gcd s₁ s₂ with hg`. Use `set a := s₁ / g with ha`. Use `set b := s₂ / g with hb`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `h0`. Rewrite `hga` using `[h0, mul_zero]`. Conclude with `hs1 hga.symm`. Establish `ha1 : a ≠ 1`. Introduce and unpack `h0`.

Rewrite `hga` using `[h0, mul_one]`. Conclude with `hnd (hga ▸ Nat.gcd_dvd_right s₁ s₂)`. Establish `hadv : a ∣ s₁` using `Dvd.intro_left g hga`. Establish `hao : Odd a` using `Odd.of_dvd_nat h1 hadv`. Establish `haq : Squarefree a` using `Squarefree.squarefree_of_dvd hadv hq1`.

Establish `hag : a.Coprime g`. Use `hq1` as an intermediate fact. Rewrite `this` using `[← hga]`. Conclude with `(Nat.squarefree_mul_iff.mp this).1.symm`. Establish `hab : a.Coprime b` using `Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero hg0)`.

Establish `has2 : a.Coprime s₂`. Rewrite using `[← hgb]`. Conclude with `Nat.Coprime.mul_right hag hab`. Establish `ham : a.Coprime m₀` using `Nat.Coprime.coprime_dvd_left hadv hc1`. Take `⟨u, hu1, hJ⟩` from `exists_jacobi_neg_one (m₀ * s₂) a hao haq (lt_of_le_of_ne (Nat.pos_of_ne_zero ha0) (Ne.symm ha1)) (Nat.Coprime.mul_right ham has2)`.

Establish `hum : u ≡ 1 [MOD m₀]` using `Nat.ModEq.of_mul_right s₂ hu1`. Establish `hus : u ≡ 1 [MOD s₂]` using `Nat.ModEq.of_mul_left m₀ hu1`. Establish `hug : u ≡ 1 [MOD g]` using `Nat.ModEq.of_dvd (Nat.gcd_dvd_right s₁ s₂) hus`. Use `haveI : NeZero g := ⟨hg0⟩`. Use `haveI : NeZero a := ⟨ha0⟩`.

Establish `hJs : jacobiSym (u : ℤ) s₂ = 1`. Rewrite using `[jacobi_congr hus]`. Simplify using the standard rewrite rules. Establish `hJg : jacobiSym (u : ℤ) g = 1`. Rewrite using `[jacobi_congr hug]`.

Simplify using the standard rewrite rules. Establish `hJ1 : jacobiSym (u : ℤ) s₁ = -1`. Rewrite using `[← hga, jacobiSym.mul_right, hJg, hJ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hua : u.Coprime a`.

Assume the negation of the conclusion as `hn`. Establish `h0 : jacobiSym (u : ℤ) a = 0`. Rewrite using `[jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]`. Conclude with `hn`. Rewrite `hJ` using `[h0]`.

Evaluate the numerical expressions using `at hJ`. Establish `hus' : u.Coprime s₂`. Establish `e : Nat.gcd u s₂ = Nat.gcd 1 s₂` using `Nat.ModEq.gcd_eq hus`. Rewrite `e` using `[Nat.gcd_one_left]`. Conclude with `e`.

Establish `hug' : u.Coprime g` using `Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right s₁ s₂) hus'`. Establish `hus1 : u.Coprime s₁`. Rewrite using `[← hga]`. Conclude with `Nat.Coprime.mul_right hug' hua`. Use `h u hum (Nat.Coprime.mul_right hus1 hus')` as an intermediate fact.

Rewrite `this` using `[hJ1, hJs]`. Evaluate the numerical expressions using `at this`.
-/
private theorem dvd_of_jacobiSym_agree_on_residue_class (m₀ s₁ s₂ : ℕ) (h1 : Odd s₁) (h2 : Odd s₂)
    (hq1 : Squarefree s₁) (hc1 : s₁.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ ∣ s₂ := by
  by_contra hnd
  have hs1 : s₁ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h1) ⟨0, rfl⟩
  have hs2 : s₂ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h2) ⟨0, rfl⟩
  have hgd : Nat.gcd s₁ s₂ ∣ s₁ := Nat.gcd_dvd_left s₁ s₂
  have hg0 : Nat.gcd s₁ s₂ ≠ 0 := Nat.gcd_ne_zero_left hs1
  have hga : Nat.gcd s₁ s₂ * (s₁ / Nat.gcd s₁ s₂) = s₁ := Nat.mul_div_cancel' hgd
  have hgb : Nat.gcd s₁ s₂ * (s₂ / Nat.gcd s₁ s₂) = s₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right s₁ s₂)
  set g := Nat.gcd s₁ s₂ with hg
  set a := s₁ / g with ha
  set b := s₂ / g with hb
  have ha0 : a ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hga
    exact hs1 hga.symm
  have ha1 : a ≠ 1 := by
    rintro h0
    rw [h0, mul_one] at hga
    exact hnd (hga ▸ Nat.gcd_dvd_right s₁ s₂)
  have hadv : a ∣ s₁ := Dvd.intro_left g hga
  have hao : Odd a := Odd.of_dvd_nat h1 hadv
  have haq : Squarefree a := Squarefree.squarefree_of_dvd hadv hq1
  have hag : a.Coprime g := by
    have := hq1
    rw [← hga] at this
    exact (Nat.squarefree_mul_iff.mp this).1.symm
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero hg0)
  have has2 : a.Coprime s₂ := by
    rw [← hgb]
    exact Nat.Coprime.mul_right hag hab
  have ham : a.Coprime m₀ := Nat.Coprime.coprime_dvd_left hadv hc1
  obtain ⟨u, hu1, hJ⟩ := exists_jacobi_neg_one (m₀ * s₂) a hao haq
    (lt_of_le_of_ne (Nat.pos_of_ne_zero ha0) (Ne.symm ha1))
    (Nat.Coprime.mul_right ham has2)
  have hum : u ≡ 1 [MOD m₀] := Nat.ModEq.of_mul_right s₂ hu1
  have hus : u ≡ 1 [MOD s₂] := Nat.ModEq.of_mul_left m₀ hu1
  have hug : u ≡ 1 [MOD g] := Nat.ModEq.of_dvd (Nat.gcd_dvd_right s₁ s₂) hus
  haveI : NeZero g := ⟨hg0⟩
  haveI : NeZero a := ⟨ha0⟩
  have hJs : jacobiSym (u : ℤ) s₂ = 1 := by
    rw [jacobi_congr hus]
    simp
  have hJg : jacobiSym (u : ℤ) g = 1 := by
    rw [jacobi_congr hug]
    simp
  have hJ1 : jacobiSym (u : ℤ) s₁ = -1 := by
    rw [← hga, jacobiSym.mul_right, hJg, hJ]
    ring
  have hua : u.Coprime a := by
    by_contra hn
    have h0 : jacobiSym (u : ℤ) a = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hn
    rw [h0] at hJ
    norm_num at hJ
  have hus' : u.Coprime s₂ := by
    have e : Nat.gcd u s₂ = Nat.gcd 1 s₂ := Nat.ModEq.gcd_eq hus
    rw [Nat.gcd_one_left] at e
    exact e
  have hug' : u.Coprime g := Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right s₁ s₂) hus'
  have hus1 : u.Coprime s₁ := by
    rw [← hga]
    exact Nat.Coprime.mul_right hug' hua
  have := h u hum (Nat.Coprime.mul_right hus1 hus')
  rw [hJ1, hJs] at this
  norm_num at this

/- English proof (translation)
Apply `Nat.dvd_antisymm` to reduce the goal to its premises. Conclude with `dvd_of_jacobiSym_agree_on_residue_class m₀ s₁ s₂ h1 h2 hq1 hc1 h`. Conclude with `dvd_of_jacobiSym_agree_on_residue_class m₀ s₂ s₁ h2 h1 hq2 hc2 (fun u hu hc => (h u hu (by rwa [mul_comm])).symm)`.
-/
theorem jacobi_separate (m₀ s₁ s₂ : ℕ) (hm : 0 < m₀) (h1 : Odd s₁) (h2 : Odd s₂) (hq1 : Squarefree s₁)
    (hq2 : Squarefree s₂) (hc1 : s₁.Coprime m₀) (hc2 : s₂.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ = s₂ := by
  apply Nat.dvd_antisymm
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₁ s₂ h1 h2 hq1 hc1 h
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₂ s₁ h2 h1 hq2 hc2
      (fun u hu hc => (h u hu (by rwa [mul_comm])).symm)

/- English proof (translation)
Establish `hpos : 0 < s` using `Nat.pos_of_ne_zero hs`. Rewrite using `[Nat.totient_eq_card_coprime]`. Apply `Finset.card_bij (fun b _ => b % s)` to reduce the goal to its premises. Introduce `b hb`. Simplify using `only [mem_filter, mem_range] at hb ⊢`.

Use `⟨Nat.mod_lt _ hpos, ?_⟩` and prove the remaining obligations. Use `show Nat.gcd s (b % s) = 1`. Rewrite using `[Nat.gcd_comm, ← Nat.gcd_rec]`. Conclude with `hb.2.2.symm`. Introduce `b₁ hb₁ b₂ hb₂ h`.

Simplify using `only [mem_filter, mem_range] at hb₁ hb₂`. Establish `h1 : b₁ ≡ b₂ [MOD m₀]` using `hb₁.2.1.trans hb₂.2.1.symm`. Establish `h2 : b₁ ≡ b₂ [MOD s]` using `h`. Establish `h3` using `(Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩`. Establish `h4 : b₁ % (m₀ * s) = b₂ % (m₀ * s)` using `h3`.

Rewrite `h4` using `[Nat.mod_eq_of_lt hb₁.1, Nat.mod_eq_of_lt hb₂.1]`. Then use the resulting hypothesis. Introduce `r hr`. Simplify using `only [mem_filter, mem_range] at hr`. Take `⟨k, hk1, hk2⟩` from `Nat.chineseRemainder hcop a r`. Establish `hk1' : k % m₀ = a % m₀` using `hk1`.

Establish `hk2' : k % s = r % s` using `hk2`. Use `⟨k % (m₀ * s), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [mem_filter, mem_range]`. Use `⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hm hs)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.mod_mul_right_mod]`.

Conclude with `hk1'`. Use `show Nat.gcd _ s = 1`. Rewrite using `[Nat.gcd_comm, Nat.gcd_rec, Nat.mod_mul_left_mod, hk2', Nat.mod_eq_of_lt hr.1]`. Conclude with `hr.2.symm`. Use `show k % (m₀ * s) % s = r`.

Rewrite using `[Nat.mod_mul_left_mod, hk2', Nat.mod_eq_of_lt hr.1]`.
-/
theorem card_cls (m₀ s a : ℕ) (hcop : m₀.Coprime s) (hm : m₀ ≠ 0) (hs : s ≠ 0) :
    ((range (m₀ * s)).filter (fun b => b % m₀ = a % m₀ ∧ b.Coprime s)).card = s.totient := by
  have hpos : 0 < s := Nat.pos_of_ne_zero hs
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_bij (fun b _ => b % s)
  · intro b hb
    simp only [mem_filter, mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    show Nat.gcd s (b % s) = 1
    rw [Nat.gcd_comm, ← Nat.gcd_rec]
    exact hb.2.2.symm
  · intro b₁ hb₁ b₂ hb₂ h
    simp only [mem_filter, mem_range] at hb₁ hb₂
    have h1 : b₁ ≡ b₂ [MOD m₀] := hb₁.2.1.trans hb₂.2.1.symm
    have h2 : b₁ ≡ b₂ [MOD s] := h
    have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    have h4 : b₁ % (m₀ * s) = b₂ % (m₀ * s) := h3
    rwa [Nat.mod_eq_of_lt hb₁.1, Nat.mod_eq_of_lt hb₂.1] at h4
  · intro r hr
    simp only [mem_filter, mem_range] at hr
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop a r
    have hk1' : k % m₀ = a % m₀ := hk1
    have hk2' : k % s = r % s := hk2
    refine ⟨k % (m₀ * s), ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hm hs)), ?_, ?_⟩
      · rw [Nat.mod_mul_right_mod]
        exact hk1'
      · show Nat.gcd _ s = 1
        rw [Nat.gcd_comm, Nat.gcd_rec, Nat.mod_mul_left_mod, hk2', Nat.mod_eq_of_lt hr.1]
        exact hr.2.symm
    · show k % (m₀ * s) % s = r
      rw [Nat.mod_mul_left_mod, hk2', Nat.mod_eq_of_lt hr.1]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
