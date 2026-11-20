import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

/- English proof (translation)
Establish `hmaps : ∀ p ∈ (Finset.univ : Finset (H × K)), (p.1 : G) * w * p.2 ∈ Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k`. Introduce `p _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨p.1, p.1.2, p.2, p.2.2, rfl⟩`. Establish `hcard` using `Finset.card_eq_sum_card_fiberwise (f := fun p : H × K => (p.1 : G) * w * p.2) (s := Finset.univ) hmaps`.

Establish `hfib : ∀ y ∈ (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k), ((Finset.univ : Finset (H × K)).filter fun p => (p.1 : G) * w * p.2 = y).card = (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card`. Introduce `y hy`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hy`. Take `⟨h0, hh0, k0, hk0, rfl⟩` from `hy`. Use `symm`.

Use `Finset.card_bij' (fun t ht => ((⟨h0 * t, H.mul_mem hh0 (Finset.mem_filter.1 ht).2.1⟩ : H), (⟨w⁻¹ * t⁻¹ * w * k0, by` and prove the remaining obligations. Establish `hinv` using `K.inv_mem (Finset.mem_filter.1 ht).2.2`. Rewrite `hinv` using `[show (w⁻¹ * t * w)⁻¹ = w⁻¹ * t⁻¹ * w by group]`. Conclude with `K.mul_mem hinv hk0⟩ : K)))`. Use the proof step `(fun p _ => h0⁻¹ * (p.1 : G)) ?_ ?_ ?_ ?_`.

Introduce `t _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use `group`. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`.

Establish `e : (p.1 : G) = h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹`. Rewrite using `[← hp]`. Use `group`. Use `⟨H.mul_mem (H.inv_mem hh0) p.1.2, ?_⟩` and prove the remaining obligations. Rewrite using `[e, show w⁻¹ * (h0⁻¹ * (h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹)) * w = k0 * (p.2 : G)⁻¹ by group]`.

Conclude with `K.mul_mem hk0 (K.inv_mem p.2.2)`. Introduce `t _ group`. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Establish `e : (p.2 : G) = w⁻¹ * (p.1 : G)⁻¹ * (h0 * w * k0)`.

Rewrite using `[← hp]`. Use `group`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `only`.

Rewrite using `[e]`. Use `group`. Rewrite `hcard` using `[Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Fintype.card_prod, ← Finset.card_univ, hcard]`.
-/
theorem card_doubleCoset_mul_card_inter {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w : G) :
    (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k).card *
      (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card = Nat.card H * Nat.card K := by
  have hmaps : ∀ p ∈ (Finset.univ : Finset (H × K)),
      (p.1 : G) * w * p.2 ∈ Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k := by
    intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun p : H × K => (p.1 : G) * w * p.2) (s := Finset.univ) hmaps
  have hfib : ∀ y ∈ (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k),
      ((Finset.univ : Finset (H × K)).filter fun p => (p.1 : G) * w * p.2 = y).card =
        (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨h0, hh0, k0, hk0, rfl⟩ := hy
    symm
    refine Finset.card_bij'
      (fun t ht => ((⟨h0 * t, H.mul_mem hh0 (Finset.mem_filter.1 ht).2.1⟩ : H),
        (⟨w⁻¹ * t⁻¹ * w * k0, by
          have hinv := K.inv_mem (Finset.mem_filter.1 ht).2.2
          rw [show (w⁻¹ * t * w)⁻¹ = w⁻¹ * t⁻¹ * w by group] at hinv
          exact K.mul_mem hinv hk0⟩ : K)))
      (fun p _ => h0⁻¹ * (p.1 : G)) ?_ ?_ ?_ ?_
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have e : (p.1 : G) = h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹ := by
        rw [← hp]; group
      refine ⟨H.mul_mem (H.inv_mem hh0) p.1.2, ?_⟩
      rw [e, show w⁻¹ * (h0⁻¹ * (h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹)) * w = k0 * (p.2 : G)⁻¹ by group]
      exact K.mul_mem hk0 (K.inv_mem p.2.2)
    · intro t _
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have e : (p.2 : G) = w⁻¹ * (p.1 : G)⁻¹ * (h0 * w * k0) := by
        rw [← hp]; group
      ext
      · simp
      · simp only
        rw [e]
        group
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Fintype.card_prod, ← Finset.card_univ,
    hcard]

/- English proof (translation)
Use `(Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun x => ?_).symm` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`. Establish `e1 : (h * w * k)⁻¹ * (h * x * h⁻¹) * (h * w * k) = k⁻¹ * (w⁻¹ * x * w) * k` using `by group`. Simplify using `only [e1]`. Establish `eH : h * x * h⁻¹ ∈ H ↔ x ∈ H`.

Rewrite using `[H.mul_mem_cancel_right (H.inv_mem hh), H.mul_mem_cancel_left hh]`. Establish `eK : k⁻¹ * (w⁻¹ * x * w) * k ∈ K ↔ w⁻¹ * x * w ∈ K`. Rewrite using `[K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]`. Distinguish the cases in `hx : x ∈ H ∧ w⁻¹ * x * w ∈ K`. Establish `hc` using `hφ k⁻¹ (K.inv_mem hk) _ hx.2`.

Rewrite `hc` using `[inv_inv]`. Rewrite using `[if_pos hx, if_pos ⟨eH.2 hx.1, eK.2 hx.2⟩, hlam h hh x hx.1, hc]`. Rewrite using `[if_neg hx, if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hx ⟨eH.1 h1, eK.1 h2⟩`.
-/
private theorem sum_conj_double_coset_eq_of_invariant {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w h k : G)
    (hh : h ∈ H) (hk : k ∈ K) (lam φ : G → ℂ)
    (hlam : ∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x)
    (hφ : ∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) :
    (∑ x : G, if x ∈ H ∧ (h * w * k)⁻¹ * x * (h * w * k) ∈ K then
        lam x * φ ((h * w * k)⁻¹ * x * (h * w * k)) else 0) =
      ∑ x : G, if x ∈ H ∧ w⁻¹ * x * w ∈ K then lam x * φ (w⁻¹ * x * w) else 0 := by
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun x => ?_).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have e1 : (h * w * k)⁻¹ * (h * x * h⁻¹) * (h * w * k) = k⁻¹ * (w⁻¹ * x * w) * k := by group
  simp only [e1]
  have eH : h * x * h⁻¹ ∈ H ↔ x ∈ H := by
    rw [H.mul_mem_cancel_right (H.inv_mem hh), H.mul_mem_cancel_left hh]
  have eK : k⁻¹ * (w⁻¹ * x * w) * k ∈ K ↔ w⁻¹ * x * w ∈ K := by
    rw [K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]
  by_cases hx : x ∈ H ∧ w⁻¹ * x * w ∈ K
  · have hc := hφ k⁻¹ (K.inv_mem hk) _ hx.2
    rw [inv_inv] at hc
    rw [if_pos hx, if_pos ⟨eH.2 hx.1, eK.2 hx.2⟩, hlam h hh x hx.1, hc]
  · rw [if_neg hx, if_neg]
    rintro ⟨h1, h2⟩
    exact hx ⟨eH.1 h1, eK.1 h2⟩

/- English proof (translation)
Introduce `G _ _ H K ι R w hR lam φ hlam hφ`. Establish `hHpos : (Nat.card H : ℂ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Establish `hKpos : (Nat.card K : ℂ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Establish `h1 : ∀ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ * ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) = (Nat.card K : ℂ)⁻¹ * ∑ y : G, (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0)`. Introduce `x`.

Distinguish the cases in `hx : x ∈ H`. Rewrite using `[if_pos hx]`. Simplify using `only [Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y⁻¹ * x * y ∈ K`.

Rewrite using `[if_pos hy, if_pos ⟨hx, hy⟩]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hy, if_neg (fun hc => hy hc.2)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hx]`.

Rewrite using `[Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, Finset.sum_comm]`. Establish `h2 : ∀ y : G, (∑ x : G, (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0)) = ∑ i ∈ R, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0) else 0`. Introduce `y`. Take `⟨i, ⟨hi, h, hhH, k, hkK, rfl⟩, huniq⟩` from `hR y`. Rewrite using `[Finset.sum_eq_single_of_mem i hi]`.

Rewrite using `[if_pos ⟨h, hhH, k, hkK, rfl⟩]`. Conclude with `sum_conj_double_coset_eq_of_invariant H K (w i) h k hhH hkK lam φ hlam hφ`. Introduce `j hj hji`. Rewrite using `[if_neg]`. Introduce `hP`.

Conclude with `hji (huniq j ⟨hj, hP⟩)`. Rewrite using `[Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm]`. Establish `h3 : ∀ i ∈ R, (∑ y : G, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0) else 0) = ((Nat.card H : ℂ) * Nat.card K) * ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ * (∑ …`. Introduce `i _`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.

Establish `hc : ((Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w i * k).card : ℂ) * ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) = (Nat.card H : ℂ) * Nat.card K`. Conclude with `card_doubleCoset_mul_card_inter H K (w i)` after adjusting the coercions. Establish `hI : ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) ≠ 0`. Establish `hmem : (1 : G) ∈ Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K`. Simplify using `[H.one_mem, K.one_mem]`.

Conclude with `(Finset.card_pos.2 ⟨1, hmem⟩).ne'` after adjusting the coercions. Rewrite using `[← hc, mul_inv_cancel_right₀ hI]`. Rewrite using `[Finset.sum_congr rfl h3, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e1 : (Nat.card H : ℂ)⁻¹ * Nat.card H = 1` using `inv_mul_cancel₀ hHpos`.

Establish `e2 : (Nat.card K : ℂ)⁻¹ * Nat.card K = 1` using `inv_mul_cancel₀ hKpos`. Take the linear combination `((Nat.card K : ℂ)⁻¹ * Nat.card K * ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ * (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e1 + (((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : …`.
-/
theorem mackey_doubleCoset_pairing : ∀ (G : Type) [Group G] [Fintype G] (H K : Subgroup G) (ι : Type) (R : Finset ι) (w : ι → G), (∀ x : G, ∃! i, i ∈ R ∧ ∃ h ∈ H, ∃ k ∈ K, x = h * w i * k) → ∀ (lam φ : G → ℂ), (∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x) → (∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) → (Nat.card H : ℂ)⁻¹ * ∑ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ * ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) = ∑ i ∈ R, ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ * ∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0 := by
  intro G _ _ H K ι R w hR lam φ hlam hφ
  have hHpos : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hKpos : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : ∀ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ *
        ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) =
      (Nat.card K : ℂ)⁻¹ * ∑ y : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0) := by
    intro x
    by_cases hx : x ∈ H
    · rw [if_pos hx]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y⁻¹ * x * y ∈ K
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]; ring
      · rw [if_neg hy, if_neg (fun hc => hy hc.2)]; ring
    · simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ y : G, (∑ x : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0)) =
      ∑ i ∈ R, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0 := by
    intro y
    obtain ⟨i, ⟨hi, h, hhH, k, hkK, rfl⟩, huniq⟩ := hR y
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [if_pos ⟨h, hhH, k, hkK, rfl⟩]
      exact sum_conj_double_coset_eq_of_invariant H K (w i) h k hhH hkK lam φ hlam hφ
    · intro j hj hji
      rw [if_neg]
      intro hP
      exact hji (huniq j ⟨hj, hP⟩)
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm]
  have h3 : ∀ i ∈ R, (∑ y : G, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0) =
      ((Nat.card H : ℂ) * Nat.card K) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0) := by
    intro i _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w i * k).card : ℂ) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) =
          (Nat.card H : ℂ) * Nat.card K := by
      exact_mod_cast card_doubleCoset_mul_card_inter H K (w i)
    have hI : ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) ≠ 0 := by
      have hmem : (1 : G) ∈ Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K := by
        simp [H.one_mem, K.one_mem]
      exact_mod_cast (Finset.card_pos.2 ⟨1, hmem⟩).ne'
    rw [← hc, mul_inv_cancel_right₀ hI]
  rw [Finset.sum_congr rfl h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (Nat.card H : ℂ)⁻¹ * Nat.card H = 1 := inv_mul_cancel₀ hHpos
  have e2 : (Nat.card K : ℂ)⁻¹ * Nat.card K = 1 := inv_mul_cancel₀ hKpos
  linear_combination
    ((Nat.card K : ℂ)⁻¹ * Nat.card K *
      ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e1 +
    (((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e2

end GlobalTheory.GLm
