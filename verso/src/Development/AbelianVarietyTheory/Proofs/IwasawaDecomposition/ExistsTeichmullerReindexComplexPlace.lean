import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
open Polynomial

noncomputable section

namespace GlobalTheory.TeichAt

open Formalism.L2.NT GlobalTheory.ParRay

/- English proof (translation)
Establish `hpos` using `(isOfFinOrder_fbar hx).orderOf_pos`. Use `set n := orderOf x with hn`. Use `(Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg.out).2 ?_))` and prove the remaining obligations. Introduce `hdvd`. Establish `hm : g ^ n.factorization g * (n / g ^ n.factorization g) = n` using `Nat.ordProj_mul_ordCompl_eq_self n g`.

Establish `h1 : x ^ (g ^ n.factorization g * (n / g ^ n.factorization g)) = 1` using `by rw [hm, hn, pow_orderOf_eq_one]`. Establish `h2 : x ^ (n / g ^ n.factorization g) = 1` using `pow_eq_one_of_charP g x _ _ h1`. Establish `h3 : n ∣ n / g ^ n.factorization g` using `orderOf_dvd_of_pow_eq_one h2`. Conclude with `Nat.not_dvd_ordCompl hg.out hpos.ne' (hdvd.trans h3)`.
-/
theorem orderOf_coprime {g : ℕ} [hg : Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : (orderOf x).Coprime g := by
  have hpos := (isOfFinOrder_fbar hx).orderOf_pos
  set n := orderOf x with hn
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg.out).2 ?_))
  intro hdvd
  have hm : g ^ n.factorization g * (n / g ^ n.factorization g) = n := Nat.ordProj_mul_ordCompl_eq_self n g
  have h1 : x ^ (g ^ n.factorization g * (n / g ^ n.factorization g)) = 1 := by rw [hm, hn, pow_orderOf_eq_one]
  have h2 : x ^ (n / g ^ n.factorization g) = 1 := pow_eq_one_of_charP g x _ _ h1
  have h3 : n ∣ n / g ^ n.factorization g := orderOf_dvd_of_pow_eq_one h2
  exact Nat.not_dvd_ordCompl hg.out hpos.ne' (hdvd.trans h3)

/- English proof (translation)
Establish `h : t 0 * t 0 = t 0` using `by rw [← map_mul, mul_zero]`. Assume the negation of the conclusion as `h0`. Establish `h1 : t 0 = 1` using `(mul_eq_left₀ h0).1 h`. Take `⟨x, hx⟩` from `Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx`.

Apply `hx.2` to reduce the goal to its premises. Use `ht x 1 hx.1 one_ne_zero ?_` and prove the remaining obligations. Establish `: t x = t x * t 0` using `by rw [h1, mul_one]`. Rewrite using `[this, ← map_mul, mul_zero, h1, map_one]`.
-/
theorem map_zero_of_inj {Ω : Type} [Field Ω] {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra h0
  have h1 : t 0 = 1 := (mul_eq_left₀ h0).1 h
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  apply hx.2
  refine ht x 1 hx.1 one_ne_zero ?_
  have : t x = t x * t 0 := by rw [h1, mul_one]
  rw [this, ← map_mul, mul_zero, h1, map_one]

/- English proof (translation)
Introduce `g _ A κ t ht`. Use `set s := redHom A κ t with hs_def`. Establish `hs : ∀ x, s x = redThrough A κ (t x)` using `fun x => rfl`. Establish `ht0 : t 0 = 0` using `map_zero_of_inj t ht`. Establish `hs0 : s 0 = 0`.

Rewrite using `[hs, ht0]`. Unfold `redThrough`. Rewrite using `[dif_pos (zero_mem A)]`. Establish `: (⟨0, zero_mem A⟩ : A) = 0` using `rfl`. Rewrite using `[this, map_zero, map_zero]`.

Establish `hsne : ∀ x, x ≠ 0 → s x ≠ 0`. Introduce `x hx h0`. Establish `hpos` using `(isOfFinOrder_fbar hx).orderOf_pos`. Establish `: s x ^ orderOf x = 1` using `by rw [← map_pow, pow_orderOf_eq_one, map_one]`. Rewrite `this` using `[h0, zero_pow hpos.ne']`.

Conclude with `zero_ne_one this`. Establish `hinj : Function.Injective s`. Introduce `x y h`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases.

Both sides reduce to the same expression. Conclude with `absurd (h.symm.trans hs0) (hsne y hy)`. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Conclude with `absurd (h.trans hs0) (hsne x hx)`. Conclude with `redHom_inj A κ t ht x y hx hy (orderOf_coprime hx) (orderOf_coprime hy) h`.

Establish `hsurj : Function.Surjective s`. Introduce `y`. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Conclude with `⟨0, hs0⟩`. Establish `hn` using `(isOfFinOrder_fbar hy).orderOf_pos`.

Use `set n := orderOf y`. Establish `hmem : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ∈ nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g) ↔ z ^ n = 1` using `fun z => mem_nthRootsFinset hn 1`. Take `⟨a, -, ha⟩` from `Finset.surj_on_of_inj_on_of_card_le (s := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (t := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (fun a _ => s a) (fun a ha => (hmem _).2 (by rw [← map_pow, (hmem a).1 ha, map_one])) (fun a₁ a₂ _ _ h => hinj h) le_r …`. Conclude with `⟨a, ha.symm⟩`. Set `e : Formalism.CyclotomicNorms.Fbar g ≃* Formalism.CyclotomicNorms.Fbar g` to `MulEquiv.ofBijective s ⟨hinj, hsurj⟩`.

Establish `he : ∀ x, e x = s x` using `fun x => rfl`. Use `⟨t.comp e.symm.toMonoidHom, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Use `⟨mem_of_monoidHom A t _, ?_⟩` and prove the remaining obligations. Establish `h1 : s (e.symm x) = x` using `by rw [← he, MulEquiv.apply_symm_apply]`.

Establish `h2` using `hs (e.symm x)`. Unfold `redThrough at h2`. Rewrite `h2` using `[dif_pos (mem_of_monoidHom A t _)]`. Conclude with `h2.symm.trans h1`. Introduce `x y hx hy h`.

Establish `hx' : e.symm x ≠ 0` using `fun h0 => hx (by rw [← e.apply_symm_apply x, h0, he, hs0])`. Establish `hy' : e.symm y ≠ 0` using `fun h0 => hy (by rw [← e.apply_symm_apply y, h0, he, hs0])`. Conclude with `e.symm.injective (ht _ _ hx' hy' h)`.
-/
theorem exists_teich_reindex : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ,
      Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  intro g _ A κ t ht
  set s := redHom A κ t with hs_def
  have hs : ∀ x, s x = redThrough A κ (t x) := fun x => rfl
  have ht0 : t 0 = 0 := map_zero_of_inj t ht
  have hs0 : s 0 = 0 := by
    rw [hs, ht0]; unfold redThrough; rw [dif_pos (zero_mem A)]
    have : (⟨0, zero_mem A⟩ : A) = 0 := rfl
    rw [this, map_zero, map_zero]
  have hsne : ∀ x, x ≠ 0 → s x ≠ 0 := by
    intro x hx h0
    have hpos := (isOfFinOrder_fbar hx).orderOf_pos
    have : s x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h0, zero_pow hpos.ne'] at this
    exact zero_ne_one this
  have hinj : Function.Injective s := by
    intro x y h
    rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne y 0 with rfl | hy
      · rfl
      · exact absurd (h.symm.trans hs0) (hsne y hy)
    · rcases eq_or_ne y 0 with rfl | hy
      · exact absurd (h.trans hs0) (hsne x hx)
      · exact redHom_inj A κ t ht x y hx hy (orderOf_coprime hx) (orderOf_coprime hy) h
  have hsurj : Function.Surjective s := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, hs0⟩
    have hn := (isOfFinOrder_fbar hy).orderOf_pos
    set n := orderOf y
    have hmem : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ∈ nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g) ↔ z ^ n = 1 :=
      fun z => mem_nthRootsFinset hn 1
    obtain ⟨a, -, ha⟩ := Finset.surj_on_of_inj_on_of_card_le (s := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g))
      (t := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (fun a _ => s a)
      (fun a ha => (hmem _).2 (by rw [← map_pow, (hmem a).1 ha, map_one]))
      (fun a₁ a₂ _ _ h => hinj h) le_rfl y ((hmem y).2 (pow_orderOf_eq_one y))
    exact ⟨a, ha.symm⟩
  let e : Formalism.CyclotomicNorms.Fbar g ≃* Formalism.CyclotomicNorms.Fbar g := MulEquiv.ofBijective s ⟨hinj, hsurj⟩
  have he : ∀ x, e x = s x := fun x => rfl
  refine ⟨t.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    refine ⟨mem_of_monoidHom A t _, ?_⟩
    have h1 : s (e.symm x) = x := by rw [← he, MulEquiv.apply_symm_apply]
    have h2 := hs (e.symm x)
    unfold redThrough at h2
    rw [dif_pos (mem_of_monoidHom A t _)] at h2
    exact h2.symm.trans h1
  · intro x y hx hy h
    have hx' : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0, he, hs0])
    have hy' : e.symm y ≠ 0 := fun h0 => hy (by rw [← e.apply_symm_apply y, h0, he, hs0])
    exact e.symm.injective (ht _ _ hx' hy' h)

end GlobalTheory.TeichAt

end
