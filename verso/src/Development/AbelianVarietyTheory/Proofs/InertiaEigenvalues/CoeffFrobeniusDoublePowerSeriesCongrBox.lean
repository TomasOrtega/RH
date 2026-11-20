import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨B, hlow⟩ : ∃ B : R⟦X⟧⟦X⟧, ∀ k ≤ i, X ^ (n + 1) * coeff k B = coeff k D := by`. Use `⟨mk fun k => mk fun m => coeff (m + (n + 1)) (coeff k D), fun k hk => ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Rewrite using `[coeff_X_pow_mul', coeff_mk]`. Use `split_ifs with hm`.

Rewrite using `[coeff_mk, Nat.sub_add_cancel hm]`. Conclude with `(h k hk m (by omega)).symm`. Establish `hdvd : (X : R⟦X⟧⟦X⟧) ^ (i + 1) ∣ D - C (X ^ (n + 1)) * B`. Rewrite using `[X_pow_dvd_iff]`. Introduce `k hk`.

Rewrite using `[map_sub, coeff_C_mul, hlow k (by omega), sub_self]`. Take `⟨A, hA⟩` from `hdvd`. Conclude with `⟨A, B, by rw [← hA]; ring⟩`.
-/
theorem exists_eq_of_coeff_box_eq_zero {R : Type} [CommRing R] (i n : ℕ) (D : R⟦X⟧⟦X⟧)
    (h : ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' D) = 0) :
    ∃ A B : R⟦X⟧⟦X⟧, D = X ^ (i + 1) * A + C (X ^ (n + 1)) * B := by
  classical
  obtain ⟨B, hlow⟩ : ∃ B : R⟦X⟧⟦X⟧, ∀ k ≤ i, X ^ (n + 1) * coeff k B = coeff k D := by
    refine ⟨mk fun k => mk fun m => coeff (m + (n + 1)) (coeff k D), fun k hk => ?_⟩
    ext m
    rw [coeff_X_pow_mul', coeff_mk]
    split_ifs with hm
    · rw [coeff_mk, Nat.sub_add_cancel hm]
    · exact (h k hk m (by omega)).symm
  have hdvd : (X : R⟦X⟧⟦X⟧) ^ (i + 1) ∣ D - C (X ^ (n + 1)) * B := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, coeff_C_mul, hlow k (by omega), sub_self]
  obtain ⟨A, hA⟩ := hdvd
  exact ⟨A, B, by rw [← hA]; ring⟩

/- English proof (translation)
Introduce `l _ K _ φ₂ hC hX i n G H h`. Take `⟨A, B, hAB⟩` from `exists_eq_of_coeff_box_eq_zero i n (G - H) (fun i' hi' n' hn' => by`. Rewrite using `[map_sub, map_sub, h i' hi' n' hn', sub_self])`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : (X : K⟦X⟧⟦X⟧) ∣ φ₂ X := by`. Rewrite using `[hX, map_pow]`.

Establish `hd` using `sub_dvd_pow_sub_pow (C X + X : K⟦X⟧⟦X⟧) (C X) l`. Rewrite `hd` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `hl : 1 ≤ l` using `(Fact.out : Nat.Prime l).one_lt.le`. Establish `e1 : φ₂ (X ^ (i + 1) * A) = X ^ (i + 1) * (c ^ (i + 1) * φ₂ A)`. Rewrite using `[map_mul, map_pow, hc]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : φ₂ (C (X ^ (n + 1)) * B) = C (X ^ (l * (n + 1))) * φ₂ B`. Rewrite using `[map_mul, hC, map_pow, frob_X, ← pow_mul]`. Establish `hz : coeff n (coeff i (φ₂ (G - H))) = 0`. Rewrite using `[hAB, map_add, e1, e2, map_add, map_add, coeff_X_pow_mul', if_neg (show ¬ (i + 1 ≤ i) by omega), map_zero, zero_add, coeff_C_mul, coeff_X_pow_mul', if_neg (show ¬ (l * (n + 1) ≤ n) by nlinarith)]`.

Rewrite `hz` using `[map_sub, map_sub, map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem coeff_frob2_congr_box : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)) := by
  intro l _ K _ φ₂ hC hX i n G H h
  obtain ⟨A, B, hAB⟩ := exists_eq_of_coeff_box_eq_zero i n (G - H) (fun i' hi' n' hn' => by
    rw [map_sub, map_sub, h i' hi' n' hn', sub_self])
  obtain ⟨c, hc⟩ : (X : K⟦X⟧⟦X⟧) ∣ φ₂ X := by
    rw [hX, map_pow]
    have hd := sub_dvd_pow_sub_pow (C X + X : K⟦X⟧⟦X⟧) (C X) l
    rwa [add_sub_cancel_left] at hd
  have hl : 1 ≤ l := (Fact.out : Nat.Prime l).one_lt.le
  have e1 : φ₂ (X ^ (i + 1) * A) = X ^ (i + 1) * (c ^ (i + 1) * φ₂ A) := by
    rw [map_mul, map_pow, hc]
    ring
  have e2 : φ₂ (C (X ^ (n + 1)) * B) = C (X ^ (l * (n + 1))) * φ₂ B := by
    rw [map_mul, hC, map_pow, frob_X, ← pow_mul]
  have hz : coeff n (coeff i (φ₂ (G - H))) = 0 := by
    rw [hAB, map_add, e1, e2, map_add, map_add, coeff_X_pow_mul',
      if_neg (show ¬ (i + 1 ≤ i) by omega), map_zero, zero_add, coeff_C_mul, coeff_X_pow_mul',
      if_neg (show ¬ (l * (n + 1) ≤ n) by nlinarith)]
  rwa [map_sub, map_sub, map_sub, sub_eq_zero] at hz

end GlobalTheory.CrysPrism
