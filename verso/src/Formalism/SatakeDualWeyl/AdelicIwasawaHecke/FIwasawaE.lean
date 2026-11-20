import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaD

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaStepB

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

/- English proof (translation)
Establish `ht` using `t.isLt`. Simplify using `only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 h2 ⊢`. Use linear arithmetic over natural numbers and integers.
-/
private theorem fin_rev_between_of_between (ρ t : Fin n) (h1 : ρ < t) (h2 : t < Fin.rev ρ) :
    ρ < Fin.rev t ∧ Fin.rev t < Fin.rev ρ := by
  have ht := t.isLt
  simp only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 h2 ⊢
  omega

/- English proof (translation)
Use `first`. Consider the case `(rw [neg_mul_neg, mul_div_assoc']; exact mul_div_cancel_left₀ a hp)`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`.
-/
private theorem neg_mul_neg_div_self (a p : L) (hp : p ≠ 0) : -p * (-a / p) = a := by
  first
    | (rw [neg_mul_neg, mul_div_assoc']; exact mul_div_cancel_left₀ a hp)
    | (field_simp; done)
    | (field_simp; ring)

/- English proof (translation)
Establish `hne : ρ ≠ Fin.rev ρ` using `ne_of_lt hρ`. Establish `hσp : σ (M ρ ρ) ≠ 0` using `(map_ne_zero σ).mpr hp`. Establish `hvp : Valued.v (M ρ ρ) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hp`. Establish `hcz : ∀ i, Fin.rev ρ < i → M i ρ = 0` using `fIwasawa_col_zero (σ := σ) M hM r hT ρ hρr hρ`. Take `⟨z, hzeq⟩ : ∃ z : Fin n → L, z = fun t => if ρ < t ∧ t < Fin.rev ρ then -(M t ρ) / M ρ ρ else 0` from `⟨_, rfl⟩`.

Establish `hzout : ∀ t, ¬(ρ < t ∧ t < Fin.rev ρ) → z t = 0`. Introduce `t ht`. Rewrite using `[hzeq]`. Conclude with `if_neg ht`. Establish `hzsupp : ∀ t, z t ≠ 0 → ρ < t ∧ t < Fin.rev ρ`.

Introduce `t ht`. Assume the negation of the conclusion as `h`. Conclude with `ht (hzout t h)`. Establish `hMz : ∀ t, ρ < t → t < Fin.rev ρ → M t ρ = -(M ρ ρ) * z t`. Introduce `t h1 h2`.

Rewrite using `[hzeq]`. Simplify using `only`. Rewrite using `[if_pos (And.intro h1 h2), neg_mul_neg_div_self _ _ hp]`. Establish `hrevmid : ∀ j, ρ < Fin.rev j ∧ Fin.rev j < Fin.rev ρ → ρ < j ∧ j < Fin.rev ρ`. Introduce `j h`.

Establish `h'` using `fin_rev_between_of_between ρ (Fin.rev j) h.1 h.2`. Rewrite `h'` using `[Fin.rev_rev]`. Then use the resulting hypothesis. Take `⟨S, hSeq⟩ : ∃ S : L, S = fIwasawaH σ z z` from `⟨_, rfl⟩`. Establish `hzm : fIwasawaH σ z (fun k => M k ρ) = -(M ρ ρ) * S`. Rewrite using `[hSeq]`.

Simplify using `only [fIwasawaH]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : ρ < j ∧ j < Fin.rev ρ`. Rewrite using `[hMz j hj.1 hj.2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hzout (Fin.rev j) (fun h => hj (hrevmid j h)), map_zero σ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hS : σ S = S`. Rewrite using `[hSeq]`.

Simplify using `only [fIwasawaH, map_sum, map_mul, hσ]`. Conclude with `Fintype.sum_equiv Fin.revPerm _ _ (fun j => by`. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev]`. Use the proof step `ring)`. Establish `key : ∀ j, σ (M (Fin.rev j) ρ) * M j ρ = ((if j = ρ then σ (M (Fin.rev ρ) ρ) * M ρ ρ else 0) + (if j = Fin.rev ρ then σ (M ρ ρ) * M (Fin.rev ρ) ρ else 0)) + σ (M ρ ρ) * M ρ ρ * (σ (z (Fin.rev j)) * z j)`.

Introduce `j`. Break down `lt_trichotomy j ρ with h1 | h1 | h1` into its components or cases. Rewrite using `[hcz (Fin.rev j) (Fin.rev_lt_rev.mpr h1), map_zero σ, hzout j (fun h => lt_asymm h1 h.1), if_neg (ne_of_lt h1), if_neg (ne_of_lt (lt_trans h1 hρ))]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, if_pos (rfl : ρ = ρ), if_neg hne, hzout ρ (fun h => lt_irrefl ρ h.1)]`.

Expand and normalize the polynomial expressions, which then agree. Break down `lt_trichotomy j (Fin.rev ρ) with h2 | h2 | h2` into its components or cases. Establish `hm` using `fin_rev_between_of_between ρ j h1 h2`. Rewrite using `[hMz j h1 h2, hMz (Fin.rev j) hm.1 hm.2, if_neg (ne_of_gt h1), if_neg (ne_of_lt h2), map_mul σ, map_neg σ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, Fin.rev_rev, if_neg hne.symm, if_pos (rfl : Fin.rev ρ = Fin.rev ρ), hzout (Fin.rev ρ) (fun h => lt_irrefl (Fin.rev ρ) h.2)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcz j h2, hzout j (fun h => lt_asymm h2 h.2), if_neg (ne_of_gt h1), if_neg (ne_of_gt h2)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : σ (M (Fin.rev ρ) ρ) * M ρ ρ + σ (M ρ ρ) * M (Fin.rev ρ) ρ + σ (M ρ ρ) * M ρ ρ * S = 0`.

Establish `hiso` using `fIwasawa_iso (σ := σ) M hM ρ hρ`. Rewrite `hiso` using `[Fintype.sum_congr _ _ key]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum] at hiso`. Rewrite using `[hSeq]`. Simplify `hiso` using `only [fIwasawaH]`.

Take `⟨c, hceq⟩ : ∃ c : L, c = -S - M (Fin.rev ρ) ρ / M ρ ρ` from `⟨_, rfl⟩`. Establish `hc0 : c + σ c + fIwasawaH σ z z = 0`. Rewrite using `[← hSeq, hceq, map_sub σ, map_neg σ, map_div₀ σ, hS]`. Clear the denominators using the available nonvanishing facts. Use `first`.

Consider the case `linear_combination hA`. Consider the case `linear_combination -hA`. Consider the case `linear_combination (-1 : L) * hA`. Establish `hzv : ∀ i, Valued.v (z i) ≤ 1`. Introduce `i`.

Distinguish the cases in `h : ρ < i ∧ i < Fin.rev ρ`. Establish `h1` using `hmax i (le_of_lt h.1) (le_of_lt h.2)`. Rewrite `h1` using `[hMz i h.1 h.2, Valuation.map_mul, Valuation.map_neg]`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rw [hzout i h, Valuation.map_zero] first | exact zero_le' | exact zero_le _ | simp`.

Establish `hSv : Valued.v S ≤ 1`. Rewrite using `[hSeq]`. Simplify using `only [fIwasawaH]`. Use `Valuation.map_sum_le _ (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Valuation.map_mul, hσv]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcv : Valued.v c ≤ 1`. Establish `hb` using `hmax (Fin.rev ρ) (le_of_lt hρ) le_rfl`. Establish `hbp : Valued.v (M (Fin.rev ρ) ρ / M ρ ρ) ≤ 1`. Rewrite using `[map_div₀, div_eq_mul_inv]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1 : Valued.v (-S) ≤ 1`. Rewrite using `[Valuation.map_neg]`. Conclude with `hSv`. Rewrite using `[hceq]`.

Use `first`. Consider the case `exact Valuation.map_sub_le _ h1 hbp`. Consider the case `exact le_trans (Valuation.map_sub _ _ _) (max_le h1 hbp)`. Establish `he : ∀ i, Valued.v ((Pi.single (Fin.rev ρ) (1 : L) : Fin n → L) i) ≤ 1`. Introduce `i`.

Distinguish the cases in `h : i = Fin.rev ρ`. Apply the tactic sequence `(rw [h, Pi.single_eq_same, Valuation.map_one]) <;> exact le_rfl`. Apply the tactic sequence `rw [Pi.single_eq_of_ne h, Valuation.map_zero] first | exact zero_le' | exact zero_le _ | simp`. Establish `hee : fIwasawaH σ (Pi.single (Fin.rev ρ) (1 : L)) (Pi.single (Fin.rev ρ) (1 : L)) = 0`. Rewrite using `[fIwasawa_H_single_left (σ := σ), Fin.rev_rev, Pi.single_eq_of_ne hne]`.

Establish `hez : fIwasawaH σ (Pi.single (Fin.rev ρ) (1 : L)) z = 0`. Rewrite using `[fIwasawa_H_single_left (σ := σ), Fin.rev_rev]`. Conclude with `hzout ρ (fun h => lt_irrefl ρ h.1)`. Establish `hcol : ∀ (A : Matrix (Fin n) (Fin n) L) (i j : Fin n), (A * M) i j = (A *ᵥ fun k => M k j) i`. Introduce `A i j`.

Use `first`. Consider the case `rfl`. Consider the case `simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Consider the case `simp [Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct]`. Use `⟨fIwasawaE σ (Pi.single (Fin.rev ρ) 1) z c, And.intro (fIwasawa_E_un (σ := σ) hσ _ z c hee hez hc0) (fIwasawa_int_E (σ := σ) hσv _ z c he hzv hcv), ?_⟩` and prove the remaining obligations.

Introduce `i j hj hji`. Rewrite using `[hcol]`. Distinguish the cases in `hj' : j.val < r`. Establish `hjρ : j < ρ`. Rewrite using `[Fin.lt_iff_val_lt_val, hρr]`.

Conclude with `hj'`. Rewrite using `[fIwasawa_E_fix (σ := σ) ρ z c hzsupp (fun k => M k j) (hT ρ j hj' hjρ) (fun t h1 _ => hT t j hj' (lt_trans hjρ h1))]`. Conclude with `hT i j hj' hji`. Establish `hjρ : j = ρ` using `Fin.ext (by omega)`. Rewrite `hji`, the goal using `[hjρ]`.

Rewrite using `[fIwasawa_E_mulVec (σ := σ), fIwasawa_H_single_left (σ := σ), Fin.rev_rev, hzm]`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Break down `lt_trichotomy i (Fin.rev ρ) with h | h | h` into its components or cases. Rewrite using `[Pi.single_eq_of_ne (ne_of_lt h), hMz i hji h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, Pi.single_eq_same, hzout (Fin.rev ρ) (fun h' => lt_irrefl (Fin.rev ρ) h'.2), hceq] first`. Consider the case `(field_simp; ring)`. Consider the case `(field_simp; done)`. Consider the case `(simp only [mul_zero, mul_one, add_zero]; field_simp; ring)`. Rewrite using `[Pi.single_eq_of_ne (ne_of_gt h), hcz i h, hzout i (fun h' => lt_asymm h h'.2)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fIwasawa_tri_succ_of_max_pivot (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ) (hT : fIwasawaTri r M)
    (ρ : Fin n) (hρr : ρ.val = r) (hρ : ρ < Fin.rev ρ) (hp : M ρ ρ ≠ 0)
    (hmax : ∀ i, ρ ≤ i → i ≤ Fin.rev ρ → Valued.v (M i ρ) ≤ Valued.v (M ρ ρ)) :
    ∃ k, fIwasawaKm σ k ∧ fIwasawaTri (r + 1) (k * M) := by
  have hne : ρ ≠ Fin.rev ρ := ne_of_lt hρ
  have hσp : σ (M ρ ρ) ≠ 0 := (map_ne_zero σ).mpr hp
  have hvp : Valued.v (M ρ ρ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp
  have hcz : ∀ i, Fin.rev ρ < i → M i ρ = 0 := fIwasawa_col_zero (σ := σ) M hM r hT ρ hρr hρ
  obtain ⟨z, hzeq⟩ : ∃ z : Fin n → L,
      z = fun t => if ρ < t ∧ t < Fin.rev ρ then -(M t ρ) / M ρ ρ else 0 := ⟨_, rfl⟩
  have hzout : ∀ t, ¬(ρ < t ∧ t < Fin.rev ρ) → z t = 0 := by
    intro t ht
    rw [hzeq]
    exact if_neg ht
  have hzsupp : ∀ t, z t ≠ 0 → ρ < t ∧ t < Fin.rev ρ := by
    intro t ht
    by_contra h
    exact ht (hzout t h)
  have hMz : ∀ t, ρ < t → t < Fin.rev ρ → M t ρ = -(M ρ ρ) * z t := by
    intro t h1 h2
    rw [hzeq]
    dsimp only
    rw [if_pos (And.intro h1 h2), neg_mul_neg_div_self _ _ hp]
  have hrevmid : ∀ j, ρ < Fin.rev j ∧ Fin.rev j < Fin.rev ρ → ρ < j ∧ j < Fin.rev ρ := by
    intro j h
    have h' := fin_rev_between_of_between ρ (Fin.rev j) h.1 h.2
    rwa [Fin.rev_rev] at h'
  obtain ⟨S, hSeq⟩ : ∃ S : L, S = fIwasawaH σ z z := ⟨_, rfl⟩
  have hzm : fIwasawaH σ z (fun k => M k ρ) = -(M ρ ρ) * S := by
    rw [hSeq]
    simp only [fIwasawaH]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : ρ < j ∧ j < Fin.rev ρ
    · rw [hMz j hj.1 hj.2]
      ring
    · rw [hzout (Fin.rev j) (fun h => hj (hrevmid j h)), map_zero σ]
      ring
  have hS : σ S = S := by
    rw [hSeq]
    simp only [fIwasawaH, map_sum, map_mul, hσ]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by
      simp only [Fin.revPerm_apply, Fin.rev_rev]
      ring)
  have key : ∀ j, σ (M (Fin.rev j) ρ) * M j ρ =
      ((if j = ρ then σ (M (Fin.rev ρ) ρ) * M ρ ρ else 0) +
        (if j = Fin.rev ρ then σ (M ρ ρ) * M (Fin.rev ρ) ρ else 0)) +
        σ (M ρ ρ) * M ρ ρ * (σ (z (Fin.rev j)) * z j) := by
    intro j
    rcases lt_trichotomy j ρ with h1 | h1 | h1
    · rw [hcz (Fin.rev j) (Fin.rev_lt_rev.mpr h1), map_zero σ, hzout j (fun h => lt_asymm h1 h.1),
        if_neg (ne_of_lt h1), if_neg (ne_of_lt (lt_trans h1 hρ))]
      ring
    · rw [h1, if_pos (rfl : ρ = ρ), if_neg hne, hzout ρ (fun h => lt_irrefl ρ h.1)]
      ring
    · rcases lt_trichotomy j (Fin.rev ρ) with h2 | h2 | h2
      · have hm := fin_rev_between_of_between ρ j h1 h2
        rw [hMz j h1 h2, hMz (Fin.rev j) hm.1 hm.2, if_neg (ne_of_gt h1), if_neg (ne_of_lt h2),
          map_mul σ, map_neg σ]
        ring
      · rw [h2, Fin.rev_rev, if_neg hne.symm, if_pos (rfl : Fin.rev ρ = Fin.rev ρ),
          hzout (Fin.rev ρ) (fun h => lt_irrefl (Fin.rev ρ) h.2)]
        ring
      · rw [hcz j h2, hzout j (fun h => lt_asymm h2 h.2), if_neg (ne_of_gt h1),
          if_neg (ne_of_gt h2)]
        ring
  have hA : σ (M (Fin.rev ρ) ρ) * M ρ ρ + σ (M ρ ρ) * M (Fin.rev ρ) ρ +
      σ (M ρ ρ) * M ρ ρ * S = 0 := by
    have hiso := fIwasawa_iso (σ := σ) M hM ρ hρ
    rw [Fintype.sum_congr _ _ key] at hiso
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, ← Finset.mul_sum] at hiso
    rw [hSeq]
    simpa only [fIwasawaH] using hiso
  obtain ⟨c, hceq⟩ : ∃ c : L, c = -S - M (Fin.rev ρ) ρ / M ρ ρ := ⟨_, rfl⟩
  have hc0 : c + σ c + fIwasawaH σ z z = 0 := by
    rw [← hSeq, hceq, map_sub σ, map_neg σ, map_div₀ σ, hS]
    field_simp
    first
      | linear_combination hA
      | linear_combination -hA
      | linear_combination (-1 : L) * hA
  have hzv : ∀ i, Valued.v (z i) ≤ 1 := by
    intro i
    by_cases h : ρ < i ∧ i < Fin.rev ρ
    · have h1 := hmax i (le_of_lt h.1) (le_of_lt h.2)
      rw [hMz i h.1 h.2, Valuation.map_mul, Valuation.map_neg] at h1
      calc Valued.v (z i) = (Valued.v (M ρ ρ))⁻¹ * (Valued.v (M ρ ρ) * Valued.v (z i)) :=
            (inv_mul_cancel_left₀ hvp _).symm
        _ ≤ (Valued.v (M ρ ρ))⁻¹ * Valued.v (M ρ ρ) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvp
    · rw [hzout i h, Valuation.map_zero]
      first | exact zero_le' | exact zero_le _ | simp
  have hSv : Valued.v S ≤ 1 := by
    rw [hSeq]
    simp only [fIwasawaH]
    refine Valuation.map_sum_le _ (fun j _ => ?_)
    rw [Valuation.map_mul, hσv]
    calc Valued.v (z (Fin.rev j)) * Valued.v (z j) ≤ 1 * 1 := by
          first | exact mul_le_one' (hzv _) (hzv _) | (gcongr <;> exact hzv _)
      _ = 1 := mul_one 1
  have hcv : Valued.v c ≤ 1 := by
    have hb := hmax (Fin.rev ρ) (le_of_lt hρ) le_rfl
    have hbp : Valued.v (M (Fin.rev ρ) ρ / M ρ ρ) ≤ 1 := by
      rw [map_div₀, div_eq_mul_inv]
      calc Valued.v (M (Fin.rev ρ) ρ) * (Valued.v (M ρ ρ))⁻¹
          ≤ Valued.v (M ρ ρ) * (Valued.v (M ρ ρ))⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvp
    have h1 : Valued.v (-S) ≤ 1 := by
      rw [Valuation.map_neg]
      exact hSv
    rw [hceq]
    first
      | exact Valuation.map_sub_le _ h1 hbp
      | exact le_trans (Valuation.map_sub _ _ _) (max_le h1 hbp)
  have he : ∀ i, Valued.v ((Pi.single (Fin.rev ρ) (1 : L) : Fin n → L) i) ≤ 1 := by
    intro i
    by_cases h : i = Fin.rev ρ
    · (rw [h, Pi.single_eq_same, Valuation.map_one]) <;> exact le_rfl
    · rw [Pi.single_eq_of_ne h, Valuation.map_zero]
      first | exact zero_le' | exact zero_le _ | simp
  have hee : fIwasawaH σ (Pi.single (Fin.rev ρ) (1 : L)) (Pi.single (Fin.rev ρ) (1 : L)) = 0 := by
    rw [fIwasawa_H_single_left (σ := σ), Fin.rev_rev, Pi.single_eq_of_ne hne]
  have hez : fIwasawaH σ (Pi.single (Fin.rev ρ) (1 : L)) z = 0 := by
    rw [fIwasawa_H_single_left (σ := σ), Fin.rev_rev]
    exact hzout ρ (fun h => lt_irrefl ρ h.1)
  have hcol : ∀ (A : Matrix (Fin n) (Fin n) L) (i j : Fin n),
      (A * M) i j = (A *ᵥ fun k => M k j) i := by
    intro A i j
    first
      | rfl
      | simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      | simp [Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct]
  refine ⟨fIwasawaE σ (Pi.single (Fin.rev ρ) 1) z c,
    And.intro (fIwasawa_E_un (σ := σ) hσ _ z c hee hez hc0)
      (fIwasawa_int_E (σ := σ) hσv _ z c he hzv hcv), ?_⟩
  intro i j hj hji
  rw [hcol]
  by_cases hj' : j.val < r
  · have hjρ : j < ρ := by
      rw [Fin.lt_iff_val_lt_val, hρr]
      exact hj'
    rw [fIwasawa_E_fix (σ := σ) ρ z c hzsupp (fun k => M k j) (hT ρ j hj' hjρ)
      (fun t h1 _ => hT t j hj' (lt_trans hjρ h1))]
    exact hT i j hj' hji
  · have hjρ : j = ρ := Fin.ext (by omega)
    rw [hjρ] at hji ⊢
    rw [fIwasawa_E_mulVec (σ := σ), fIwasawa_H_single_left (σ := σ), Fin.rev_rev, hzm]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_trichotomy i (Fin.rev ρ) with h | h | h
    · rw [Pi.single_eq_of_ne (ne_of_lt h), hMz i hji h]
      ring
    · rw [h, Pi.single_eq_same, hzout (Fin.rev ρ) (fun h' => lt_irrefl (Fin.rev ρ) h'.2), hceq]
      first
        | (field_simp; ring)
        | (field_simp; done)
        | (simp only [mul_zero, mul_one, add_zero]; field_simp; ring)
    · rw [Pi.single_eq_of_ne (ne_of_gt h), hcz i h, hzout i (fun h' => lt_asymm h h'.2)]
      ring

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `_`. Use `⟨1, fIwasawa_Km_one (σ := σ), ?_⟩` and prove the remaining obligations.

Introduce `i j hj _`. Conclude with `absurd hj (Nat.not_lt_zero _)`. Consider the case `succ r ih`. Introduce `hr`. Take `⟨k, hk, hkT⟩` from `ih (by omega)`.

Establish `hrn : r < n` using `by omega`. Establish `hρ : (⟨r, hrn⟩ : Fin n) < Fin.rev ⟨r, hrn⟩`. Rewrite using `[Fin.lt_iff_val_lt_val, Fin.val_rev]`. Use `show r < n - (r + 1)`. Use linear arithmetic over natural numbers and integers.

Establish `hkM : fIwasawaUn σ (k * M)` using `fIwasawa_un_mul (σ := σ) k M (And.left hk) hM`. Take `⟨k1, hk1, hT1, hp1, hmax1⟩` from `fIwasawa_exists_max_pivot (σ := σ) hσv (k * M) hkM r hkT ⟨r, hrn⟩ rfl hρ`. Establish `hk1M : fIwasawaUn σ (k1 * (k * M))` using `fIwasawa_un_mul (σ := σ) k1 (k * M) (And.left hk1) hkM`. Take `⟨k2, hk2, hT2⟩` from `fIwasawa_tri_succ_of_max_pivot (σ := σ) hσ hσv (k1 * (k * M)) hk1M r hT1 ⟨r, hrn⟩ rfl hρ hp1 hmax1`. Use `⟨k2 * (k1 * k), fIwasawa_Km_mul (σ := σ) hk2 (fIwasawa_Km_mul (σ := σ) hk1 hk), ?_⟩` and prove the remaining obligations.

Simplify `hT2` using `only [Matrix.mul_assoc]`.
-/
theorem fIwasawa_reduce (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    ∀ r : ℕ, 2 * r ≤ n → ∃ k, fIwasawaKm σ k ∧ fIwasawaTri r (k * M) := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨1, fIwasawa_Km_one (σ := σ), ?_⟩
    intro i j hj _
    exact absurd hj (Nat.not_lt_zero _)
  | succ r ih =>
    intro hr
    obtain ⟨k, hk, hkT⟩ := ih (by omega)
    have hrn : r < n := by omega
    have hρ : (⟨r, hrn⟩ : Fin n) < Fin.rev ⟨r, hrn⟩ := by
      rw [Fin.lt_iff_val_lt_val, Fin.val_rev]
      show r < n - (r + 1)
      omega
    have hkM : fIwasawaUn σ (k * M) := fIwasawa_un_mul (σ := σ) k M (And.left hk) hM
    obtain ⟨k1, hk1, hT1, hp1, hmax1⟩ :=
      fIwasawa_exists_max_pivot (σ := σ) hσv (k * M) hkM r hkT ⟨r, hrn⟩ rfl hρ
    have hk1M : fIwasawaUn σ (k1 * (k * M)) :=
      fIwasawa_un_mul (σ := σ) k1 (k * M) (And.left hk1) hkM
    obtain ⟨k2, hk2, hT2⟩ :=
      fIwasawa_tri_succ_of_max_pivot (σ := σ) hσ hσv (k1 * (k * M)) hk1M r hT1 ⟨r, hrn⟩ rfl hρ hp1 hmax1
    refine ⟨k2 * (k1 * k), fIwasawa_Km_mul (σ := σ) hk2 (fIwasawa_Km_mul (σ := σ) hk1 hk), ?_⟩
    simpa only [Matrix.mul_assoc] using hT2

/- English proof (translation)
Take `⟨k, hk, hT⟩` from `fIwasawa_reduce (σ := σ) hσ hσv M hM (n / 2) (by omega)`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Establish `hkM : fIwasawaUn σ (k * M)` using `fIwasawa_un_mul (σ := σ) k M (And.left hk) hM`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`.

Distinguish the cases in `hj : j.val < n / 2`. Conclude with `hT i j hj hij'`. Establish `hlt` using `Fin.lt_iff_val_lt_val.mp hij'`. Establish `hi` using `i.isLt`. Establish `hs : (Fin.rev i).val < n / 2`.

Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Establish `h0` using `(fIwasawa_rows (σ := σ) (k * M) hkM (n / 2) hT (Fin.rev i) hs).2 j (by rw [Fin.rev_rev]; exact hij')`. Rewrite `h0` using `[Fin.rev_rev]`. Then use the resulting hypothesis.
-/
theorem fIwasawa_upper (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    ∃ k, fIwasawaKm σ k ∧ (k * M).BlockTriangular id := by
  obtain ⟨k, hk, hT⟩ := fIwasawa_reduce (σ := σ) hσ hσv M hM (n / 2) (by omega)
  refine ⟨k, hk, ?_⟩
  have hkM : fIwasawaUn σ (k * M) := fIwasawa_un_mul (σ := σ) k M (And.left hk) hM
  intro i j hij
  have hij' : j < i := hij
  by_cases hj : j.val < n / 2
  · exact hT i j hj hij'
  · have hlt := Fin.lt_iff_val_lt_val.mp hij'
    have hi := i.isLt
    have hs : (Fin.rev i).val < n / 2 := by
      rw [Fin.val_rev]
      omega
    have h0 := (fIwasawa_rows (σ := σ) (k * M) hkM (n / 2) hT (Fin.rev i) hs).2 j
      (by rw [Fin.rev_rev]; exact hij')
    rwa [Fin.rev_rev] at h0

end FIwasawaStepB

end Formalism.UG.P
