import Mathlib
import Formalism.PieriBlockIdeals.WEChain
import Formalism.PieriBlockIdeals.PieriColumnMinors.ContentLinkageHolds
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightExchangeBoundHolds

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

/- English proof (translation)
Rewrite using `[Finset.image_val_of_injOn hW.injective.injOn, Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem map_cast_image_val_eq (l N : ℕ) (W : Fin N → ℤ) (hW : StrictAnti W) :
    Multiset.map (fun u : ℤ => (u : ZMod l)) (Finset.univ.image W).val =
      Multiset.map (fun a => ((W a : ℤ) : ZMod l)) Finset.univ.val := by
  rw [Finset.image_val_of_injOn hW.injective.injOn, Multiset.map_map]
  rfl

/- English proof (translation)
Use `Finset.sum_bij' (fun a ha => (⟨k + j + t - 1 - (a : ℕ), by` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha`. Use the proof step `omega⟩ : Fin t))`. Use the proof step `(fun s _ => (⟨k + j + t - 1 - (s : ℕ), by`. Use `s.isLt` as an intermediate fact.

Use the proof step `omega⟩ : Fin (k + j + t + q))) ?_ ?_ ?_ ?_ ?_`. Introduce `a _`. Conclude with `Finset.mem_univ _`. Introduce `s _`. Use `s.isLt` as an intermediate fact.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha`. Use `ext`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Introduce `s _`. Use `s.isLt` as an intermediate fact. Use `ext`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha`. Rewrite using `[hblock a ha.1 ha.2]`.
-/
theorem sum_filter_block_eq (k j t q : ℕ) (U : Fin (k + j + t + q) → ℤ) (b : ℤ)
    (hblock : ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) :
    ∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := by
  refine Finset.sum_bij'
    (fun a ha => (⟨k + j + t - 1 - (a : ℕ), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      omega⟩ : Fin t))
    (fun s _ => (⟨k + j + t - 1 - (s : ℕ), by
      have := s.isLt
      omega⟩ : Fin (k + j + t + q))) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro s _
    have := s.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    ext
    simp only
    omega
  · intro s _
    have := s.isLt
    ext
    simp only
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [hblock a ha.1 ha.2]

/- English proof (translation)
Introduce `k j t q l h κ K _ _ U U' V V' b b' c c' kc kp hl htl hU hU' hV hV' hU0 hU'h hsum hblock hVb hprodU hprodV hkc hkp hmU hmV hfilt`. Establish `hlink` using `contentLinkage_holds l K _ U U' c hl hprodU`. Establish `hlinkV` using `contentLinkage_holds l K _ V V' c' hl hprodV`. Establish `hmemU : ∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ Finset.univ.image U`. Introduce `s`.

Establish `hs` using `s.isLt`. Use `Finset.mem_image.mpr ⟨⟨k + j + t - 1 - (s : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `h1 : k + j + t - 1 - (k + j + t - 1 - (s : ℕ)) = (s : ℕ)` using `by omega`. Rewrite using `[hblock _ (by simp only; omega) (by simp only; omega)]`. Simplify using `only [h1]`.

Establish `hmemV : ∀ s : Fin t, b' + ((s : ℕ) : ℤ) ∈ Finset.univ.image V`. Introduce `s`. Take `⟨a, ha⟩` from `hVb s`. Conclude with `Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩`. Establish `hKU : |∑ s, kc s| ≤ (mwCount l b t κ (Finset.univ.image U) : ℤ) * ((t : ℤ) + 2 * κ)`.

Use `shiftSumBound_holds l b t κ (Finset.univ.image U) kc hl.pos htl hmemU hkc ?_` and prove the remaining obligations. Rewrite using `[map_cast_image_val_eq l _ U hU, hlink]`. Conclude with `hmU`. Establish `hKV : |∑ s, kp s| ≤ (mwCount l b' t κ (Finset.univ.image V) : ℤ) * ((t : ℤ) + 2 * κ)`. Use `shiftSumBound_holds l b' t κ (Finset.univ.image V) kp hl.pos htl hmemV hkp ?_` and prove the remaining obligations.

Rewrite using `[map_cast_image_val_eq l _ V hV, hlinkV]`. Conclude with `hmV`. Establish `hfilt' : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤ (∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) + (l : ℤ) * (∑ s, kp s) - ∑ s, kc s`. Rewrite using `[sum_filter_block_eq k j t q U b hblock]`. Use `hfilt.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]`. Conclude with `weightExchangeBound_holds k j t q l h κ _ _ U U' (∑ s, kc s) (∑ s, kp s) hU hU' hU0 hU'h hsum hfilt' hKU hKV`.
-/
theorem weightExchangeChain_holds : WEChain := by
  intro k j t q l h κ K _ _ U U' V V' b b' c c' kc kp hl htl hU hU' hV hV' hU0 hU'h hsum hblock hVb
    hprodU hprodV hkc hkp hmU hmV hfilt
  have hlink := contentLinkage_holds l K _ U U' c hl hprodU
  have hlinkV := contentLinkage_holds l K _ V V' c' hl hprodV
  have hmemU : ∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ Finset.univ.image U := by
    intro s
    have hs := s.isLt
    refine Finset.mem_image.mpr ⟨⟨k + j + t - 1 - (s : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    have h1 : k + j + t - 1 - (k + j + t - 1 - (s : ℕ)) = (s : ℕ) := by omega
    rw [hblock _ (by simp only; omega) (by simp only; omega)]
    simp only [h1]
  have hmemV : ∀ s : Fin t, b' + ((s : ℕ) : ℤ) ∈ Finset.univ.image V := by
    intro s
    obtain ⟨a, ha⟩ := hVb s
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
  have hKU : |∑ s, kc s| ≤ (mwCount l b t κ (Finset.univ.image U) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b t κ (Finset.univ.image U) kc hl.pos htl hmemU hkc ?_
    rw [map_cast_image_val_eq l _ U hU, hlink]
    exact hmU
  have hKV : |∑ s, kp s| ≤ (mwCount l b' t κ (Finset.univ.image V) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b' t κ (Finset.univ.image V) kp hl.pos htl hmemV hkp ?_
    rw [map_cast_image_val_eq l _ V hV, hlinkV]
    exact hmV
  have hfilt' : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) +
        (l : ℤ) * (∑ s, kp s) - ∑ s, kc s := by
    rw [sum_filter_block_eq k j t q U b hblock]
    refine hfilt.trans (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact weightExchangeBound_holds k j t q l h κ _ _ U U' (∑ s, kc s) (∑ s, kp s) hU hU' hU0 hU'h hsum hfilt'
    hKU hKV

end Formalism.CohomologicalDescent
