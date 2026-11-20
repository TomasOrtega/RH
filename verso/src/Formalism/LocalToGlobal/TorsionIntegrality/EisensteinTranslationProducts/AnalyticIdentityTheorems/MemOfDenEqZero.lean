import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenySigma

noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F
namespace EvenThetaIsogeny

open IsogenySigmaQuotient

variable (L : PeriodPair)

/- English proof (translation)
The claim follows from `e ▸ h`.
-/
lemma mem_of_eq {x y : ℂ} (h : y ∈ L.lattice) (e : x = y) : x ∈ L.lattice := e ▸ h

variable (α t : ℂ) (T : Finset ℂ)

/- English proof (translation)
Take `⟨hT1, hT2, hT3⟩` from `hT`. Take `⟨Q₀, hQ₀, -⟩` from `hT3 (t / α) (mem_of_eq L (zero_mem _) (by field_simp; ring))`. Establish `hinj1 : Function.Injective (fun Q : ℂ => Q - Q₀)` using `sub_left_injective`. Establish `hinj2 : Function.Injective (fun Q : ℂ => -Q - Q₀)` using `fun a b h => by`. Establish `h' : -a - Q₀ = -b - Q₀` using `h`.

Take the linear combination `-h'`. Establish `hno : ∀ Q ∈ T, ∀ Q' ∈ T, Q + Q' ∉ L.lattice`. Introduce `Q hQ Q' hQ' h`. Establish `h'` using `hT2 Q hQ Q' hQ' (Or.inr h)`. Rewrite `h` using `[← h']`.

Conclude with `(hT1 Q hQ).2 (mem_of_eq L h (by ring))`. Establish `hdisj : Disjoint ((T.erase Q₀).image (fun Q : ℂ => Q - Q₀)) (T.image (fun Q : ℂ => -Q - Q₀))`. Rewrite using `[Finset.disjoint_left]`. Introduce `P hP hP'`. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.1 hP`.

Take `⟨Q', hQ', h⟩` from `Finset.mem_image.1 hP'`. Conclude with `hno Q (Finset.mem_of_mem_erase hQ) Q' hQ' (mem_of_eq L (zero_mem _) (by linear_combination -h))`. Establish `hker : IsKerReps L α ((T.erase Q₀).image (fun Q : ℂ => Q - Q₀) ∪ T.image (fun Q : ℂ => -Q - Q₀))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`.

Break down `Finset.mem_union.1 hP with hP | hP` into its components or cases. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.1 hP`. Establish `hQT` using `Finset.mem_of_mem_erase hQ`. Conclude with `⟨mem_of_eq L (sub_mem (hT1 Q hQT).1 (hT1 Q₀ hQ₀).1) (by ring), fun h => Finset.ne_of_mem_erase hQ (hT2 Q hQT Q₀ hQ₀ (Or.inl h))⟩`. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.1 hP`.

Conclude with `⟨mem_of_eq L (neg_mem (add_mem (add_mem (hT1 Q hQ).1 (hT1 Q₀ hQ₀).1) h2t)) (by ring), fun h => hno Q hQ Q₀ hQ₀ (mem_of_eq L (neg_mem h) (by ring))⟩`. Introduce `P hP P' hP' h`. Apply the tactic sequence `rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'`. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.1 hP`. Take `⟨Q', hQ', rfl⟩` from `Finset.mem_image.1 hP'`.

Rewrite using `[hT2 Q (Finset.mem_of_mem_erase hQ) Q' (Finset.mem_of_mem_erase hQ') (Or.inl (mem_of_eq L h (by ring)))]`. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.1 hP`. Take `⟨Q', hQ', rfl⟩` from `Finset.mem_image.1 hP'`. Conclude with `absurd (mem_of_eq L h (by ring)) (hno Q (Finset.mem_of_mem_erase hQ) Q' hQ')`. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.1 hP`.

Take `⟨Q', hQ', rfl⟩` from `Finset.mem_image.1 hP'`. Conclude with `absurd (mem_of_eq L (neg_mem h) (by ring)) (hno Q hQ Q' (Finset.mem_of_mem_erase hQ'))`. Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.1 hP`. Take `⟨Q', hQ', rfl⟩` from `Finset.mem_image.1 hP'`. Rewrite using `[hT2 Q hQ Q' hQ' (Or.inl (mem_of_eq L (neg_mem h) (by ring)))]`.

Introduce `z hz hz0`. Take `⟨Q, hQ, h⟩` from `hT3 (z + Q₀) (mem_of_eq L (add_mem hz (hT1 Q₀ hQ₀).1) (by ring))`. Break down `h with h | h` into its components or cases. Use `⟨Q - Q₀, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨fun hne => hz0 (mem_of_eq L h (by rw [hne]; ring)), hQ⟩)), mem_of_eq L h (by ring)⟩` and prove the remaining obligations. Conclude with `⟨-Q - Q₀, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ), mem_of_eq L h (by ring)⟩`.

Establish `hcard` using `kernel_reps_card L α _ hα hst hker`. Rewrite `hcard` using `[Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2, Finset.card_erase_of_mem hQ₀]`. Establish `hpos : 1 ≤ T.card` using `Finset.card_pos.2 ⟨Q₀, hQ₀⟩`. Rewrite using `[← hcard]`. Move the coercions through the operations in `[Nat.cast_sub hpos]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma card_eq (hα : α ≠ 0) (hst : MulStable L α) (h2t : 2 * t ∈ L.lattice)
    (hT : IsFibreReps L α t T) : 2 * (T.card : ℝ) = Complex.normSq α := by
  classical
  obtain ⟨hT1, hT2, hT3⟩ := hT
  obtain ⟨Q₀, hQ₀, -⟩ := hT3 (t / α) (mem_of_eq L (zero_mem _) (by field_simp; ring))
  have hinj1 : Function.Injective (fun Q : ℂ => Q - Q₀) := sub_left_injective
  have hinj2 : Function.Injective (fun Q : ℂ => -Q - Q₀) := fun a b h => by
    have h' : -a - Q₀ = -b - Q₀ := h
    linear_combination -h'
  have hno : ∀ Q ∈ T, ∀ Q' ∈ T, Q + Q' ∉ L.lattice := by
    intro Q hQ Q' hQ' h
    have h' := hT2 Q hQ Q' hQ' (Or.inr h)
    rw [← h'] at h
    exact (hT1 Q hQ).2 (mem_of_eq L h (by ring))
  have hdisj : Disjoint ((T.erase Q₀).image (fun Q : ℂ => Q - Q₀))
      (T.image (fun Q : ℂ => -Q - Q₀)) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨Q', hQ', h⟩ := Finset.mem_image.1 hP'
    exact hno Q (Finset.mem_of_mem_erase hQ) Q' hQ'
      (mem_of_eq L (zero_mem _) (by linear_combination -h))
  have hker : IsKerReps L α
      ((T.erase Q₀).image (fun Q : ℂ => Q - Q₀) ∪ T.image (fun Q : ℂ => -Q - Q₀)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro P hP
      rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        have hQT := Finset.mem_of_mem_erase hQ
        exact ⟨mem_of_eq L (sub_mem (hT1 Q hQT).1 (hT1 Q₀ hQ₀).1) (by ring),
          fun h => Finset.ne_of_mem_erase hQ (hT2 Q hQT Q₀ hQ₀ (Or.inl h))⟩
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        exact ⟨mem_of_eq L (neg_mem (add_mem (add_mem (hT1 Q hQ).1 (hT1 Q₀ hQ₀).1) h2t)) (by ring),
          fun h => hno Q hQ Q₀ hQ₀ (mem_of_eq L (neg_mem h) (by ring))⟩
    · intro P hP P' hP' h
      rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        rw [hT2 Q (Finset.mem_of_mem_erase hQ) Q' (Finset.mem_of_mem_erase hQ')
          (Or.inl (mem_of_eq L h (by ring)))]
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        exact absurd (mem_of_eq L h (by ring)) (hno Q (Finset.mem_of_mem_erase hQ) Q' hQ')
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        exact absurd (mem_of_eq L (neg_mem h) (by ring)) (hno Q hQ Q' (Finset.mem_of_mem_erase hQ'))
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hP'
        rw [hT2 Q hQ Q' hQ' (Or.inl (mem_of_eq L (neg_mem h) (by ring)))]
    · intro z hz hz0
      obtain ⟨Q, hQ, h⟩ := hT3 (z + Q₀) (mem_of_eq L (add_mem hz (hT1 Q₀ hQ₀).1) (by ring))
      rcases h with h | h
      · refine ⟨Q - Q₀, Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_erase.2 ⟨fun hne => hz0 (mem_of_eq L h (by rw [hne]; ring)), hQ⟩)),
          mem_of_eq L h (by ring)⟩
      · exact ⟨-Q - Q₀, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ),
          mem_of_eq L h (by ring)⟩
  have hcard := kernel_reps_card L α _ hα hst hker
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2, Finset.card_erase_of_mem hQ₀] at hcard
  have hpos : 1 ≤ T.card := Finset.card_pos.2 ⟨Q₀, hQ₀⟩
  rw [← hcard]
  push_cast [Nat.cast_sub hpos]
  ring

def num (z : ℂ) : ℂ := th0 L t (α * z)

def den (z : ℂ) : ℂ := ∏ Q ∈ T, fac L Q z

/- English proof (translation)
Unfold `th0`. Rewrite using `[div_eq_inv_mul]`. Both sides reduce to the same expression.
-/
lemma thetaZero_periodLattice_eq (w : ℂ) : th0 L t w = (opU L t (sgStar L) 0)⁻¹ * (sgStar L (w + t) *
    Complex.exp (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) := by
  unfold th0
  rw [div_eq_inv_mul]
  rfl

/- English proof (translation)
Take `⟨Q, hQ, hzQ⟩` from `hT.2.2 z hz`. Rewrite using `[Finset.sum_eq_single Q]`. Break down `hzQ with h | h` into its components or cases. Rewrite using `[ind_of_mem L h, ind_of_notMem L, zero_add]`. Conclude with `fun h' => (hT.1 Q hQ).2 (mem_of_eq L (sub_mem h' h) (by ring))`.

Rewrite using `[ind_of_mem L h, ind_of_notMem L, add_zero]`. Conclude with `fun h' => (hT.1 Q hQ).2 (mem_of_eq L (sub_mem h h') (by ring))`. Introduce `Q' hQ' hne`. Rewrite using `[ind_of_notMem L, ind_of_notMem L, add_zero]`. Introduce `h'`.

Use `hne (hT.2.1 Q' hQ' Q hQ ?_)` and prove the remaining obligations. Break down `hzQ with h | h` into its components or cases. Conclude with `Or.inl (mem_of_eq L (sub_mem h h') (by ring))`. Conclude with `Or.inr (mem_of_eq L (sub_mem h h') (by ring))`. Introduce `h'`.

Use `hne (hT.2.1 Q' hQ' Q hQ ?_)` and prove the remaining obligations. Break down `hzQ with h | h` into its components or cases. Conclude with `Or.inr (mem_of_eq L (sub_mem h' h) (by ring))`. Conclude with `Or.inl (mem_of_eq L (sub_mem h' h) (by ring))`. Introduce `h`.

Conclude with `absurd hQ h`.
-/
lemma count (hT : IsFibreReps L α t T) (z : ℂ) (hz : α * z - t ∈ L.lattice) :
    ∑ Q ∈ T, (ind L (z + Q) + ind L (z - Q)) = 1 := by
  obtain ⟨Q, hQ, hzQ⟩ := hT.2.2 z hz
  rw [Finset.sum_eq_single Q]
  · rcases hzQ with h | h
    · rw [ind_of_mem L h, ind_of_notMem L, zero_add]
      exact fun h' => (hT.1 Q hQ).2 (mem_of_eq L (sub_mem h' h) (by ring))
    · rw [ind_of_mem L h, ind_of_notMem L, add_zero]
      exact fun h' => (hT.1 Q hQ).2 (mem_of_eq L (sub_mem h h') (by ring))
  · intro Q' hQ' hne
    rw [ind_of_notMem L, ind_of_notMem L, add_zero]
    · intro h'
      refine hne (hT.2.1 Q' hQ' Q hQ ?_)
      rcases hzQ with h | h
      · exact Or.inl (mem_of_eq L (sub_mem h h') (by ring))
      · exact Or.inr (mem_of_eq L (sub_mem h h') (by ring))
    · intro h'
      refine hne (hT.2.1 Q' hQ' Q hQ ?_)
      rcases hzQ with h | h
      · exact Or.inr (mem_of_eq L (sub_mem h' h) (by ring))
      · exact Or.inl (mem_of_eq L (sub_mem h' h) (by ring))
  · intro h
    exact absurd hQ h

/- English proof (translation)
Take `⟨k, hk⟩` from `altEInt L ω ω₀ hω hω₀`. Unfold `thetaZeroCharacter`. Rewrite using `[mul_pow, semiChar_sq, one_mul, sq, ← Complex.exp_add, hk]`. Rewrite using `[← Complex.exp_int_mul_two_pi_mul_I k]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma th0Char_sq (ω₀ ω : ℂ) (hω₀ : ω₀ ∈ L.lattice) (hω : ω ∈ L.lattice) :
    thetaZeroCharacter L ω₀ ω ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := altEInt L ω ω₀ hω hω₀
  unfold thetaZeroCharacter
  rw [mul_pow, semiChar_sq, one_mul, sq, ← Complex.exp_add, hk]
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  congr 1
  push_cast
  ring

end EvenThetaIsogeny

end Formalism.L2.Th1.F
