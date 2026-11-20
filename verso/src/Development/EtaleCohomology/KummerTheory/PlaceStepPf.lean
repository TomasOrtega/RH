import Development.EtaleCohomology.KummerTheory.PlaceExPf
import Mathlib.RingTheory.Valuation.LocalSubring

noncomputable section

open IsLocalRing Algebra

namespace LateralTheory.KummerTheory

def PlaceResGood : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → ∀ (y : K) (S : Subring K) (hAS : A.toSubring ≤ S),
    S = (Algebra.adjoin A.toSubring {y}).toSubring → ∀ (Q : Ideal S) [Q.IsMaximal],
      (maximalIdeal A.toSubring).map (Subring.inclusion hAS) ≤ Q →
        PlaceGood k K (LocalSubring.ofPrime S Q)

/- English proof (translation)
Introduce `k K _ _ _ _ A hA hmax x`. Establish `collapse : ∀ (y : K) (S : Subring K) (hAS : A.toSubring ≤ S), S = (Algebra.adjoin A.toSubring {y}).toSubring → ∀ (Q : Ideal S) [Q.IsMaximal], (maximalIdeal A.toSubring).map (Subring.inclusion hAS) ≤ Q → S ≤ A.toSubring`. Introduce `y S hAS hS Q _ hQ`. Establish `hle : A ≤ LocalSubring.ofPrime S Q`. Use `⟨hAS.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]`. Use `.trans ?_ (Ideal.map_mono hQ)` and prove the remaining obligations. Rewrite using `[Ideal.map_map]`. Both sides reduce to the same expression. Conclude with `(LocalSubring.le_ofPrime S Q).trans (hmax _ hle (hR k K A hA y S hAS hS Q hQ)).1`.

Establish `top : ∀ y ∉ A.toSubring, (maximalIdeal A.toSubring).map (Subring.inclusion (T` using `(Algebra.adjoin A.toSubring {y}).toSubring) (fun r hr => algebraMap_mem (Algebra.adjoin A.toSubring {y}) ⟨r, hr⟩)) = ⊤ := by`. Introduce `y hy`. Assume the negation of the conclusion as `hne`. Take `⟨Q, hQm, hQ⟩` from `Ideal.exists_le_maximal _ hne`. Conclude with `hy (collapse y _ _ rfl Q hQ (self_mem_adjoin_singleton _ _))`.

Establish `intmem : ∀ z : K, IsIntegral A.toSubring z → z ∈ A.toSubring`. Introduce `z hz`. Set `S` to `A.toSubring[z]`. Establish `: Algebra.IsIntegral A.toSubring S` using `Algebra.IsIntegral.adjoin (by simpa)`. Take `⟨Q : Ideal S.toSubring, hQ, e⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (maximalIdeal A.toSubring) (le_maximalIdeal (by set_option synthInstance.maxHeartbeats 400000 in simp))`.

Conclude with `collapse z S.toSubring (fun r hr => algebraMap_mem S ⟨r, hr⟩) rfl Q (Ideal.map_le_iff_le_comap.mpr e.ge) (self_mem_adjoin_singleton _ _)`. Distinguish the cases in `hx : x ∈ A.toSubring`. Conclude with `Or.inl hx`. Use `right`. Use `intmem _ ?_` and prove the remaining obligations.

Establish `hx0 : x ≠ 0` using `fun e => hx (e ▸ zero_mem _)`. Set `` to `invertibleOfNonzero hx0`. Establish `⟨p, hp, hpx⟩` using `exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _ (maximalIdeal.isMaximal A.toSubring).ne_top (top_unique ((top x hx).ge.trans le_self_add))`. Establish `H : IsUnit p.leadingCoeff` using `of_not_not fun h => by simpa using sub_mem h hp`. Conclude with `⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩`.
-/
theorem PlaceStep_of (hR : PlaceResGood) : PlaceStep := by
  intro k K _ _ _ _ A hA hmax x

  have collapse : ∀ (y : K) (S : Subring K) (hAS : A.toSubring ≤ S),
      S = (Algebra.adjoin A.toSubring {y}).toSubring → ∀ (Q : Ideal S) [Q.IsMaximal],
      (maximalIdeal A.toSubring).map (Subring.inclusion hAS) ≤ Q → S ≤ A.toSubring := by
    intro y S hAS hS Q _ hQ
    have hle : A ≤ LocalSubring.ofPrime S Q := by
      refine ⟨hAS.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩
      conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
      refine .trans ?_ (Ideal.map_mono hQ)
      rw [Ideal.map_map]; rfl
    exact (LocalSubring.le_ofPrime S Q).trans (hmax _ hle (hR k K A hA y S hAS hS Q hQ)).1
  have top : ∀ y ∉ A.toSubring,
      (maximalIdeal A.toSubring).map
        (Subring.inclusion (T := (Algebra.adjoin A.toSubring {y}).toSubring)
          (fun r hr => algebraMap_mem (Algebra.adjoin A.toSubring {y}) ⟨r, hr⟩)) = ⊤ := by
    intro y hy
    by_contra hne
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_le_maximal _ hne
    exact hy (collapse y _ _ rfl Q hQ (self_mem_adjoin_singleton _ _))
  have intmem : ∀ z : K, IsIntegral A.toSubring z → z ∈ A.toSubring := by
    intro z hz
    let S := A.toSubring[z]
    have : Algebra.IsIntegral A.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
    obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := S) (maximalIdeal A.toSubring) (le_maximalIdeal (by set_option synthInstance.maxHeartbeats 400000 in simp))
    exact collapse z S.toSubring (fun r hr => algebraMap_mem S ⟨r, hr⟩) rfl Q
      (Ideal.map_le_iff_le_comap.mpr e.ge) (self_mem_adjoin_singleton _ _)
  by_cases hx : x ∈ A.toSubring
  · exact Or.inl hx
  right
  refine intmem _ ?_
  have hx0 : x ≠ 0 := fun e => hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal A.toSubring).ne_top (top_unique ((top x hx).ge.trans le_self_add))
  have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

end LateralTheory.KummerTheory
