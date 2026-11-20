import Mathlib

open Module Module.End

namespace Bl.general_b_fact_left_last

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hkm`. Rewrite using `[show k + d = d + k from Nat.add_comm k d, pow_add, Module.End.mul_apply, hx, map_zero]`.
-/
private lemma pz {T : End K V} {x : V} {k m : ℕ} (hkm : k ≤ m) (hx : (T ^ k) x = 0) :
    (T ^ m) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [show k + d = d + k from Nat.add_comm k d, pow_add, Module.End.mul_apply, hx, map_zero]

/- English proof (translation)
Rewrite `hA`, `hB`, the goal using `[mem_maxGenEigenspace]`. Take `⟨k, hk⟩` from `hA`. Take `⟨l, hl⟩` from `hB`. Establish `hNB : Commute (A - a • 1) B` using `h.sub_left ((Commute.one_left B).smul_left a)`. Establish `hNM : Commute (A - a • 1) (B - b • 1)` using `hNB.sub_right ((Commute.one_right _).smul_right b)`.

Establish `hBM : Commute B (B - b • 1)` using `(Commute.refl B).sub_right ((Commute.one_right B).smul_right b)`. Establish `key : A * B - (a * b) • (1 : End K V) = (A - a • 1) * B + a • (B - b • 1)`. Rewrite using `[sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]`. Normalize the expressions using the abelian group laws. Establish `hc : Commute ((A - a • 1) * B) (a • (B - b • 1))` using `(hNM.mul_left hBM).smul_right a`.

Use `⟨k + l, ?_⟩` and prove the remaining obligations. Rewrite using `[key, hc.add_pow, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, hNB.mul_pow, smul_pow]`. Use `(congrArg _ ?_).trans (smul_zero _)` and prove the remaining obligations.

Break down `le_or_gt k m with hkm | hkm` into its components or cases. Establish `hC : Commute ((A - a • 1) ^ m) (B ^ m * (a ^ (k + l - m) • (B - b • 1) ^ (k + l - m)))` using `(hNB.pow_pow m m).mul_right ((hNM.pow_pow m (k + l - m)).smul_right _)`. Rewrite using `[mul_assoc, hC.eq, Module.End.mul_apply, pz hkm hk, map_zero]`. Rewrite using `[Module.End.mul_apply, LinearMap.smul_apply, pz (by omega) hl, smul_zero, map_zero]`.
-/
theorem goal1 {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A * B).maxGenEigenspace (a * b) := by
  rw [mem_maxGenEigenspace] at hA hB ⊢
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  have hNB : Commute (A - a • 1) B := h.sub_left ((Commute.one_left B).smul_left a)
  have hNM : Commute (A - a • 1) (B - b • 1) :=
    hNB.sub_right ((Commute.one_right _).smul_right b)
  have hBM : Commute B (B - b • 1) :=
    (Commute.refl B).sub_right ((Commute.one_right B).smul_right b)
  have key : A * B - (a * b) • (1 : End K V) = (A - a • 1) * B + a • (B - b • 1) := by
    rw [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]; abel
  have hc : Commute ((A - a • 1) * B) (a • (B - b • 1)) := (hNM.mul_left hBM).smul_right a
  refine ⟨k + l, ?_⟩
  rw [key, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, hNB.mul_pow, smul_pow]
  refine (congrArg _ ?_).trans (smul_zero _)
  rcases le_or_gt k m with hkm | hkm
  · have hC : Commute ((A - a • 1) ^ m) (B ^ m * (a ^ (k + l - m) • (B - b • 1) ^ (k + l - m))) :=
      (hNB.pow_pow m m).mul_right ((hNM.pow_pow m (k + l - m)).smul_right _)
    rw [mul_assoc, hC.eq, Module.End.mul_apply, pz hkm hk, map_zero]
  · rw [Module.End.mul_apply, LinearMap.smul_apply, pz (by omega) hl, smul_zero, map_zero]

end Bl.general_b_fact_left_last
