import Mathlib

open Polynomial Matrix

/- English proof (translation)
Introduce `C ι _ _ _ d hd W hD w hw i`. Establish `key : ∀ S : Finset ι, (fun k => (∏ j ∈ S, (d k - d j)) * w k) ∈ W`. Introduce `S`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Simplify using `using hw`.

Introduce `j S hj ih`. Establish `h2` using `W.sub_mem (hD _ ih) (W.smul_mem (d j) ih)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [Finset.prod_insert hj, mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hu : IsUnit (∏ j ∈ Finset.univ.erase i, (d i - d j))` using `IsUnit.prod_iff.mpr fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm`. Establish `h3` using `W.smul_mem (↑hu.unit⁻¹ : C) (key (Finset.univ.erase i))`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, IsUnit.val_inv_mul, one_mul]`. Establish `hz : ∏ j ∈ Finset.univ.erase i, (d k - d j) = 0` using `Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) (sub_self _)`.

Simplify using `[Pi.single_eq_of_ne hk, hz]`.
-/
theorem UpperTheory.V.AlgebraTools.coordSub :
    ∀ (C ι : Type) [CommRing C] [Fintype ι] [DecidableEq ι] (d : ι → C), (∀ i j, i ≠ j → IsUnit (d i - d j)) →
      ∀ W : Submodule C (ι → C), (∀ w ∈ W, diagonal d *ᵥ w ∈ W) → ∀ w ∈ W, ∀ i, Pi.single i (w i) ∈ W := by
  intro C ι _ _ _ d hd W hD w hw i
  have key : ∀ S : Finset ι, (fun k => (∏ j ∈ S, (d k - d j)) * w k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa using hw
    · intro j S hj ih
      have h2 := W.sub_mem (hD _ ih) (W.smul_mem (d j) ih)
      convert h2 using 1
      funext k
      simp only [Finset.prod_insert hj, mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (d i - d j)) :=
    IsUnit.prod_iff.mpr fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm
  have h3 := W.smul_mem (↑hu.unit⁻¹ : C) (key (Finset.univ.erase i))
  convert h3 using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · have hz : ∏ j ∈ Finset.univ.erase i, (d k - d j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp [Pi.single_eq_of_ne hk, hz]
