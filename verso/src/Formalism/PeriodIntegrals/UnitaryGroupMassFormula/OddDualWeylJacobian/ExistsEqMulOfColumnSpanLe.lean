import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace Misc

/- English proof (translation)
Establish `h : PI.OddDualWeyl.sgnK K m = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : K)`. Unfold `PI.OddDualWeyl.sgnK PI.OddDualWeyl.revCol`. Establish `hr : (Fin.rev : Fin (m + 1) → Fin (m + 1)) = ⇑(Fin.revPerm : Equiv.Perm (Fin (m + 1)))` using `rfl`. Rewrite using `[hr, Matrix.det_permute', Matrix.det_one, mul_one]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with hs | hs <;>`.

Simplify using `[h, hs]`.
-/
theorem sgn (K : Type) [Field K] (m : ℕ) : sgnK K m = 1 ∨ sgnK K m = -1 := by
  have h : PI.OddDualWeyl.sgnK K m =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : K) := by
    unfold PI.OddDualWeyl.sgnK PI.OddDualWeyl.revCol
    have hr : (Fin.rev : Fin (m + 1) → Fin (m + 1)) = ⇑(Fin.revPerm : Equiv.Perm (Fin (m + 1))) := rfl
    rw [hr, Matrix.det_permute', Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with hs | hs <;>
    simp [h, hs]

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

/- English proof (translation)
Establish `h2 : Submodule.span O (Set.range fun c : Fin n => fun i => g i c) ≤ Submodule.span O (Set.range fun c : Fin n => fun i => g' i c)` using `h`. Establish `hc : ∀ c : Fin n, ∃ a : Fin n → O, ∑ j, a j • (fun i => g' i j) = fun i => g i c`. Introduce `c`. Establish `hm : (fun i => g i c) ∈ Submodule.span O (Set.range fun c : Fin n => fun i => g' i c)` using `h2 (Submodule.subset_span ⟨c, rfl⟩)`. Conclude with `(Submodule.mem_span_range_iff_exists_fun (R := O)).1 hm`.

Use `choose a ha using hc`. Use `⟨Matrix.of fun j c => a c j, ?_⟩` and prove the remaining obligations. Use extensionality with `i c`. Establish `hi` using `congrFun (ha c) i`. Rewrite using `[← hi, Finset.sum_apply]`.

Simplify using `only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem exists_eq_mul_of_columnSpan_le {n : ℕ} (g g' : Matrix (Fin n) (Fin n) K) (h : colSpan O g ≤ colSpan O g') :
    ∃ v : Matrix (Fin n) (Fin n) O, g = g' * v.map (algebraMap O K) := by
  have h2 : Submodule.span O (Set.range fun c : Fin n => fun i => g i c) ≤
      Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) := h
  have hc : ∀ c : Fin n, ∃ a : Fin n → O, ∑ j, a j • (fun i => g' i j) = fun i => g i c := by
    intro c
    have hm : (fun i => g i c) ∈ Submodule.span O (Set.range fun c : Fin n => fun i => g' i c) :=
      h2 (Submodule.subset_span ⟨c, rfl⟩)
    exact (Submodule.mem_span_range_iff_exists_fun (R := O)).1 hm
  choose a ha using hc
  refine ⟨Matrix.of fun j c => a c j, ?_⟩
  ext i c
  have hi := congrFun (ha c) i
  rw [← hi, Finset.sum_apply]
  simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Unfold `PI.OddDualWeyl.colSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨c, rfl⟩`. Establish `hv : (fun i => (h' * v.map (algebraMap O K)) i c) = ∑ j, v j c • fun i => h' i j`. Use extensionality with `i`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Simplify using `only`. Rewrite using `[hv]`.

Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem colSpan_mul_le {n : ℕ} (h' : Matrix (Fin n) (Fin n) K) (v : Matrix (Fin n) (Fin n) O) :
    colSpan O (h' * v.map (algebraMap O K)) ≤ colSpan O h' := by
  unfold PI.OddDualWeyl.colSpan
  rw [Submodule.span_le]
  rintro x ⟨c, rfl⟩
  have hv : (fun i => (h' * v.map (algebraMap O K)) i c) = ∑ j, v j c • fun i => h' i j := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  dsimp only
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Establish `hU : g⁻¹ * g' = u.map (algebraMap O K)`. Rewrite using `[hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]`. Establish `hinv : g⁻¹ = u.map (algebraMap O K) * g'⁻¹`. Rewrite using `[← hU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg', Matrix.mul_one]`. Rewrite using `[hinv, Matrix.transpose_mul, Matrix.transpose_map]`.
-/
theorem invT_eq {n : ℕ} {g g' : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) (hg' : IsUnit g'.det)
    (u : Matrix (Fin n) (Fin n) O) (hu : g' = g * u.map (algebraMap O K)) :
    (g⁻¹)ᵀ = (g'⁻¹)ᵀ * (uᵀ).map (algebraMap O K) := by
  have hU : g⁻¹ * g' = u.map (algebraMap O K) := by
    rw [hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hinv : g⁻¹ = u.map (algebraMap O K) * g'⁻¹ := by
    rw [← hU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg', Matrix.mul_one]
  rw [hinv, Matrix.transpose_mul, Matrix.transpose_map]

end Misc

/- English proof (translation)
Introduce `K _ m`. Conclude with `PI.OddDualWeyl.Misc.sgn K m`.
-/
theorem reverseSignUnit : SgnPM := by
  intro K _ m
  exact PI.OddDualWeyl.Misc.sgn K m

/- English proof (translation)
Introduce `O K _ _ _ m g g' hg hg' h`. Take `⟨v, hv⟩` from `PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g' g h.ge`. Take `⟨w, hw⟩` from `PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g g' h.le`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[PI.OddDualWeyl.Misc.invT_eq hg hg' v hv]`.

Conclude with `PI.OddDualWeyl.Misc.colSpan_mul_le _ _`. Rewrite using `[PI.OddDualWeyl.Misc.invT_eq hg' hg w hw]`. Conclude with `PI.OddDualWeyl.Misc.colSpan_mul_le _ _`.
-/
theorem columnSpanDual : DualB := by
  intro O K _ _ _ m g g' hg hg' h
  obtain ⟨v, hv⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g' g h.ge
  obtain ⟨w, hw⟩ := PI.OddDualWeyl.Misc.exists_eq_mul_of_columnSpan_le (O := O) g g' h.le
  apply le_antisymm
  · rw [PI.OddDualWeyl.Misc.invT_eq hg hg' v hv]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _
  · rw [PI.OddDualWeyl.Misc.invT_eq hg' hg w hw]
    exact PI.OddDualWeyl.Misc.colSpan_mul_le _ _

end PI.OddDualWeyl
