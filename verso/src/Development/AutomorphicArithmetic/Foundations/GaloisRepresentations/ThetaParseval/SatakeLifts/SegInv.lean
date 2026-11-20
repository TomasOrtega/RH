import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `hinj : ∀ i ∈ (Finset.range t).val, ∀ j ∈ (Finset.range t).val, t - 1 - i = t - 1 - j → i = j`. Introduce `i hi j hj h`. Simplify using `only [Finset.mem_val, Finset.mem_range] at hi hj`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Multiset.Nodup.ext (Multiset.Nodup.map_on hinj (Finset.range t).nodup) (Finset.range t).nodup]`.

Introduce `y`. Simplify using `only [Multiset.mem_map, Finset.mem_val, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`. Use linear arithmetic over natural numbers and integers.

Introduce `hy`. Conclude with `⟨t - 1 - y, by omega, by omega⟩`.
-/
private theorem range_val_map_rev (t : ℕ) :
    (Finset.range t).val.map (fun i : ℕ => t - 1 - i) = (Finset.range t).val := by
  have hinj : ∀ i ∈ (Finset.range t).val, ∀ j ∈ (Finset.range t).val, t - 1 - i = t - 1 - j → i = j := by
    intro i hi j hj h
    simp only [Finset.mem_val, Finset.mem_range] at hi hj
    omega
  rw [Multiset.Nodup.ext (Multiset.Nodup.map_on hinj (Finset.range t).nodup) (Finset.range t).nodup]
  intro y
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hy
    exact ⟨t - 1 - y, by omega, by omega⟩

/- English proof (translation)
Use `ext`. Rewrite using `[Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.coe_npowU]`. Unfold `GlobalTheory.LFun.npow`. Conclude with `Complex.cpow_neg _ _`.
-/
private theorem npowU_neg {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) :
    GlobalTheory.LFun.npowU w (-z) = (GlobalTheory.LFun.npowU w z)⁻¹ := by
  ext
  rw [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.coe_npowU]
  unfold GlobalTheory.LFun.npow
  exact Complex.cpow_neg _ _

/- English proof (translation)
Introduce `K _ _ w x t`. Unfold `GlobalTheory.LFun.seg`. Rewrite using `[Multiset.map_map]`. Use `conv_rhs => rw [← range_val_map_rev t, Multiset.map_map]`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises.

Introduce `i hi`. Simplify using `only [Finset.mem_val, Finset.mem_range] at hi`. Simplify using `only [Function.comp_apply, mul_inv, ← npowU_neg]`. Use `congr 2`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega : 1 + i ≤ t)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.TP.Loc.segInv :
    UpperTheory.Gal.TP.Loc.SegInv := by
  intro K _ _ w x t
  unfold GlobalTheory.LFun.seg
  rw [Multiset.map_map]
  conv_rhs => rw [← range_val_map_rev t, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i hi
  simp only [Finset.mem_val, Finset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv, ← npowU_neg]
  congr 2
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + i ≤ t)]
  push_cast
  ring
