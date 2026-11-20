import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiIndex

noncomputable section

open Module

variable {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Rewrite using `[Basis.det_apply, ← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Matrix.transpose_apply, Basis.toMatrix_apply, hv i, map_sum]`. Simplify using `only [map_zsmul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem basis_det_eq {N : Type*} [AddCommGroup N] [Module ℤ N] {r : ℕ} (b : Basis (Fin r) ℤ N)
    (A : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → N) (hv : ∀ k, v k = ∑ l, A k l • b l) : b.det v = A.det := by
  classical
  rw [Basis.det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  rw [Matrix.transpose_apply, Basis.toMatrix_apply, hv i, map_sum]
  simp only [map_zsmul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Take `⟨c, hc0, hc⟩` from `ChangeOfLattice.exists_clear_den T`. Use `choose A hA using hc`. Use `set L := Submodule.span ℤ (Set.range e) with hLdef`. Use `set L' := Submodule.span ℤ (Set.range e') with hL'def`. Use `set f : Fin r → Ω := fun k => (c : Ω) * e' k with hfdef`.

Establish `hAΩ : ∀ k l, (c : Ω) * (T k l : Ω) = (A k l : Ω)` using `fun k l => by`. Establish `h` using `congrArg (fun q : ℚ => (q : Ω)) (hA k l)`. Move the coercions through the operations in `at h`. Conclude with `h`. Establish `hf : ∀ k, f k = ∑ l, A k l • e l`.

Introduce `k`. Simplify using `only [hfdef, hT k, Finset.mul_sum, zsmul_eq_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hAΩ]`. Establish `hc0' : (c : Ω) ≠ 0` using `by exact_mod_cast hc0`.

Establish `hfli : LinearIndependent ℤ f` using `ChangeOfLattice.linearIndependent_const_mul hc0' he'`. Establish `hfc : ∀ k, f k = ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l • e' l`. Introduce `k`. Rewrite using `[Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]`. Simplify using `[hfdef, zsmul_eq_mul]`.

Use `set M := Submodule.span ℤ (Set.range f) with hMdef`. Establish `hML : M ≤ L` using `Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by`. Rewrite using `[hf k]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))`. Establish `hML' : M ≤ L'` using `Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by`.

Rewrite using `[hfc k]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))`. Establish `hML₀ : M.toAddSubgroup ≤ L.toAddSubgroup` using `hML`. Establish `hML'₀ : M.toAddSubgroup ≤ L'.toAddSubgroup` using `hML'`. Establish `i1 : M.toAddSubgroup.relIndex L'.toAddSubgroup = (c ^ r : ℕ)`.

Rewrite using `[AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L'.toAddSubgroup hML'₀ (Basis.span hfli) (Basis.span he')]`. Use `(congrArg Int.natAbs (basis_det_eq _ ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) _ ?_)).trans ?_` and prove the remaining obligations. Introduce `k`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`.

Simplify using `only [AddSubgroupClass.coe_zsmul]`. Use `show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) = ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l • ((Basis.span he' l : Submodule.span ℤ (Set.range e')) : Ω)`. Simplify using `only [Basis.coe_span_apply]`. Conclude with `hfc k`. Rewrite using `[Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast]`.

Establish `i2 : M.toAddSubgroup.relIndex L.toAddSubgroup = (Matrix.of A).det.natAbs`. Rewrite using `[AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L.toAddSubgroup hML₀ (Basis.span hfli) (Basis.span he)]`. Use `congrArg Int.natAbs (basis_det_eq _ (Matrix.of A) _ fun k => ?_)` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`.

Simplify using `only [AddSubgroupClass.coe_zsmul, Matrix.of_apply]`. Use `show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) = ∑ l, A k l • ((Basis.span he l : Submodule.span ℤ (Set.range e)) : Ω)`. Simplify using `only [Basis.coe_span_apply]`. Conclude with `hf k`. Establish `hAdet : (((Matrix.of A).det : ℤ) : ℝ) = (c : ℝ) ^ r * (T.det : ℝ)`.

Establish `hmap : (Int.castRingHom ℚ).mapMatrix (Matrix.of A) = (c : ℚ) • T`. Use extensionality with `i j`. Simplify using `[← hA i j]`. Establish `h1 : (((Matrix.of A).det : ℤ) : ℚ) = (c : ℚ) ^ r * T.det`. Rewrite using `[← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, hmap, Matrix.det_smul, Fintype.card_fin]`.

Rewrite using `[← Rat.cast_intCast, h1, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]`. Establish `hcr : (c : ℝ) ^ r ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hc0)`. Establish `hTr : (T.det : ℝ) ≠ 0` using `by exact_mod_cast hdet`. Establish `h1 : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0`. Rewrite using `[i2]`.

Introduce `h0`. Establish `: (((Matrix.of A).det : ℤ) : ℝ) = 0`. Rewrite using `[Int.natAbs_eq_zero.1 h0, Int.cast_zero]`. Rewrite `this` using `[hAdet]`. Conclude with `mul_ne_zero hcr hTr this`.

Establish `h2 : M.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0`. Rewrite using `[i1]`. Conclude with `pow_ne_zero _ hc0`. Rewrite using `[ChangeOfLattice.log_relIndex_cocycle hML₀ hML'₀ h1 h2, i1, i2, Nat.cast_natAbs, Int.cast_abs, hAdet, Nat.cast_pow]`. Rewrite using `[abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ r), Real.log_mul hcr (abs_ne_zero.2 hTr)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_relIndex_sub {r : ℕ} {e e' : Fin r → Ω} (he : LinearIndependent ℤ e) (he' : LinearIndependent ℤ e')
    (T : Matrix (Fin r) (Fin r) ℚ) (hT : ∀ k, e' k = ∑ l, (T k l : Ω) * e l) (hdet : T.det ≠ 0) :
    Real.log ((Submodule.span ℤ (Set.range e)).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e')).toAddSubgroup) -
      Real.log ((Submodule.span ℤ (Set.range e')).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range e)).toAddSubgroup) =
      -Real.log |(T.det : ℝ)| := by
  classical
  obtain ⟨c, hc0, hc⟩ := ChangeOfLattice.exists_clear_den T
  choose A hA using hc
  set L := Submodule.span ℤ (Set.range e) with hLdef
  set L' := Submodule.span ℤ (Set.range e') with hL'def
  set f : Fin r → Ω := fun k => (c : Ω) * e' k with hfdef
  have hAΩ : ∀ k l, (c : Ω) * (T k l : Ω) = (A k l : Ω) := fun k l => by
    have h := congrArg (fun q : ℚ => (q : Ω)) (hA k l)
    push_cast at h
    exact h
  have hf : ∀ k, f k = ∑ l, A k l • e l := by
    intro k
    simp only [hfdef, hT k, Finset.mul_sum, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, hAΩ]
  have hc0' : (c : Ω) ≠ 0 := by exact_mod_cast hc0
  have hfli : LinearIndependent ℤ f := ChangeOfLattice.linearIndependent_const_mul hc0' he'
  have hfc : ∀ k, f k = ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l • e' l := by
    intro k
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp [hfdef, zsmul_eq_mul]
  set M := Submodule.span ℤ (Set.range f) with hMdef
  have hML : M ≤ L := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hf k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML' : M ≤ L' := Submodule.span_le.2 (Set.range_subset_iff.2 fun k => by
    rw [hfc k]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hML₀ : M.toAddSubgroup ≤ L.toAddSubgroup := hML
  have hML'₀ : M.toAddSubgroup ≤ L'.toAddSubgroup := hML'

  have i1 : M.toAddSubgroup.relIndex L'.toAddSubgroup = (c ^ r : ℕ) := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L'.toAddSubgroup hML'₀ (Basis.span hfli)
      (Basis.span he')]
    refine (congrArg Int.natAbs (basis_det_eq _ ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) _ ?_)).trans ?_
    · intro k
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [AddSubgroupClass.coe_zsmul]
      show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
        ∑ l, ((c : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) k l •
          ((Basis.span he' l : Submodule.span ℤ (Set.range e')) : Ω)
      simp only [Basis.coe_span_apply]
      exact hfc k
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast]
  have i2 : M.toAddSubgroup.relIndex L.toAddSubgroup = (Matrix.of A).det.natAbs := by
    rw [AddSubgroup.relIndex_eq_natAbs_det M.toAddSubgroup L.toAddSubgroup hML₀ (Basis.span hfli)
      (Basis.span he)]
    refine congrArg Int.natAbs (basis_det_eq _ (Matrix.of A) _ fun k => ?_)
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [AddSubgroupClass.coe_zsmul, Matrix.of_apply]
    show ((Basis.span hfli k : Submodule.span ℤ (Set.range f)) : Ω) =
      ∑ l, A k l • ((Basis.span he l : Submodule.span ℤ (Set.range e)) : Ω)
    simp only [Basis.coe_span_apply]
    exact hf k
  have hAdet : (((Matrix.of A).det : ℤ) : ℝ) = (c : ℝ) ^ r * (T.det : ℝ) := by
    have hmap : (Int.castRingHom ℚ).mapMatrix (Matrix.of A) = (c : ℚ) • T := by
      ext i j
      simp [← hA i j]
    have h1 : (((Matrix.of A).det : ℤ) : ℚ) = (c : ℚ) ^ r * T.det := by
      rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, hmap, Matrix.det_smul, Fintype.card_fin]
    rw [← Rat.cast_intCast, h1, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  have hcr : (c : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc0)
  have hTr : (T.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have h1 : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [i2]
    intro h0
    have : (((Matrix.of A).det : ℤ) : ℝ) = 0 := by
      rw [Int.natAbs_eq_zero.1 h0, Int.cast_zero]
    rw [hAdet] at this
    exact mul_ne_zero hcr hTr this
  have h2 : M.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 := by
    rw [i1]
    exact pow_ne_zero _ hc0
  rw [ChangeOfLattice.log_relIndex_cocycle hML₀ hML'₀ h1 h2, i1, i2, Nat.cast_natAbs, Int.cast_abs, hAdet, Nat.cast_pow]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ r), Real.log_mul hcr (abs_ne_zero.2 hTr)]
  ring

end

end ResChiIndex

end GroundTheory.Heights₂.Heights.HilbertSamuel
