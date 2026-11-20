import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

open PI.EntAtD

section DerDet

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `i s hi ih`. Rewrite using `[Finset.prod_insert hi, Derivation.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi, smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[Finset.erase_insert_of_ne (by rintro rfl; exact hi hk), Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)), mul_assoc]`.
-/
theorem minorAff_derProd {ι : Type} [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.prod_insert hi, Derivation.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.erase_insert_of_ne (by rintro rfl; exact hi hk),
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)), mul_assoc]

/- English proof (translation)
Simplify using `only [Matrix.det_apply, map_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, map_zsmul, minorAff_derProd, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `h1 : ∏ j, (M.updateCol i (fun r => D (M r i))) (σ j) j = D (M (σ i) i) * ∏ j ∈ Finset.univ.erase i, M (σ j) j`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Matrix.updateCol_self]`. Use `congr 1`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Conclude with `Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)`.

Rewrite using `[Units.smul_def, h1, mul_comm]`.
-/
theorem minorAff_derDet (D : Derivation R A A) {k : ℕ} (M : Matrix (Fin k) (Fin k) A) :
    D M.det = ∑ i, (M.updateCol i (fun r => D (M r i))).det := by
  classical
  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, minorAff_derProd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∏ j, (M.updateCol i (fun r => D (M r i))) (σ j) j =
      D (M (σ i) i) * ∏ j ∈ Finset.univ.erase i, M (σ j) j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Matrix.updateCol_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)
  rw [Units.smul_def, h1, mul_comm]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]`.
-/
theorem minorAff_sumApply {ι : Type} [DecidableEq ι] (s : Finset ι) (D : ι → Derivation R A A) (x : A) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

end DerDet

/- English proof (translation)
Introduce `H N0 N1 t k I b b'`. Set `y : Fin k → PolyXZ H N0 N1` to `fun i => ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) * MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a))`. Establish `hD : ∀ (bb : Fin N1) (f : PolyXZ H N0 N1), dRow (N0` using `N0) t 0 bb f = ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) * MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, bb)) f := by`. Introduce `bb f`. Simplify using `only [dRow]`.

Rewrite using `[minorAff_sumApply]`. Simplify using `only [Derivation.smul_apply, smul_eq_mul]`. Establish `hE : ∀ (bb c : Fin N1) (i : Fin k), dRow (N0` using `N0) t 0 bb (∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) * MvPolynomial.X (Sum.inr ((true, t), a, c))) = if c = bb then y i else 0 := by`. Introduce `bb c i`. Rewrite using `[hD]`.

Distinguish the cases in `hc : c = bb`. Substitute `hc` using the available equality. Simplify using `[y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]`. Simplify using `[map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hc]`. Establish `hy : ∀ (bb : Fin N1) (i : Fin k), dRow (N0` using `N0) t 0 bb (y i) = 0 := by`.

Introduce `bb i`. Rewrite using `[hD]`. Simplify using `[y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]`. Simplify using `only [minorXZ]`. Rewrite using `[minorAff_derDet, map_sum]`.

Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : I c = b'`. Establish `hcol : (fun r => dRow (N0` using `N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) * MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = y := by`. Use function extensionality and compare the values at `r`. Rewrite using `[Matrix.of_apply, hE, if_pos hc]`.

Rewrite using `[hcol, minorAff_derDet]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l = c`. Substitute `hl` using the available equality. Apply `Matrix.det_eq_zero_of_column_eq_zero l` to reduce the goal to its premises.

Introduce `r`. Simplify using `only [Matrix.updateCol_self, hy]`. Distinguish the cases in `hIl : I l = b`. Apply `Matrix.det_zero_of_column_eq hl` to reduce the goal to its premises. Introduce `r`.

Simplify using `only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.updateCol_ne (Ne.symm hl), Matrix.of_apply, hE, if_pos hIl]`. Apply `Matrix.det_eq_zero_of_column_eq_zero l` to reduce the goal to its premises. Introduce `r`. Simplify using `only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.of_apply, hE, if_neg hIl]`. Establish `hcol : (fun r => dRow (N0` using `N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) * MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = fun _ => 0 := by`.

Use function extensionality and compare the values at `r`. Rewrite using `[Matrix.of_apply, hE, if_neg hc]`. Rewrite using `[hcol]`. Use `map_zero (dRow (N0 := N0) t 0 b)` and compare the differences between its conclusion and the goal. Conclude with `Matrix.det_eq_zero_of_column_eq_zero c fun r => Matrix.updateCol_self`.
-/
theorem pMinorAff : PMinorAff := by
  intro H N0 N1 t k I b b'
  classical
  let y : Fin k → PolyXZ H N0 N1 := fun i => ∑ a : Fin N0,
    (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
      MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a))
  have hD : ∀ (bb : Fin N1) (f : PolyXZ H N0 N1), dRow (N0 := N0) t 0 bb f =
      ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
        MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, bb)) f := by
    intro bb f
    simp only [dRow]
    rw [minorAff_sumApply]
    simp only [Derivation.smul_apply, smul_eq_mul]
  have hE : ∀ (bb c : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb
      (∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
        MvPolynomial.X (Sum.inr ((true, t), a, c))) = if c = bb then y i else 0 := by
    intro bb c i
    rw [hD]
    by_cases hc : c = bb
    · subst hc
      simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
    · simp [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hc]
  have hy : ∀ (bb : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb (y i) = 0 := by
    intro bb i
    rw [hD]
    simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [minorXZ]
  rw [minorAff_derDet, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : I c = b'
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = y := by
      funext r
      rw [Matrix.of_apply, hE, if_pos hc]
    rw [hcol, minorAff_derDet]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = c
    · subst hl
      apply Matrix.det_eq_zero_of_column_eq_zero l
      intro r
      simp only [Matrix.updateCol_self, hy]
    · by_cases hIl : I l = b
      · apply Matrix.det_zero_of_column_eq hl
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.updateCol_ne (Ne.symm hl),
          Matrix.of_apply, hE, if_pos hIl]
      · apply Matrix.det_eq_zero_of_column_eq_zero l
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.of_apply, hE, if_neg hIl]
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = fun _ => 0 := by
      funext r
      rw [Matrix.of_apply, hE, if_neg hc]
    rw [hcol]
    convert map_zero (dRow (N0 := N0) t 0 b)
    exact Matrix.det_eq_zero_of_column_eq_zero c fun r => Matrix.updateCol_self

end PI.EntAtD.W
