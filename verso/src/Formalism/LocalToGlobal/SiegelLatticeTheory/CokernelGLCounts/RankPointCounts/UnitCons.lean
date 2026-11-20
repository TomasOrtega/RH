import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowMulSelf

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

/- English proof (translation)
Establish `hP` using `Psi_upU w (upU_inv hU) (blk_inv w hU hB)`. Rewrite using `[Matrix.sub_apply]`. Break down `eq_or_lt_of_le hji with h | h` into its components or cases. Substitute `h` using the available equality. Rewrite using `[(hU _ _).2 rfl, (hP _ _).2 rfl, sub_self]`.

Rewrite using `[(hU _ _).1 h, (hP _ _).1 h, sub_self]`.
-/
theorem E_strict {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (i j : Fin (D.R.rS + 1)) (hji : j ≤ i) :
    (X - Psi w X⁻¹) i j = 0 := by
  have hP := Psi_upU w (upU_inv hU) (blk_inv w hU hB)
  rw [Matrix.sub_apply]
  rcases eq_or_lt_of_le hji with h | h
  · subst h; rw [(hU _ _).2 rfl, (hP _ _).2 rfl, sub_self]
  · rw [(hU _ _).1 h, (hP _ _).1 h, sub_self]

/- English proof (translation)
Establish `hXd : IsUnit X.det` using `by rw [upU_det hU]; exact isUnit_one`. Establish `hXi` using `upU_inv hU`. Establish `hBi` using `blk_inv w hU hB`. Establish `hGi` using `grD_inv hU hG`. Establish `hY` using `Psi_upU w hU hB`.

Establish `hGY` using `Psi_grD w δ M hA hB hG`. Establish `hPi : Psi w X⁻¹ = (Psi w X)⁻¹` using `Psi_inv w hXd`. Establish `hYd : IsUnit (Psi w X).det` using `by rw [upU_det hY]; exact isUnit_one`. Establish `hES` using `E_strict w hU hB`. Establish `hPE : Psi w (X - Psi w X⁻¹) = Psi w X * (X - Psi w X⁻¹) * X⁻¹`.

Rewrite using `[Psi_sub, Psi_Psi w hBi, hPi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hXd, Matrix.mul_nonsing_inv _ hYd, Matrix.one_mul]`. Establish `decomp : Psi w X * (X - Psi w X⁻¹) * X⁻¹ - (X - Psi w X⁻¹) = (Psi w X - 1) * (X - Psi w X⁻¹) * X⁻¹ + (X - Psi w X⁻¹) * (X⁻¹ - 1)`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[hPE, ← Matrix.sub_apply, decomp, Matrix.add_apply]`.

Establish `hac' : a.val < c.val` using `hac`. Use `(qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : a < i`. Establish `h1' : a.val < i.val` using `h1`. Distinguish the cases in `h2 : i < j`. Establish `h2' : i.val < j.val` using `h2`.

Distinguish the cases in `h3 : j ≤ c`. Establish `h3' : j.val ≤ c.val` using `h3`. Rewrite using `[show (Psi w X - 1) a i = Psi w X a i by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h1), sub_zero]]`. Establish `m1` using `hGY a i (le_of_lt h1)`. Establish `m2` using `hlow i j h2 (by omega)`.

Establish `m3` using `hGi j c h3`. Use `mem_qdPow_mul (mem_ddPow_mul_qd m1 m2) m3` as an intermediate fact. Rewrite `this` using `[show i.val - a.val + (j.val - i.val) + (c.val - j.val) = c.val - a.val by omega]`. Then use the resulting hypothesis. Rewrite using `[(hXi j c).1 (lt_of_not_ge h3), mul_zero]`. Conclude with `FractionalIdeal.zero_mem _`.

Rewrite using `[hES i j (not_lt.1 h2), mul_zero, zero_mul]`. Conclude with `FractionalIdeal.zero_mem _`. Establish `h0 : (Psi w X - 1) a i = 0`. Rewrite using `[Matrix.sub_apply]`. Break down `eq_or_lt_of_le (not_lt.1 h1) with h | h` into its components or cases.

Rewrite using `[h, (hY _ _).2 rfl, Matrix.one_apply_eq, sub_self]`. Rewrite using `[(hY _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]`. Rewrite using `[h0, zero_mul, zero_mul]`. Conclude with `FractionalIdeal.zero_mem _`. Rewrite using `[Matrix.mul_apply]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : a < j`. Establish `h1' : a.val < j.val` using `h1`. Distinguish the cases in `h2 : j < c`. Establish `h2' : j.val < c.val` using `h2`.

Rewrite using `[show (X⁻¹ - 1) j c = X⁻¹ j c by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h2), sub_zero]]`. Use `mem_qdPow_mul (hlow a j h1 (by omega)) (hGi j c (le_of_lt h2))` as an intermediate fact. Rewrite `this` using `[show j.val - a.val + (c.val - j.val) = c.val - a.val by omega]`. Then use the resulting hypothesis. Establish `h0 : (X⁻¹ - 1) j c = 0`. Rewrite using `[Matrix.sub_apply]`.

Break down `eq_or_lt_of_le (not_lt.1 h2) with h | h` into its components or cases. Rewrite using `[h, (hXi _ _).2 rfl, Matrix.one_apply_eq, sub_self]`. Rewrite using `[(hXi _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]`. Rewrite using `[h0, mul_zero]`. Conclude with `FractionalIdeal.zero_mem _`.

Rewrite using `[hES a j (not_lt.1 h1), zero_mul]`. Conclude with `FractionalIdeal.zero_mem _`.
-/
theorem unitCons (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (hG : GrD X)
    {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hlow : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val →
      (X - Psi w X⁻¹) i j ∈ qdPow D (j.val - i.val)) :
    Psi w (X - Psi w X⁻¹) a c - (X - Psi w X⁻¹) a c ∈ qdPow D (c.val - a.val) := by
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hXi := upU_inv hU
  have hBi := blk_inv w hU hB
  have hGi := grD_inv hU hG
  have hY := Psi_upU w hU hB
  have hGY := Psi_grD w δ M hA hB hG
  have hPi : Psi w X⁻¹ = (Psi w X)⁻¹ := Psi_inv w hXd
  have hYd : IsUnit (Psi w X).det := by rw [upU_det hY]; exact isUnit_one
  have hES := E_strict w hU hB
  have hPE : Psi w (X - Psi w X⁻¹) = Psi w X * (X - Psi w X⁻¹) * X⁻¹ := by
    rw [Psi_sub, Psi_Psi w hBi, hPi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hXd,
      Matrix.mul_nonsing_inv _ hYd, Matrix.one_mul]
  have decomp : Psi w X * (X - Psi w X⁻¹) * X⁻¹ - (X - Psi w X⁻¹) =
      (Psi w X - 1) * (X - Psi w X⁻¹) * X⁻¹ + (X - Psi w X⁻¹) * (X⁻¹ - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  rw [hPE, ← Matrix.sub_apply, decomp, Matrix.add_apply]
  have hac' : a.val < c.val := hac
  refine (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ?_ ?_
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h1 : a < i
    · have h1' : a.val < i.val := h1
      by_cases h2 : i < j
      · have h2' : i.val < j.val := h2
        by_cases h3 : j ≤ c
        · have h3' : j.val ≤ c.val := h3
          rw [show (Psi w X - 1) a i = Psi w X a i by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h1), sub_zero]]
          have m1 := hGY a i (le_of_lt h1)
          have m2 := hlow i j h2 (by omega)
          have m3 := hGi j c h3
          have := mem_qdPow_mul (mem_ddPow_mul_qd m1 m2) m3
          rwa [show i.val - a.val + (j.val - i.val) + (c.val - j.val) = c.val - a.val by omega] at this
        · rw [(hXi j c).1 (lt_of_not_ge h3), mul_zero]; exact FractionalIdeal.zero_mem _
      · rw [hES i j (not_lt.1 h2), mul_zero, zero_mul]; exact FractionalIdeal.zero_mem _
    · have h0 : (Psi w X - 1) a i = 0 := by
        rw [Matrix.sub_apply]
        rcases eq_or_lt_of_le (not_lt.1 h1) with h | h
        · rw [h, (hY _ _).2 rfl, Matrix.one_apply_eq, sub_self]
        · rw [(hY _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
      rw [h0, zero_mul, zero_mul]; exact FractionalIdeal.zero_mem _
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h1 : a < j
    · have h1' : a.val < j.val := h1
      by_cases h2 : j < c
      · have h2' : j.val < c.val := h2
        rw [show (X⁻¹ - 1) j c = X⁻¹ j c by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h2), sub_zero]]
        have := mem_qdPow_mul (hlow a j h1 (by omega)) (hGi j c (le_of_lt h2))
        rwa [show j.val - a.val + (c.val - j.val) = c.val - a.val by omega] at this
      · have h0 : (X⁻¹ - 1) j c = 0 := by
          rw [Matrix.sub_apply]
          rcases eq_or_lt_of_le (not_lt.1 h2) with h | h
          · rw [h, (hXi _ _).2 rfl, Matrix.one_apply_eq, sub_self]
          · rw [(hXi _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
        rw [h0, mul_zero]; exact FractionalIdeal.zero_mem _
    · rw [hES a j (not_lt.1 h1), zero_mul]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
