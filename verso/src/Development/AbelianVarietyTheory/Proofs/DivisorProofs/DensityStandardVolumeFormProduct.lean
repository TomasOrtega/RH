import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensMulPullHeadL

set_option autoImplicit false

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

namespace GlobalTheory.BcUnique.DensPull

open GlobalTheory.LocFub GlobalTheory.LocFub.TopDens

noncomputable def rho : Alt (1 + 1) →ₐ[ℂ] Alt (1 + 1) := (pull (headL 1)).comp (pull headIn)

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(pull_dz _ _).1, Fin.sum_univ_one, headIn_apply, appendV_zero]`. Simplify using `[GlobalTheory.GoodMetric.coordVec]`. Rewrite using `[(pull_dz _ _).2, Fin.sum_univ_one, headIn_apply, appendV_zero]`. Simplify using `[GlobalTheory.GoodMetric.coordVec]`.

Rewrite using `[(pull_dz _ _).1, Fin.sum_univ_one, headIn_apply, appendV_last]`. Simplify using the standard rewrite rules. Rewrite using `[(pull_dz _ _).2, Fin.sum_univ_one, headIn_apply, appendV_last]`. Simplify using the standard rewrite rules.
-/
theorem pull_headIn_dz : pull headIn (dz (0 : Fin (1 + 1))) = dz 0 ∧ pull headIn (dzb (0 : Fin (1 + 1))) = dzb 0 ∧
    pull headIn (dz (Fin.last 1)) = 0 ∧ pull headIn (dzb (Fin.last 1)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(pull_dz _ _).1, Fin.sum_univ_one, headIn_apply, appendV_zero]
    simp [GlobalTheory.GoodMetric.coordVec]
  · rw [(pull_dz _ _).2, Fin.sum_univ_one, headIn_apply, appendV_zero]
    simp [GlobalTheory.GoodMetric.coordVec]
  · rw [(pull_dz _ _).1, Fin.sum_univ_one, headIn_apply, appendV_last]
    simp
  · rw [(pull_dz _ _).2, Fin.sum_univ_one, headIn_apply, appendV_last]
    simp

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `pull_headIn_dz`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rho, AlgHom.comp_apply, h1, (pull_headL_dz _).1]`. Both sides reduce to the same expression. Rewrite using `[rho, AlgHom.comp_apply, h2, (pull_headL_dz _).2]`.

Both sides reduce to the same expression. Rewrite using `[rho, AlgHom.comp_apply, h3, map_zero]`. Rewrite using `[rho, AlgHom.comp_apply, h4, map_zero]`.
-/
theorem rho_dz : rho (dz 0) = dz 0 ∧ rho (dzb 0) = dzb 0 ∧ rho (dz (Fin.last 1)) = 0 ∧ rho (dzb (Fin.last 1)) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := pull_headIn_dz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rho, AlgHom.comp_apply, h1, (pull_headL_dz _).1]; rfl
  · rw [rho, AlgHom.comp_apply, h2, (pull_headL_dz _).2]; rfl
  · rw [rho, AlgHom.comp_apply, h3, map_zero]
  · rw [rho, AlgHom.comp_apply, h4, map_zero]

noncomputable def wl : Alt (1 + 1) := dz (Fin.last 1) * dzb (Fin.last 1)

/- English proof (translation)
The claim follows from `Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center _ _) b`.
-/
theorem wl_central (b : Alt (1 + 1)) : b * wl = wl * b :=
  Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center _ _) b

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← wl_central, wl, ← mul_assoc, dz, ExteriorAlgebra.ι_sq_zero, zero_mul]`. Rewrite using `[wl, mul_assoc, dzb, ExteriorAlgebra.ι_sq_zero, mul_zero]`.
-/
theorem wl_mul_dz : wl * dz (Fin.last 1) = 0 ∧ wl * dzb (Fin.last 1) = 0 := by
  constructor
  · rw [← wl_central, wl, ← mul_assoc, dz, ExteriorAlgebra.ι_sq_zero, zero_mul]
  · rw [wl, mul_assoc, dzb, ExteriorAlgebra.ι_sq_zero, mul_zero]

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `rho_dz`. Take `⟨w1, w2⟩` from `wl_mul_dz`. Establish `hx : x = x (Sum.inl 0) • Pi.single (Sum.inl 0) 1 + x (Sum.inl (Fin.last 1)) • Pi.single (Sum.inl (Fin.last 1)) 1 + x (Sum.inr 0) • Pi.single (Sum.inr 0) 1 + x (Sum.inr (Fin.last 1)) • Pi.single (Sum.inr (Fin.last 1)) 1`. Apply the tactic sequence `ext (i | i) <;> fin_cases i <;> simp`. Rewrite using `[hx]`.

Simplify using `only [map_add, map_smul, mul_add, mul_smul_comm]`. Establish `d0 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inl (0 : Fin (1 + 1))) 1) = dz 0` using `rfl`. Establish `d1 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inl (Fin.last 1)) 1) = dz (Fin.last 1)` using `rfl`. Establish `b0 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inr (0 : Fin (1 + 1))) 1) = dzb 0` using `rfl`. Establish `b1 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inr (Fin.last 1)) 1) = dzb (Fin.last 1)` using `rfl`.

Rewrite using `[d0, d1, b0, b1, h1, h2, h3, h4, w1, w2]`. Simplify using the standard rewrite rules.
-/
theorem wl_mul_ι (x : Fin (1 + 1) ⊕ Fin (1 + 1) → ℂ) : wl * ExteriorAlgebra.ι ℂ x = wl * rho (ExteriorAlgebra.ι ℂ x) := by
  obtain ⟨h1, h2, h3, h4⟩ := rho_dz
  obtain ⟨w1, w2⟩ := wl_mul_dz
  have hx : x = x (Sum.inl 0) • Pi.single (Sum.inl 0) 1 + x (Sum.inl (Fin.last 1)) • Pi.single (Sum.inl (Fin.last 1)) 1 +
      x (Sum.inr 0) • Pi.single (Sum.inr 0) 1 + x (Sum.inr (Fin.last 1)) • Pi.single (Sum.inr (Fin.last 1)) 1 := by
    ext (i | i) <;> fin_cases i <;> simp
  rw [hx]
  simp only [map_add, map_smul, mul_add, mul_smul_comm]
  have d0 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inl (0 : Fin (1 + 1))) 1) = dz 0 := rfl
  have d1 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inl (Fin.last 1)) 1) = dz (Fin.last 1) := rfl
  have b0 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inr (0 : Fin (1 + 1))) 1) = dzb 0 := rfl
  have b1 : ExteriorAlgebra.ι ℂ (Pi.single (Sum.inr (Fin.last 1)) 1) = dzb (Fin.last 1) := rfl
  rw [d0, d1, b0, b1, h1, h2, h3, h4, w1, w2]
  simp

/- English proof (translation)
Proceed by induction on `a using ExteriorAlgebra.induction with`. Consider the case `algebraMap r => rw [AlgHom.commutes]`. Consider the case `ι x => exact wl_mul_ι x`. Consider the case `mul a b ha hb`. Rewrite using `[map_mul, ← mul_assoc, ha, ← wl_central, mul_assoc, hb, ← mul_assoc, wl_central, mul_assoc]`.

Consider the case `add a b ha hb => rw [map_add, mul_add, mul_add, ha, hb]`.
-/
theorem wl_mul_rho (a : Alt (1 + 1)) : wl * a = wl * rho a := by
  induction a using ExteriorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]
  | ι x => exact wl_mul_ι x
  | mul a b ha hb =>
    rw [map_mul, ← mul_assoc, ha, ← wl_central, mul_assoc, hb, ← mul_assoc, wl_central, mul_assoc]
  | add a b ha hb => rw [map_add, mul_add, mul_add, ha, hb]

/- English proof (translation)
Establish `e1 : (Complex.I / 2) • (dz 0 * dzb 0 : Alt 1) = (vol 1 : Alt 1)`. Rewrite using `[vol, Fin.prod_univ_one]`. Both sides reduce to the same expression. Establish `e2 : (Complex.I / 2) * dens (dz 0 * dzb 0 : Alt 1) = 1`. Rewrite using `[← dens_smul, e1, dens_vol]`.

Rewrite using `[smul_mul_assoc, dens_smul, ← wl, wl_mul_rho, wl, rho, AlgHom.comp_apply, dens_gen, map_mul, pull_fibL_last.1, pull_fibL_last.2, ← mul_assoc, e2, one_mul]`.
-/
theorem dens_mul_eq_dens_pull (a : Alt (1 + 1)) :
    dens (((Complex.I / 2) • (dz (Fin.last 1) * dzb (Fin.last 1))) * a) = dens (pull headIn a) := by
  have e1 : (Complex.I / 2) • (dz 0 * dzb 0 : Alt 1) = (vol 1 : Alt 1) := by
    rw [vol, Fin.prod_univ_one]; rfl
  have e2 : (Complex.I / 2) * dens (dz 0 * dzb 0 : Alt 1) = 1 := by
    rw [← dens_smul, e1, dens_vol]
  rw [smul_mul_assoc, dens_smul, ← wl, wl_mul_rho, wl, rho, AlgHom.comp_apply, dens_gen, map_mul, pull_fibL_last.1,
    pull_fibL_last.2, ← mul_assoc, e2, one_mul]

end GlobalTheory.BcUnique.DensPull
