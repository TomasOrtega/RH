import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeightsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometryStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

/- English proof (translation)
Take `⟨a, ha⟩ : Even (R.N j)` from `R.k_even.add (R.t_odd.add_one.mul_left j)`. Establish `h1 : R.N j / 2 = a` using `by omega`. Rewrite using `[h1, ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem half_rank_cast (R : Ranks) (j : ℕ) : (((R.N j / 2 : ℕ) : ℤ) : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ : Even (R.N j) := R.k_even.add (R.t_odd.add_one.mul_left j)
  have h1 : R.N j / 2 = a := by omega
  rw [h1, ha]
  push_cast
  ring

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La'`. Establish `hjm : j < D.R.m` using `hj`. Establish `hW` using `(GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hjm ⟨La'.1⟩).dv`. Apply the tactic sequence `obtain ⟨e, he, hmu⟩ := GlobalTheory.T.stepCharacter_det_rationalIsometry S j hjm`. Establish `hG` using `GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S (j + 1) hj`.

Use `set γ := d.gam (j + 1) hj La' with hγ`. Establish `hmem : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj)` using `d.mem (j + 1) hj La'`. Establish `hmuγ` using `hmu (j + 1) hj γ hmem`. Establish `hgd` using `(hG.2 γ hmem).1`. Establish `hq0 : (gMat J (j + 1) hj 1).det ≠ 0` using `left_ne_zero_of_mul_eq_one hG.1`.

Establish `hdm : (mM d (j + 1) hj La').1.det * γ.1.det = (uB J (j + 1) hj La'.1).1.det`. Establish `h1 : (γ⁻¹).1.det * γ.1.det = 1`. Rewrite using `[← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]`. Simplify using `only [mM, uB, Units.val_mul, Matrix.det_mul]`. Take the linear combination `((J.A.crd (j + 1) hj).1.det * (bAt J (j + 1) hj La'.1).1.det) * h1`.

Establish `hsd : ∀ τ, (D.chTw u μ).sDiv j τ = e τ - ((D.R.N j / 2 : ℕ) : ℤ)` using `fun τ => by`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Rewrite using `[(D.chTw u μ).sDiv_eq j hjm τ, Int.cast_sub, D.hcW_e, he τ, half_rank_cast]`. Simplify using `only [sExp, Nat.add_sub_cancel]`. Simplify using `only [dPow, sPt, Dec.uT, dif_pos hj, kT, hW, hsd]`.

Rewrite using `[← hγ, hmuγ, hgd]`. Establish `hP : ∀ τ x, TaylorLogMetric.embT D τ x = embT D τ x` using `fun _ _ => rfl`. Simplify using `only [hP, map_mul]`. Rewrite using `[← Finset.prod_zpow]`. Establish `hb : ∀ τ, embT D τ (uB J (j + 1) hj La'.1).1.det ≠ 0` using `fun τ => by`.

Rewrite using `[map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Units.ne_zero _`. Establish `hg0 : ∀ τ, embT D τ γ.1.det ≠ 0` using `fun τ => by`. Rewrite using `[map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Units.ne_zero _`.

Establish `hq : ∀ τ, embT D τ (gMat J (j + 1) hj 1).det ≠ 0` using `fun τ => by`. Rewrite using `[map_ne_zero]`. Conclude with `hq0`. Establish `hm : ∀ τ, embT D τ (mM d (j + 1) hj La').1.det = embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det` using `fun τ => by`. Rewrite using `[eq_div_iff (hg0 τ), ← map_mul, hdm]`.

Simplify using `only [hm]`. Use `set n : ℤ := ((D.R.N j / 2 : ℕ) : ℤ)`. Use `set c : ℤ := cTw D (j + 1)`. Establish `key : ∀ τ, (embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det) ^ (-(e τ - n - c)) * embT D τ (uB J (j + 1) hj La'.1).1.det ^ (-c) = embT D τ γ.1.det ^ e τ * (embT D τ γ.1.det * embT D τ (gMat J (j + 1) hj 1).det) ^ (-(n + c)) * (embT D τ (uB J (j + 1) hj La'.1).1.det ^ (- …` using `fun τ => by`. Establish `h1` using `hb τ`.

Establish `h2` using `hg0 τ`. Establish `h3` using `hq τ`. Simplify using `only [div_zpow, mul_zpow, zpow_neg, zpow_sub₀ h1, zpow_sub₀ h2, zpow_add₀ h1, zpow_add₀ h2, zpow_add₀ h3]`. Clear the denominators using the available nonvanishing facts. Establish `hprod` using `Finset.prod_congr rfl (fun τ (_ : τ ∈ Finset.univ) => key τ)`.

Simplify using `only [Finset.prod_mul_distrib] at hprod`. Take the linear combination `(d.chi (j + 1) hj La' * ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ c) * hprod`.
-/
theorem target_scalar : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La' : (sysS H X std).Lt (j + 1)),
      dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d (j + 1) hj La' =
        d.uT S j La' * kT J j hj La'.1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La'
  have hjm : j < D.R.m := hj
  have hW := (GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hjm ⟨La'.1⟩).dv
  obtain ⟨e, he, hmu⟩ := GlobalTheory.T.stepCharacter_det_rationalIsometry S j hjm
  have hG := GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S (j + 1) hj
  set γ := d.gam (j + 1) hj La' with hγ
  have hmem : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) := d.mem (j + 1) hj La'
  have hmuγ := hmu (j + 1) hj γ hmem
  have hgd := (hG.2 γ hmem).1
  have hq0 : (gMat J (j + 1) hj 1).det ≠ 0 := left_ne_zero_of_mul_eq_one hG.1
  have hdm : (mM d (j + 1) hj La').1.det * γ.1.det = (uB J (j + 1) hj La'.1).1.det := by
    have h1 : (γ⁻¹).1.det * γ.1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    simp only [mM, uB, Units.val_mul, Matrix.det_mul]
    linear_combination ((J.A.crd (j + 1) hj).1.det * (bAt J (j + 1) hj La'.1).1.det) * h1
  have hsd : ∀ τ, (D.chTw u μ).sDiv j τ = e τ - ((D.R.N j / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [(D.chTw u μ).sDiv_eq j hjm τ, Int.cast_sub, D.hcW_e, he τ, half_rank_cast]
    simp only [sExp, Nat.add_sub_cancel]
  simp only [dPow, sPt, Dec.uT, dif_pos hj, kT, hW, hsd]
  rw [← hγ, hmuγ, hgd]
  have hP : ∀ τ x, TaylorLogMetric.embT D τ x = embT D τ x := fun _ _ => rfl
  simp only [hP, map_mul]
  rw [← Finset.prod_zpow]
  have hb : ∀ τ, embT D τ (uB J (j + 1) hj La'.1).1.det ≠ 0 := fun τ => by
    rw [map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hg0 : ∀ τ, embT D τ γ.1.det ≠ 0 := fun τ => by
    rw [map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hq : ∀ τ, embT D τ (gMat J (j + 1) hj 1).det ≠ 0 := fun τ => by
    rw [map_ne_zero]
    exact hq0
  have hm : ∀ τ, embT D τ (mM d (j + 1) hj La').1.det = embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det := fun τ => by
    rw [eq_div_iff (hg0 τ), ← map_mul, hdm]
  simp only [hm]
  set n : ℤ := ((D.R.N j / 2 : ℕ) : ℤ)
  set c : ℤ := cTw D (j + 1)
  have key : ∀ τ, (embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det) ^ (-(e τ - n - c)) *
      embT D τ (uB J (j + 1) hj La'.1).1.det ^ (-c) =
      embT D τ γ.1.det ^ e τ * (embT D τ γ.1.det * embT D τ (gMat J (j + 1) hj 1).det) ^ (-(n + c)) *
        (embT D τ (uB J (j + 1) hj La'.1).1.det ^ (-(e τ - n)) * embT D τ (gMat J (j + 1) hj 1).det ^ (n + c)) := fun τ => by
    have h1 := hb τ
    have h2 := hg0 τ
    have h3 := hq τ
    simp only [div_zpow, mul_zpow, zpow_neg, zpow_sub₀ h1, zpow_sub₀ h2, zpow_add₀ h1, zpow_add₀ h2, zpow_add₀ h3]
    field_simp
  have hprod := Finset.prod_congr rfl (fun τ (_ : τ ∈ Finset.univ) => key τ)
  simp only [Finset.prod_mul_distrib] at hprod
  linear_combination (d.chi (j + 1) hj La' * ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ c) * hprod

end GlobalTheory.TwV.DelA
