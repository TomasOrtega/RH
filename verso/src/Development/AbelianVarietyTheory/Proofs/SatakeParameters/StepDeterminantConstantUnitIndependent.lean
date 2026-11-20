import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSiteStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOneStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a a'`. Establish `hB` using `GlobalTheory.T.orthonormalChartBasis_det_norm_one S hPos ι hι`. Establish `hG` using `GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι`. Establish `hD` using `GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S`. Establish `hL` using `GlobalTheory.T.norm_site_coordinate_scale_eq_one S`.

Establish `hN` using `GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one S hPos ι hι`. Establish `hBas` using `bAt_orth_lev S`. Use `beta_reduce at hD hL hBas`. Establish `hdPow : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (e : D.what₂.Tau → ℤ), (∀ τ, ‖ι (embT D τ M.det)‖ = 1) → ‖ι (dPow M e)‖ = 1`. Introduce `n M e hM`.

Unfold `dPow`. Rewrite using `[map_prod, norm_prod]`. Conclude with `Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hM τ, one_zpow])`. Establish `hdPowC : ∀ (k : ℕ) (hk : k ≤ D.R.m) (c : ℤ), ‖ι (dPow (gMat J k hk 1) (fun _ => c))‖ = 1`. Introduce `k hk c`.

Unfold `dPow`. Rewrite using `[Finset.prod_zpow, map_zpow₀, norm_zpow]`. Rewrite using `[show (∏ τ, embT D τ (gMat J k hk 1).det) = ∏ τ, TaylorLogMetric.embT D τ (gMat J k hk 1).det from rfl]`. Rewrite using `[hN _ (hD k hk).1, one_zpow]`. Establish `hsg : ∀ n, ‖ι (sgRev n)‖ = 1`.

Introduce `n`. Unfold `sgRev`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]`. Establish `hcOp : ‖ι (cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1`. Establish `h1 : ‖ι (sgO (sysS H X std) D (hT.gat_pos u w hg) j)‖ = 1`.

Unfold `sgO`. Rewrite using `[map_prod, norm_prod]`. Use `Finset.prod_eq_one (fun τ _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Simplify using `[hsg]`.

Simplify using the standard rewrite rules. Establish `h2 : ‖ι (∏ τ, (t.O u μ).dgen τ ^ (-(szT (sysS H X std) D (hT.gat_pos u w hg) j τ)))‖ = 1`. Rewrite using `[map_prod, norm_prod]`. Conclude with `Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hG τ, one_zpow])`. Unfold `cOp`.

Rewrite using `[map_mul, norm_mul, h1, h2, one_mul]`. Establish `hkS : ∀ b : Lv.comp j, ‖ι (kS J j (Nat.le_of_succ_le hj) b)‖ = 1`. Introduce `b`. Unfold `kS`. Rewrite using `[map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]`.

Establish `hkT : ∀ b : Lv.comp (j + 1), ‖ι (kT J j hj b)‖ = 1`. Introduce `b`. Unfold `kT`. Rewrite using `[map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]`. Establish `hkSc : ∀ b : Lv.comp j, ‖ι (kS J j (Nat.le_of_succ_le hj) b * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1`.

Introduce `b`. Rewrite using `[map_mul, norm_mul, hkS, hcOp, one_mul]`. Establish `hkSeq : ∀ b : Lv.comp j, kS J j (Nat.le_of_succ_le hj) b = kS J j (Nat.le_of_succ_le hj) a`. Introduce `b`. Simplify using `only [kS, uB, (hBas j (Nat.le_of_succ_le hj) a).2 b]`.

Establish `hkTeq : ∀ b : Lv.comp (j + 1), kT J j hj b = kT J j hj a'`. Introduce `b`. Simplify using `only [kT, uB, (hBas (j + 1) hj a').2 b]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `cKs`.

Rewrite using `[norm_mul, norm_zpow, hL, one_zpow, mul_one, map_mul, norm_mul, map_inv₀, norm_inv, hkT, hkSc, inv_one, mul_one]`. Introduce `h`. Establish `h1` using `hkSc a`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.

Introduce `b b'`. Unfold `cKs`. Rewrite using `[hkSeq b, hkTeq b']`.
-/
theorem cKs_unit_indep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a a'
  have hB := GlobalTheory.T.orthonormalChartBasis_det_norm_one S hPos ι hι
  have hG := GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι
  have hD := GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S
  have hL := GlobalTheory.T.norm_site_coordinate_scale_eq_one S
  have hN := GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one S hPos ι hι
  have hBas := bAt_orth_lev S
  beta_reduce at hD hL hBas
  have hdPow : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (e : D.what₂.Tau → ℤ),
      (∀ τ, ‖ι (embT D τ M.det)‖ = 1) → ‖ι (dPow M e)‖ = 1 := by
    intro n M e hM
    unfold dPow
    rw [map_prod, norm_prod]
    exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hM τ, one_zpow])
  have hdPowC : ∀ (k : ℕ) (hk : k ≤ D.R.m) (c : ℤ), ‖ι (dPow (gMat J k hk 1) (fun _ => c))‖ = 1 := by
    intro k hk c
    unfold dPow
    rw [Finset.prod_zpow, map_zpow₀, norm_zpow]
    rw [show (∏ τ, embT D τ (gMat J k hk 1).det) = ∏ τ, TaylorLogMetric.embT D τ (gMat J k hk 1).det from rfl]
    rw [hN _ (hD k hk).1, one_zpow]
  have hsg : ∀ n, ‖ι (sgRev n)‖ = 1 := by
    intro n
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]
  have hcOp : ‖ι (cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    have h1 : ‖ι (sgO (sysS H X std) D (hT.gat_pos u w hg) j)‖ = 1 := by
      unfold sgO
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one (fun τ _ => ?_)
      split_ifs
      · simp [hsg]
      · simp
    have h2 : ‖ι (∏ τ, (t.O u μ).dgen τ ^ (-(szT (sysS H X std) D (hT.gat_pos u w hg) j τ)))‖ = 1 := by
      rw [map_prod, norm_prod]
      exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hG τ, one_zpow])
    unfold cOp
    rw [map_mul, norm_mul, h1, h2, one_mul]
  have hkS : ∀ b : Lv.comp j, ‖ι (kS J j (Nat.le_of_succ_le hj) b)‖ = 1 := by
    intro b
    unfold kS
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkT : ∀ b : Lv.comp (j + 1), ‖ι (kT J j hj b)‖ = 1 := by
    intro b
    unfold kT
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkSc : ∀ b : Lv.comp j,
      ‖ι (kS J j (Nat.le_of_succ_le hj) b * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    intro b
    rw [map_mul, norm_mul, hkS, hcOp, one_mul]
  have hkSeq : ∀ b : Lv.comp j, kS J j (Nat.le_of_succ_le hj) b = kS J j (Nat.le_of_succ_le hj) a := by
    intro b
    simp only [kS, uB, (hBas j (Nat.le_of_succ_le hj) a).2 b]
  have hkTeq : ∀ b : Lv.comp (j + 1), kT J j hj b = kT J j hj a' := by
    intro b
    simp only [kT, uB, (hBas (j + 1) hj a').2 b]
  refine ⟨?_, ?_, ?_⟩
  · unfold cKs
    rw [norm_mul, norm_zpow, hL, one_zpow, mul_one, map_mul, norm_mul, map_inv₀, norm_inv, hkT, hkSc, inv_one, mul_one]
  · intro h
    have h1 := hkSc a
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  · intro b b'
    unfold cKs
    rw [hkSeq b, hkTeq b']

end GlobalTheory.TwV.DelA
