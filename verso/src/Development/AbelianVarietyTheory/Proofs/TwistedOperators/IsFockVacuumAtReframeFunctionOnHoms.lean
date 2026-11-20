import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.FockVac

variable {D : D7}

/- English proof (translation)
Unfold `reW`. Conclude with `Continuous.matrix_mul continuous_id continuous_const`.
-/
theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Continuous (reW S T b) := by
  unfold reW
  exact Continuous.matrix_mul continuous_id continuous_const

/- English proof (translation)
Unfold `compAt`. Rewrite using `[Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `e`. Conclude with `GlobalTheory.FockCompare.comp_incA hθ τ e`.
-/
theorem compAt_frPinv {θ : InfFam D} (hθ : IsInfFam θ) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) : compAt θ τ ((frPinv S b).map (incA D)) = (frPinv S b).map (tauE D τ) := by
  unfold compAt
  rw [Matrix.map_map]
  congr 1
  funext e
  exact GlobalTheory.FockCompare.comp_incA hθ τ e

/- English proof (translation)
Establish `hL` using `GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z`. Set `L : ℝ →+ WO S T` to `(reWHom S T b).comp (lineAt θ τ z)`. Establish `hL' : IsLineAt θ τ (z * (frPinv S b).map (tauE D τ)) L`. Use `⟨(continuous_reW S T b).comp hL.1, fun t => ?_, fun t τ' => ?_⟩` and prove the remaining obligations. Use `show (reW S T b (lineAt θ τ z t)).map (finPart D) = 0`.

Unfold `reW`. Rewrite using `[Matrix.map_mul, hL.2.1, Matrix.zero_mul]`. Use `show compAt θ τ' (reW S T b (lineAt θ τ z t)) = _`. Unfold `reW`. Rewrite using `[GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_frPinv hθ]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Matrix.smul_mul]`. Rewrite using `[Matrix.zero_mul]`. Rewrite using `[GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']`.

Both sides reduce to the same expression.
-/
theorem lineAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) = lineAt θ τ (z * (frPinv S b).map (tauE D τ)) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T := (reWHom S T b).comp (lineAt θ τ z)
  have hL' : IsLineAt θ τ (z * (frPinv S b).map (tauE D τ)) L := by
    refine ⟨(continuous_reW S T b).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (reW S T b (lineAt θ τ z t)).map (finPart D) = 0
      unfold reW
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (reW S T b (lineAt θ τ z t)) = _
      unfold reW
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_frPinv hθ]
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

/- English proof (translation)
The claim follows from `lineAt_reW hθ S T b τ z t`.
-/
theorem lineAt_reW' {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) =
      lineAt θ τ (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) t :=
  lineAt_reW hθ S T b τ z t

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[reF_apply]`. Unfold `Formalism.IndefR.Datum.dRho`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Rewrite using `[heisO_reF S T b ψ hs, reF_apply, lineAt_reW' hθ]`.
-/
theorem dRho_reF (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (hs : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (reS S b) T) θ τ z (reF S T b f) =
      reF S T b (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) f) := by
  funext x
  rw [reF_apply]
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [heisO_reF S T b ψ hs, reF_apply, lineAt_reW' hθ]

/- English proof (translation)
Introduce `D ψ θ S T b hθ hs τ sT f hf z`. Set `P' : Matrix (Fin S.rank) (Fin S.rank) ℂ` to `(frPinv S b).map (tauE D τ)`. Set `z' : Matrix (Fin T.rank) (Fin S.rank) ℂ` to `z`. Establish `hJ : HMul.hMul (α` using `Matrix (Fin T.rank) (Fin S.rank) ℂ) (cplxO 1 sT z) P' = cplxO 1 sT (z' * P') := by show Complex.I • (sT * z' * 1) * P' = Complex.I • (sT * (z' * P') * 1)`. Rewrite using `[Matrix.mul_one, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]`.

Use function extensionality and compare the values at `x`. Establish `h0 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z' * P') f (reW S T b x) + Complex.I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 sT (z' * P')) f (reW S T b x) = 0` using `congrFun (hf (z' * P')) (reW S T b x)`. Rewrite `h0` using `[← hJ]`. Establish `e1` using `congrFun (dRho_reF ψ hθ S T b hs τ z f) x`. Establish `e2` using `congrFun (dRho_reF ψ hθ S T b hs τ (cplxO 1 sT z) f) x`.

Use `(congrArg₂ (fun a c : ℂ => a + Complex.I • c) e1 e2).trans ?_` and prove the remaining obligations. Conclude with `h0`.
-/
theorem isFockVacAt_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ →
    (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) →
    ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
      IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := by
  intro D ψ θ S T b hθ hs τ sT f hf z
  let P' : Matrix (Fin S.rank) (Fin S.rank) ℂ := (frPinv S b).map (tauE D τ)
  let z' : Matrix (Fin T.rank) (Fin S.rank) ℂ := z
  have hJ : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) (cplxO 1 sT z) P' = cplxO 1 sT (z' * P') := by
    show Complex.I • (sT * z' * 1) * P' = Complex.I • (sT * (z' * P') * 1)
    rw [Matrix.mul_one, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  funext x
  have h0 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z' * P') f (reW S T b x) +
      Complex.I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 sT (z' * P')) f (reW S T b x) = 0 :=
    congrFun (hf (z' * P')) (reW S T b x)
  rw [← hJ] at h0
  have e1 := congrFun (dRho_reF ψ hθ S T b hs τ z f) x
  have e2 := congrFun (dRho_reF ψ hθ S T b hs τ (cplxO 1 sT z) f) x
  refine (congrArg₂ (fun a c : ℂ => a + Complex.I • c) e1 e2).trans ?_
  exact h0

end GlobalTheory.AdSpan.ReVec.FockVac

end
