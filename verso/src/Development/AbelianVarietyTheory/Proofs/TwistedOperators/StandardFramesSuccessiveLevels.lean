import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatOStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatOStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.GoodFB

/- English proof (translation)
Introduce `i j` and use `by simp only [Matrix.mul_apply] exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)`.
-/
theorem mxAt_mul {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (b : Mx D n k) :
    MxAt P (a * b) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

/- English proof (translation)
Introduce `i j` and use `by simp only [Matrix.mul_apply] exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ha l j)`.
-/
theorem mxAt_mul_left {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (b : Mx D m n) {a : Mx D n k} (ha : MxAt P a) :
    MxAt P (b * a) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ha l j)

/- English proof (translation)
Introduce `D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv`. Establish `I` using `GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF`. Establish `t1` using `GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel D hQ T L μ0 hL sc G W M hM F hF (σ + 1) h v hv`. Establish `t2` using `GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv`. Establish `r1` using `GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv`.

Establish `r2` using `GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v`. Establish `r3` using `GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv`. Take `⟨-, hb, -⟩` from `I`. Establish `hbσ` using `hb σ h'`. Establish `hbσ1` using `hb (σ + 1) h`.

Use `⟨⟨?_, ?_, ?_, hbσ.1, (hbσ1.2.1 v).2, (hbσ.2.1 v).1, t1, t2⟩, ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(G.sp.V_is (2 * σ + 3) 0 (by omega) (by omega) (by omega)).sd`. Conclude with `(G.sp.P_is (2 * σ + 3) (by omega)).sd`. Conclude with `(G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (by omega)).sd`. Introduce `a ha`.

Conclude with `r1 _ (mxAt_mul ha _)`. Introduce `a ha`. Take `⟨⟨ε, hεε, -, hεi, -, hεoff⟩, -⟩` from `GlobalTheory.FinPl.localComponents D (· = v)`. Use `⟨ε • a, fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hεoff]`.

Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[mul_sub, ← mul_assoc, hεε, sub_self]`. Use `r2 ε hεi _ ha` as an intermediate fact. Establish `e : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (ε • a) = ε • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a`. Rewrite using `[HypDec.extX_apply, HypDec.extX_apply, Matrix.smul_mul]`.

Rewrite using `[e]`. Conclude with `this`. Introduce `ξ hξ`. Conclude with `r3 _ (mxAt_mul (mxAt_mul_left _ hξ) _)`.
-/
theorem goodAt_stdAt_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF
  have t1 := GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel D hQ T L μ0 hL sc G W M hM F hF (σ + 1) h v hv
  have t2 := GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have r1 := GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  have r2 := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v
  have r3 := GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  obtain ⟨-, hb, -⟩ := I
  have hbσ := hb σ h'
  have hbσ1 := hb (σ + 1) h
  refine ⟨⟨?_, ?_, ?_, hbσ.1, (hbσ1.2.1 v).2, (hbσ.2.1 v).1, t1, t2⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (G.sp.V_is (2 * σ + 3) 0 (by omega) (by omega) (by omega)).sd
  · exact (G.sp.P_is (2 * σ + 3) (by omega)).sd
  · exact (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (by omega)).sd
  · intro a ha
    exact r1 _ (mxAt_mul ha _)
  · intro a ha
    obtain ⟨⟨ε, hεε, -, hεi, -, hεoff⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = v)
    refine ⟨ε • a, fun i j => ?_, ?_⟩
    · rw [hεoff]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub, ← mul_assoc, hεε, sub_self]
    · have := r2 ε hεi _ ha
      have e : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (ε • a) =
          ε • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a := by
        rw [HypDec.extX_apply, HypDec.extX_apply, Matrix.smul_mul]
      rw [e]
      exact this
  · intro ξ hξ
    exact r3 _ (mxAt_mul (mxAt_mul_left _ hξ) _)

end GlobalTheory.AscFin.GoodFB
