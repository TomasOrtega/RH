import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGauge
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntMulOfCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTrCalc

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
Simplify using `only [NF.dZb]`. Rewrite using `[show (fun x => f x - g x) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]`. Simplify using `only [ContinuousLinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dZb_sub {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    NF.dZb (fun x => f x - g x) w = NF.dZb f w - NF.dZb g w := by
  simp only [NF.dZb]
  rw [show (fun x => f x - g x) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/- English proof (translation)
Establish `hev : (MA.DQ P).ev M.vz 1 = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Use `show MA.coordE M.vz q.1 * MA.wirt M.vz (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0`. Establish `hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ)` using `by filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx`.

Simplify using `[MA.ext, hx]`. Simplify using `[MA.wirt, hloc.fderiv_eq]`. Simplify using `only [dzQ, MA.DAlg.dzP, MA.DAlg.mkP]`. Use `show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0`. Rewrite using `[hev, map_zero]`.
-/
theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vz 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vz q.1 * MA.wirt M.vz (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzQ, MA.DAlg.dzP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [hev, map_zero]

/- English proof (translation)
Establish `hev : (MA.DQ P).ev M.vzb 1 = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Use `show MA.coordE M.vzb q.1 * MA.wirt M.vzb (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0`. Establish `hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ)` using `by filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx`.

Simplify using `[MA.ext, hx]`. Simplify using `[MA.wirt, hloc.fderiv_eq]`. Simplify using `only [dzbQ, MA.DAlg.dzbP, MA.DAlg.mkP]`. Use `show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0`. Rewrite using `[hev, map_zero]`.
-/
theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vzb 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vzb q.1 * MA.wirt M.vzb (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzbQ, MA.DAlg.dzbP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [hev, map_zero]

/- English proof (translation)
Simplify using `only [MA.actA, MA.ggiA, MA.sc, mulQ, Matrix.scalar_apply]`. Use `(Finset.sum_eq_single ρ ?_ ?_).trans ?_` and prove the remaining obligations. Introduce `b _ hb`. Simplify using `[Matrix.diagonal, Ne.symm hb]`. Both sides reduce to the same expression.

Introduce `h`. Conclude with `absurd (Finset.mem_univ ρ) h`. Simplify using `[Matrix.diagonal]`. Both sides reduce to the same expression.
-/
theorem actA_ggiA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.ggiA P (MA.DQ P)) g ρ = mulQ P ((MA.DQ P).ggiP P.TT) (g ρ) := by
  simp only [MA.actA, MA.ggiA, MA.sc, mulQ, Matrix.scalar_apply]
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    simp [Matrix.diagonal, Ne.symm hb]
    rfl
  · intro h
    exact absurd (Finset.mem_univ ρ) h
  · simp [Matrix.diagonal]
    rfl

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hK A B hAB hC hBA hcurv ρ ζ hζ`. Establish `hTT : 0 ≤ P.TT` using `tt_nonneg_of_hyp hyp`. Establish `hev : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT), ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q` using `fun Φ σ q => SSTr.trR_apply P Bs hyp.1 hyp.2.1 e he Φ σ q`. Establish `tsub : ∀ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT), ((trR P Bs e (Φ - Ψ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - ((trR P Bs e Ψ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q`. Introduce `Φ Ψ σ q`.

Rewrite using `[hev, hev, hev, Submodule.coe_sub, sub_eq_add_neg, ← neg_one_smul ℂ (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), VLem.rawR_add, VLem.rawR_smul]`. Simplify using `[sub_eq_add_neg]`. Establish `tsmul : ∀ (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT), ((trR P Bs e (c • Φ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = c * ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q`. Introduce `c Φ σ q`. Rewrite using `[hev, hev, Submodule.coe_smul, VLem.rawR_smul]`.

Both sides reduce to the same expression. Take `⟨Φ₀, hΦ₀, -⟩` from `SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))`. Establish `hAs` using `(hAB ρ).1`. Establish `hBs` using `(hAB ρ).2`. Establish `hΨ : trR P Bs e ((d.κ (dTy P ρ)).1 Φ₀) ρ = 1`.

Rewrite using `[hK, actA_kap, hΦ₀]`. Simplify using `[dTy]`. Establish `hN : trR P Bs e (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (A ρ)`. Rewrite using `[(hC _ ρ).1, hΨ, dzQ_one P hTT, zero_add, mul_one]`. Establish `hS : trR P Bs e (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (B ρ)`.

Rewrite using `[(hC _ ρ).2, hΨ, dzbQ_one P hTT, neg_zero, zero_add, mul_one]`. Establish `hSN : trR P Bs e (d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ = -dzbQ P (fnZ P (A ρ)) + fnZ P (B ρ) * fnZ P (A ρ)`. Rewrite using `[(hC _ ρ).2, hN]`. Establish `hNS : trR P Bs e (d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ = dzQ P (fnZ P (B ρ)) + fnZ P (A ρ) * fnZ P (B ρ)`. Rewrite using `[(hC _ ρ).1, hS]`.

Establish `hG : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e (d.L.GGi.1 Φ) ρ = mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ)`. Introduce `Φ`. Rewrite using `[((GT.gauge_function_holds Wp Wq P Bs X d hyp e) Φ).2.2.2.2.2, actA_ggiA]`. Establish `hc' : d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) - d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) = ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • d.L.GGi.1 (d.L.GGi.1 ((d.κ (dTy P ρ)).1 Φ₀))` using `congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ₀) (hcurv ρ)`. Establish `hζQ : (((fun _ => (1 : ℂ)), ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT` using `⟨fun _ => one_ne_zero, hζ⟩`.

Establish `key` using `congrArg (fun Φ => ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) ⟨_, hζQ⟩) hc'`. Rewrite `key` using `[tsub, tsmul, hSN, hNS, hG, hG, hΨ]`. Simplify using `only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, mulQ_ggiP, Subalgebra.coe_one, Pi.one_apply, dzbQ_apply P hTT, dzQ_apply P hTT, fnZ_val P hAs, fnZ_val P hBs] at key`. Establish `hz1` using `wirt_fnZ_zb P hAs ⟨_, hζQ⟩`. Establish `hz2` using `wirtinger_derivative_fibre_function P hBs ⟨_, hζQ⟩`.

Simplify using `only at hz1 hz2`. Rewrite `key` using `[hz1, hz2]`. Establish `hAd : DifferentiableAt ℝ (A ρ) ζ` using `(hAs.contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)`. Establish `hmd : DifferentiableAt ℝ (modA P ρ) ζ` using `((modA_smooth P ρ hTT).contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)`. Establish `hBeq : B ρ =ᶠ[nhds ζ] fun w => star (A ρ w)` using `by filter_upwards [(ann_open P).mem_nhds hζ] with w hw`.

Conclude with `hBA ρ w hw`. Establish `hdZB : NF.dZ (B ρ) ζ = star (NF.dZb (A ρ) ζ)`. Rewrite using `[Formalism.FourierDecayAlt.P5.HerB.dZ_eq, hBeq.fderiv_eq, ← Formalism.FourierDecayAlt.P5.HerB.dZ_eq]`. Conclude with `Formalism.FourierDecayAlt.P5.HerB.dZ_conj hAd`. Express the relevant statement in the definitionally equal form `-NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (NF.dZ (B ρ) ζ + A ρ ζ * B ρ ζ) = ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) at key`.

Rewrite `key` using `[hdZB]`. Establish `h2 : -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (star (NF.dZb (A ρ) ζ) + A ρ ζ * B ρ ζ) = -(NF.dZb (A ρ) ζ + star (NF.dZb (A ρ) ζ))` using `by ring`. Establish `h4 : ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) = ((2 * M.aC P ρ * P.TT * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `key` using `[h2, h4]`. Establish `h3` using `congrArg Complex.re key`.

Rewrite `h3` using `[Complex.neg_re, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re]`. Establish `hx : 0 < Complex.normSq ζ - P.TT` using `sub_pos.mpr hζ`. Rewrite using `[dZb_sub hmd hAd, Complex.sub_re, re_dZb_modA P ρ hζ]`. Establish `hw : (NF.dZb (A ρ) ζ).re = -(M.aC P ρ * P.TT) * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹)`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hw]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem curvTr_core
    (hmod : ∀ (P : M.Par) (ρ : M.Ty P) (ζ : ℂ), ζ ∈ Ann P →
      NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) :
    GTCCurvTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hK A B hAB hC hBA hcurv ρ ζ hζ
  have hTT : 0 ≤ P.TT := tt_nonneg_of_hyp hyp
  have hev : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q :=
    fun Φ σ q => SSTr.trR_apply P Bs hyp.1 hyp.2.1 e he Φ σ q
  have tsub : ∀ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (Φ - Ψ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q -
          ((trR P Bs e Ψ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro Φ Ψ σ q
    rw [hev, hev, hev, Submodule.coe_sub, sub_eq_add_neg, ← neg_one_smul ℂ (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      VLem.rawR_add, VLem.rawR_smul]
    simp [sub_eq_add_neg]
  have tsmul : ∀ (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (c • Φ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        c * ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro c Φ σ q
    rw [hev, hev, Submodule.coe_smul, VLem.rawR_smul]
    rfl
  obtain ⟨Φ₀, hΦ₀, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have hAs := (hAB ρ).1
  have hBs := (hAB ρ).2
  have hΨ : trR P Bs e ((d.κ (dTy P ρ)).1 Φ₀) ρ = 1 := by
    rw [hK, actA_kap, hΦ₀]
    simp [dTy]
  have hN : trR P Bs e (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (A ρ) := by
    rw [(hC _ ρ).1, hΨ, dzQ_one P hTT, zero_add, mul_one]
  have hS : trR P Bs e (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (B ρ) := by
    rw [(hC _ ρ).2, hΨ, dzbQ_one P hTT, neg_zero, zero_add, mul_one]
  have hSN : trR P Bs e (d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      -dzbQ P (fnZ P (A ρ)) + fnZ P (B ρ) * fnZ P (A ρ) := by
    rw [(hC _ ρ).2, hN]
  have hNS : trR P Bs e (d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      dzQ P (fnZ P (B ρ)) + fnZ P (A ρ) * fnZ P (B ρ) := by
    rw [(hC _ ρ).1, hS]
  have hG : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      trR P Bs e (d.L.GGi.1 Φ) ρ = mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ) := by
    intro Φ
    rw [((GT.gauge_function_holds Wp Wq P Bs X d hyp e) Φ).2.2.2.2.2, actA_ggiA]
  have hc' : d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) - d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) =
      ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • d.L.GGi.1 (d.L.GGi.1 ((d.κ (dTy P ρ)).1 Φ₀)) :=
    congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ₀) (hcurv ρ)
  have hζQ : (((fun _ => (1 : ℂ)), ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨fun _ => one_ne_zero, hζ⟩
  have key := congrArg (fun Φ => ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) ⟨_, hζQ⟩) hc'
  rw [tsub, tsmul, hSN, hNS, hG, hG, hΨ] at key
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply,
    mulQ_ggiP, Subalgebra.coe_one, Pi.one_apply, dzbQ_apply P hTT, dzQ_apply P hTT,
    fnZ_val P hAs, fnZ_val P hBs] at key
  have hz1 := wirt_fnZ_zb P hAs ⟨_, hζQ⟩
  have hz2 := wirtinger_derivative_fibre_function P hBs ⟨_, hζQ⟩
  dsimp only at hz1 hz2
  rw [hz1, hz2] at key
  have hAd : DifferentiableAt ℝ (A ρ) ζ := (hAs.contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hmd : DifferentiableAt ℝ (modA P ρ) ζ :=
    ((modA_smooth P ρ hTT).contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hBeq : B ρ =ᶠ[nhds ζ] fun w => star (A ρ w) := by
    filter_upwards [(ann_open P).mem_nhds hζ] with w hw
    exact hBA ρ w hw
  have hdZB : NF.dZ (B ρ) ζ = star (NF.dZb (A ρ) ζ) := by
    rw [Formalism.FourierDecayAlt.P5.HerB.dZ_eq, hBeq.fderiv_eq, ← Formalism.FourierDecayAlt.P5.HerB.dZ_eq]
    exact Formalism.FourierDecayAlt.P5.HerB.dZ_conj hAd
  change -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (NF.dZ (B ρ) ζ + A ρ ζ * B ρ ζ) =
    ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) at key
  rw [hdZB] at key
  have h2 : -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (star (NF.dZb (A ρ) ζ) + A ρ ζ * B ρ ζ) =
      -(NF.dZb (A ρ) ζ + star (NF.dZb (A ρ) ζ)) := by ring
  have h4 : ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) =
      ((2 * M.aC P ρ * P.TT * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, h4] at key
  have h3 := congrArg Complex.re key
  rw [Complex.neg_re, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re] at h3
  have hx : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  rw [dZb_sub hmd hAd, Complex.sub_re, re_dZb_modA P ρ hζ]
  have hw : (NF.dZb (A ρ) ζ).re = -(M.aC P ρ * P.TT) * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) := by
    linarith
  rw [hw]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
The claim follows from `CurvTr.curvTr_core (fun P ρ ζ hζ => dZb_modA P ρ hζ)`.
-/
theorem curvature_trace_holds : GTCCurvTr := CurvTr.curvTr_core (fun P ρ ζ hζ => dZb_modA P ρ hζ)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
