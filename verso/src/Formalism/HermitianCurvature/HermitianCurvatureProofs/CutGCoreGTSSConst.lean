import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGauge
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSC

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
Establish `hs` using `Real.sqrt_nonneg P.TT`. Establish `hss` using `Real.sq_sqrt hTT.le`. Establish `heq : Ann P = (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Set.Ioi (Real.sqrt P.TT) ×ˢ (Set.univ : Set ℝ))`. Use extensionality with `ζ`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : P.TT < Complex.normSq ζ` using `h`. Use `⟨(‖ζ‖, Complex.arg ζ), ⟨?_, Set.mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I ζ⟩` and prove the remaining obligations. Use `show Real.sqrt P.TT < ‖ζ‖`. Rewrite `h'` using `[Complex.normSq_eq_norm_sq]`.

Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Use polynomial arithmetic with `[norm_nonneg ζ, mul_le_mul hle hle (norm_nonneg ζ) hs]`. Introduce and unpack `⟨⟨a, b⟩, ⟨ha, -⟩, rfl⟩`. Establish `ha' : Real.sqrt P.TT < a` using `ha`.

Use `show P.TT < Complex.normSq ((a : ℂ) * Complex.exp (b * Complex.I))`. Rewrite using `[Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hs ha')]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[heq]`. Conclude with `(isPreconnected_Ioi.prod isPreconnected_univ).image _ (Continuous.continuousOn (by fun_prop))`.
-/
theorem ann_preconn (P : M.Par) (hTT : 0 < P.TT) : IsPreconnected (Ann P) := by
  have hs := Real.sqrt_nonneg P.TT
  have hss := Real.sq_sqrt hTT.le
  have heq : Ann P = (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) ''
      (Set.Ioi (Real.sqrt P.TT) ×ˢ (Set.univ : Set ℝ)) := by
    ext ζ
    constructor
    · intro h
      have h' : P.TT < Complex.normSq ζ := h
      refine ⟨(‖ζ‖, Complex.arg ζ), ⟨?_, Set.mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I ζ⟩
      show Real.sqrt P.TT < ‖ζ‖
      rw [Complex.normSq_eq_norm_sq] at h'
      by_contra hle
      push_neg at hle
      nlinarith [norm_nonneg ζ, mul_le_mul hle hle (norm_nonneg ζ) hs]
    · rintro ⟨⟨a, b⟩, ⟨ha, -⟩, rfl⟩
      have ha' : Real.sqrt P.TT < a := ha
      show P.TT < Complex.normSq ((a : ℂ) * Complex.exp (b * Complex.I))
      rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hs ha')]
      nlinarith
  rw [heq]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image _ (Continuous.continuousOn (by fun_prop))

/- English proof (translation)
Establish `hopen : IsOpen (Ann P)` using `isOpen_lt continuous_const Complex.continuous_normSq`. Establish `hdiff : DifferentiableOn ℝ f (Ann P)` using `hf.differentiableOn (by simp)`. Establish `hzero : Set.EqOn (fderiv ℝ f) 0 (Ann P)`. Introduce `ζ hζ`. Take `⟨h1, h2⟩` from `h0 ζ hζ`.

Simplify using `only [NF.dZ, NF.dZb] at h1 h2`. Establish `e1 : fderiv ℝ f ζ 1 = 0` using `by linear_combination h1 + h2`. Establish `e2 : fderiv ℝ f ζ Complex.I = 0`. Establish `h3 : Complex.I * fderiv ℝ f ζ Complex.I = 0` using `by linear_combination h2 - h1`. Simplify `h3` using `[Complex.I_ne_zero]`.

Use `show fderiv ℝ f ζ = 0`. Use `ContinuousLinearMap.ext fun w => ?_` and prove the remaining obligations. Establish `hw : w = w.re • (1 : ℂ) + w.im • Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[ContinuousLinearMap.zero_apply, hw, map_add, map_smul, map_smul, e1, e2]`.

Simplify using the standard rewrite rules. Use `⟨f (((Real.sqrt P.TT + 1 : ℝ)) : ℂ), fun ζ hζ => ?_⟩` and prove the remaining obligations. Conclude with `hopen.is_const_of_fderiv_eq_zero (ann_preconn P hTT) hdiff hzero hζ (ann_pt P hTT)`.
-/
theorem const_of_wirt (P : M.Par) (hTT : 0 < P.TT) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P))
    (h0 : ∀ ζ ∈ Ann P, NF.dZ f ζ = 0 ∧ NF.dZb f ζ = 0) : ∃ C : ℂ, ∀ ζ ∈ Ann P, f ζ = C := by
  have hopen : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq
  have hdiff : DifferentiableOn ℝ f (Ann P) := hf.differentiableOn (by simp)
  have hzero : Set.EqOn (fderiv ℝ f) 0 (Ann P) := by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := h0 ζ hζ
    simp only [NF.dZ, NF.dZb] at h1 h2
    have e1 : fderiv ℝ f ζ 1 = 0 := by linear_combination h1 + h2
    have e2 : fderiv ℝ f ζ Complex.I = 0 := by
      have h3 : Complex.I * fderiv ℝ f ζ Complex.I = 0 := by linear_combination h2 - h1
      simpa [Complex.I_ne_zero] using h3
    show fderiv ℝ f ζ = 0
    refine ContinuousLinearMap.ext fun w => ?_
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [ContinuousLinearMap.zero_apply, hw, map_add, map_smul, map_smul, e1, e2]
    simp
  refine ⟨f (((Real.sqrt P.TT + 1 : ℝ)) : ℂ), fun ζ hζ => ?_⟩
  exact hopen.is_const_of_fderiv_eq_zero (ann_preconn P hTT) hdiff hzero hζ (ann_pt P hTT)

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def vl (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) : ℂ :=
  (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) q

/- English proof (translation)
Unfold `B.hsVec`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem hsVec_sub (A C : Wq →L[ℂ] Wp) : B.hsVec (A - C) = B.hsVec A - B.hsVec C := by
  unfold B.hsVec
  ext i
  simp

/- English proof (translation)
Establish `hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ, rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT` using `fun Φ ρ => radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ`. Establish `hv : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', vl P Bs e Φ ρ q = rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q`. Introduce `Φ`. Simplify using `only [vl, GC.trR, MA.toSm, dif_pos (hsm Φ ρ)]`. Rewrite using `[hv, hv, hv]`.

Simplify using `only [rawR, Submodule.coe_sub, Pi.sub_apply, hsVec_sub, inner_sub_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vl_sub (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    vl P Bs e (Φ - Ψ) ρ q = vl P Bs e Φ ρ q - vl P Bs e Ψ ρ q := by
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hv : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', vl P Bs e Φ ρ q =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    intro Φ
    simp only [vl, GC.trR, MA.toSm, dif_pos (hsm Φ ρ)]
  rw [hv, hv, hv]
  simp only [rawR, Submodule.coe_sub, Pi.sub_apply, hsVec_sub, inner_sub_right]
  ring

/- English proof (translation)
Unfold `vl`. Rewrite using `[show trR P Bs e ((d.κ f).1 Φ) ρ = _ from congrFun (hk f Φ) ρ, actA_kap]`. Both sides reduce to the same expression.
-/
theorem vl_kap (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (hk : KapF P Bs d e) (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P)
    (q : MA.Qp P.r P.TT) : vl P Bs e ((d.κ f).1 Φ) ρ q = f ρ * vl P Bs e Φ ρ q := by
  unfold vl
  rw [show trR P Bs e ((d.κ f).1 Φ) ρ = _ from congrFun (hk f Φ) ρ, actA_kap]
  rfl

/- English proof (translation)
Simplify using `only [MA.actA, MA.sc]`. Use `(Fintype.sum_eq_single ρ ?_).trans ?_` and prove the remaining obligations. Introduce `b hb`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (Ne.symm hb)]`. Apply the tactic sequence `first | rfl | simp [ZeroMemClass.coe_zero] | exact LinearMap.zero_apply _`.

Simplify using `[Matrix.scalar_apply]`. Both sides reduce to the same expression.
-/
theorem actA_sc (P : M.Par) (x : (MA.DQ P).Pr) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.sc P (MA.DQ P) x) g ρ = x.1 (g ρ) := by
  simp only [MA.actA, MA.sc]
  refine (Fintype.sum_eq_single ρ ?_).trans ?_
  · intro b hb
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    first | rfl | simp [ZeroMemClass.coe_zero] | exact LinearMap.zero_apply _
  · simp [Matrix.scalar_apply]
    rfl

/- English proof (translation)
Take `⟨f1, -, f3, -, -, f6⟩` from `GT.gauge_function_holds Wp Wq P Bs X d hH e Φ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `vl`. Rewrite using `[show trR P Bs e (d.L.ζ.1 Φ) ρ = _ from congrFun f1 ρ]`. Conclude with `(congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q) (actA_sc P _ _ ρ)).trans (mulQ_zP P _ q)`.

Unfold `vl`. Rewrite using `[show trR P Bs e (d.L.ζb.1 Φ) ρ = _ from congrFun f3 ρ]`. Conclude with `(congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q) (actA_sc P _ _ ρ)).trans (mulQ_zbP P _ q)`. Unfold `vl`. Rewrite using `[show trR P Bs e (d.L.GGi.1 Φ) ρ = _ from congrFun f6 ρ]`.

Conclude with `(congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q) (actA_sc P _ _ ρ)).trans (mulQ_ggiP P _ q)`.
-/
theorem vl_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hH : GTHyp P Bs X d)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P)
    (q : MA.Qp P.r P.TT) :
    vl P Bs e (d.L.ζ.1 Φ) ρ q = q.1.2 * vl P Bs e Φ ρ q ∧
    vl P Bs e (d.L.ζb.1 Φ) ρ q = star q.1.2 * vl P Bs e Φ ρ q ∧
    vl P Bs e (d.L.GGi.1 Φ) ρ q = ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * vl P Bs e Φ ρ q := by
  obtain ⟨f1, -, f3, -, -, f6⟩ := GT.gauge_function_holds Wp Wq P Bs X d hH e Φ
  refine ⟨?_, ?_, ?_⟩
  · unfold vl
    rw [show trR P Bs e (d.L.ζ.1 Φ) ρ = _ from congrFun f1 ρ]
    exact (congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q) (actA_sc P _ _ ρ)).trans
      (mulQ_zP P _ q)
  · unfold vl
    rw [show trR P Bs e (d.L.ζb.1 Φ) ρ = _ from congrFun f3 ρ]
    exact (congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q) (actA_sc P _ _ ρ)).trans
      (mulQ_zbP P _ q)
  · unfold vl
    rw [show trR P Bs e (d.L.GGi.1 Φ) ρ = _ from congrFun f6 ρ]
    exact (congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q) (actA_sc P _ _ ρ)).trans
      (mulQ_ggiP P _ q)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `vl`. Rewrite using `[show trR P Bs e (d.L.nab.1 Φ) ρ = _ from congrFun (hn Φ).1 ρ, actA_nabA]`. Use `show (dzQ P (trR P Bs e Φ ρ) : MA.Qp P.r P.TT → ℂ) q + (M.aC P ρ : ℂ) * ((mulQ P (MA.DQ P).zbP (mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ)) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = _`. Rewrite using `[mulQ_zbP, mulQ_ggiP]`.

Unfold `vl`. Rewrite using `[show trR P Bs e (d.L.nabs.1 Φ) ρ = _ from congrFun (hn Φ).2 ρ, actA_nabsA]`. Use `show -(dzbQ P (trR P Bs e Φ ρ) : MA.Qp P.r P.TT → ℂ) q + (M.aC P ρ : ℂ) * ((mulQ P (MA.DQ P).zP (mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ)) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = _`. Rewrite using `[mulQ_zP, mulQ_ggiP]`.
-/
theorem vl_nab (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (hn : NabF P Bs d e) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    vl P Bs e (d.L.nab.1 Φ) ρ q = (dzQ P (trR P Bs e Φ ρ) : MA.Qp P.r P.TT → ℂ) q +
        (M.aC P ρ : ℂ) * (star q.1.2 * (((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * vl P Bs e Φ ρ q)) ∧
    vl P Bs e (d.L.nabs.1 Φ) ρ q = -(dzbQ P (trR P Bs e Φ ρ) : MA.Qp P.r P.TT → ℂ) q +
        (M.aC P ρ : ℂ) * (q.1.2 * (((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * vl P Bs e Φ ρ q)) := by
  refine ⟨?_, ?_⟩
  · unfold vl
    rw [show trR P Bs e (d.L.nab.1 Φ) ρ = _ from congrFun (hn Φ).1 ρ, actA_nabA]
    show (dzQ P (trR P Bs e Φ ρ) : MA.Qp P.r P.TT → ℂ) q +
      (M.aC P ρ : ℂ) * ((mulQ P (MA.DQ P).zbP (mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ)) :
        MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = _
    rw [mulQ_zbP, mulQ_ggiP]
  · unfold vl
    rw [show trR P Bs e (d.L.nabs.1 Φ) ρ = _ from congrFun (hn Φ).2 ρ, actA_nabsA]
    show -(dzbQ P (trR P Bs e Φ ρ) : MA.Qp P.r P.TT → ℂ) q +
      (M.aC P ρ : ℂ) * ((mulQ P (MA.DQ P).zP (mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ)) :
        MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = _
    rw [mulQ_zP, mulQ_ggiP]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hSL l hl Φ ρ'`. Prove the components needed by the constructor for the conclusion. Simplify using `only [vl, h1, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[fnZ_eq_mk P (hst l ρ' σ).1]`.

Simplify using `only [vl, h2, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[fnZ_eq_mk P (hst l ρ' σ).2]`.
-/
theorem vl_SS (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) (hst : SmST P s t) (hSL : SSLoc P Bs d e s t)
    {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P)
    (q : MA.Qp P.r P.TT) :
    vl P Bs e ((d.SS l).1 Φ) ρ' q = ∑ σ, s l ρ' σ q.1.2 * vl P Bs e Φ σ q ∧
    vl P Bs e ((star (d.SS l)).1 Φ) ρ' q = ∑ σ, t l ρ' σ q.1.2 * vl P Bs e Φ σ q := by
  obtain ⟨h1, h2⟩ := hSL l hl Φ ρ'
  constructor
  · simp only [vl, h1, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [fnZ_eq_mk P (hst l ρ' σ).1]
  · simp only [vl, h2, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [fnZ_eq_mk P (hst l ρ' σ).2]

end vals

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `a` using `h1 i`. Establish `b` using `h2 i`. Conclude with `Fin.ext (by omega)`.
-/
theorem up_pred {P : M.Par} {l : ℕ} {σ ρ τ : M.Ty P} (h1 : M.Up P l σ τ) (h2 : M.Up P l ρ τ) : σ = ρ := by
  funext i
  have a := h1 i
  have b := h2 i
  exact Fin.ext (by omega)

/- English proof (translation)
Simplify using `[mul_ite, Finset.sum_ite_eq']`.
-/
theorem sum_delta {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) (a : ι) (c : ℂ) :
    ∑ σ, f σ * (if σ = a then c else 0) = f a * c := by
  simp [mul_ite, Finset.sum_ite_eq']

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hn s t hst hSL l hl ρ' ρ0`. Establish `hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π'` using `hH.1`. Establish `hk2 : 2 ≤ P.k` using `hH.2.1`. Establish `hAL` using `hH.2.2.2.1`. Establish `hS` using `hH.2.2.2.2.1`.

Establish `hR` using `hH.2.2.2.2.2.1`. Establish `hTT : 0 < P.TT` using `mul_pos hpl.1.T_pos hpl.1.T'_pos`. Establish `pm : ∀ x y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), (x * y).1 = x.1 * y.1` using `fun _ _ => rfl`. Establish `ps : ∀ x y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), (x - y).1 = x.1 - y.1` using `fun _ _ => rfl`. Take `⟨U, hU, -⟩` from `SSTr.exists_tr P Bs hpl hk2 e he (fun σ => fnZ P (fun _ => if σ = ρ0 then (1 : ℂ) else 0))`.

Establish `hUt : ∀ σ, trR P Bs e U σ = fnZ P (fun _ => if σ = ρ0 then (1 : ℂ) else 0)` using `fun σ => congrFun hU σ`. Establish `hUv : ∀ σ q, vl P Bs e U σ q = if σ = ρ0 then 1 else 0`. Introduce `σ q`. Unfold `vl`. Rewrite using `[hUt σ]`.

Conclude with `fnZ_val P contDiffOn_const q`. Establish `hdU : ∀ σ (q : MA.Qp P.r P.TT), (dzQ P (trR P Bs e U σ) : MA.Qp P.r P.TT → ℂ) q = 0 ∧ (dzbQ P (trR P Bs e U σ) : MA.Qp P.r P.TT → ℂ) q = 0`. Introduce `σ q`. Rewrite using `[hUt σ]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[dzQ_apply P hTT.le, wirtinger_derivative_fibre_function P contDiffOn_const q]`. Simplify using `[NF.dZ]`. Rewrite using `[dzbQ_apply P hTT.le, wirt_fnZ_zb P contDiffOn_const q]`. Simplify using `[NF.dZb]`. Establish `hfn` using `fun Φ ρ q => vl_fn P Bs X d hH e Φ ρ q`.

Establish `hnb` using `fun Φ ρ q => vl_nab P Bs d e hn Φ ρ q`. Establish `hss` using `fun Φ ρ q => vl_SS P Bs d e s t hst hSL hl Φ ρ q`. Establish `hNU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.nab.1 U) σ q = if σ = ρ0 then (M.aC P σ : ℂ) * (star q.1.2 * (((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * 1)) else 0`. Introduce `σ q`. Rewrite using `[(hnb U σ q).1, (hdU σ q).1, hUv]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hNsU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.nabs.1 U) σ q = if σ = ρ0 then (M.aC P σ : ℂ) * (q.1.2 * (((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * 1)) else 0`. Introduce `σ q`. Rewrite using `[(hnb U σ q).2, (hdU σ q).2, hUv]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hGZU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.GGi.1 (d.L.ζ.1 U)) σ q = if σ = ρ0 then ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (q.1.2 * 1) else 0`. Introduce `σ q`. Rewrite using `[(hfn _ σ q).2.2, (hfn U σ q).1, hUv]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hGZbU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.GGi.1 (d.L.ζb.1 U)) σ q = if σ = ρ0 then ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (star q.1.2 * 1) else 0`.

Introduce `σ q`. Rewrite using `[(hfn _ σ q).2.2, (hfn U σ q).2.1, hUv]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hVeq : trR P Bs e ((d.SS l).1 U) ρ' = fnZ P (s l ρ' ρ0)`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `q`. Use `show vl P Bs e ((d.SS l).1 U) ρ' q = _`. Rewrite using `[(hss U ρ' q).1, fnZ_val P (hst l ρ' ρ0).1 q]`. Simplify using `only [hUv, sum_delta, mul_one]`. Establish `hWeq : trR P Bs e ((star (d.SS l)).1 U) ρ' = fnZ P (t l ρ' ρ0)`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Use `show vl P Bs e ((star (d.SS l)).1 U) ρ' q = _`. Rewrite using `[(hss U ρ' q).2, fnZ_val P (hst l ρ' ρ0).2 q]`. Simplify using `only [hUv, sum_delta, mul_one]`.

Establish `hVv : ∀ q, vl P Bs e ((d.SS l).1 U) ρ' q = s l ρ' ρ0 q.1.2`. Introduce `q`. Unfold `vl`. Rewrite using `[hVeq]`. Conclude with `fnZ_val P (hst l ρ' ρ0).1 q`.

Establish `hWv : ∀ q, vl P Bs e ((star (d.SS l)).1 U) ρ' q = t l ρ' ρ0 q.1.2`. Introduce `q`. Unfold `vl`. Rewrite using `[hWeq]`. Conclude with `fnZ_val P (hst l ρ' ρ0).2 q`.

Establish `hVd : ∀ q : MA.Qp P.r P.TT, (dzQ P (trR P Bs e ((d.SS l).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q = NF.dZ (s l ρ' ρ0) q.1.2 ∧ (dzbQ P (trR P Bs e ((d.SS l).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q = NF.dZb (s l ρ' ρ0) q.1.2`. Introduce `q`. Rewrite using `[hVeq]`. Conclude with `⟨(dzQ_apply P hTT.le _ q).trans (wirtinger_derivative_fibre_function P (hst l ρ' ρ0).1 q), (dzbQ_apply P hTT.le _ q).trans (wirt_fnZ_zb P (hst l ρ' ρ0).1 q)⟩`. Establish `hWd : ∀ q : MA.Qp P.r P.TT, (dzQ P (trR P Bs e ((star (d.SS l)).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q = NF.dZ (t l ρ' ρ0) q.1.2 ∧ (dzbQ P (trR P Bs e ((star (d.SS l)).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q = NF.dZb (t l ρ' ρ0) q.1.2`.

Introduce `q`. Rewrite using `[hWeq]`. Conclude with `⟨(dzQ_apply P hTT.le _ q).trans (wirtinger_derivative_fibre_function P (hst l ρ' ρ0).2 q), (dzbQ_apply P hTT.le _ q).trans (wirt_fnZ_zb P (hst l ρ' ρ0).2 q)⟩`. Establish `hrel` using `hR.2.2.2.2.1 l hl`. Establish `hGi : star d.L.GGi = d.L.GGi` using `by rw [hAL.2.2.2.2.2.2.2.2.2.2.2.1]; rfl`.

Establish `hZb : star d.L.ζb = d.L.ζ` using `by rw [← hS.1, star_star]`. Establish `hNs : star d.L.nabs = d.L.nab` using `by rw [← hS.2.1, star_star]`. Establish `E1 : d.L.nab.1 ((d.SS l).1 U) = (d.SS l).1 (d.L.nab.1 U) - d.L.ζb.1 (d.L.GGi.1 ((d.SS l).1 U))`. Establish `h` using `congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) hrel.1`. Simplify using `only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h`.

Conclude with `h`. Establish `E2 : d.L.nabs.1 ((d.SS l).1 U) = (d.SS l).1 (d.L.nabs.1 U) - d.L.ζ.1 (d.L.GGi.1 ((d.SS l).1 U))`. Establish `h` using `congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) hrel.2`. Simplify using `only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h`. Conclude with `h`.

Establish `F1 : (star (d.SS l)).1 (d.L.nabs.1 U) = d.L.nabs.1 ((star (d.SS l)).1 U) - (star (d.SS l)).1 (d.L.GGi.1 (d.L.ζ.1 U))`. Establish `h0` using `congrArg star hrel.1`. Rewrite `h0` using `[star_mul, star_sub, star_mul, star_mul, star_mul, hS.2.1, hGi, hZb]`. Establish `h` using `congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) h0`. Simplify using `only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h`.

Conclude with `h`. Establish `F2 : (star (d.SS l)).1 (d.L.nab.1 U) = d.L.nab.1 ((star (d.SS l)).1 U) - (star (d.SS l)).1 (d.L.GGi.1 (d.L.ζb.1 U))`. Establish `h0` using `congrArg star hrel.2`. Rewrite `h0` using `[star_mul, star_sub, star_mul, star_mul, star_mul, hNs, hGi, hS.1]`. Establish `h` using `congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) h0`.

Simplify using `only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h`. Conclude with `h`. Establish `hDs : ∀ q : MA.Qp P.r P.TT, M.Up P l ρ0 ρ' → NF.dZ (s l ρ' ρ0) q.1.2 = 0 ∧ NF.dZb (s l ρ' ρ0) q.1.2 = 0`. Introduce `q hup`. Establish `ha : (M.aC P ρ' : ℂ) = (M.aC P ρ0 : ℂ) - 1`.

Rewrite using `[Mx4.aC_up P l hl ρ0 ρ' hup]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `V1` using `congrArg (fun Φ => vl P Bs e Φ ρ' q) E1`. Establish `V2` using `congrArg (fun Φ => vl P Bs e Φ ρ' q) E2`.

Apply the tactic sequence `try simp only at V1 V2`. Rewrite `V1` using `[vl_sub P Bs hpl hk2 e he, (hnb ((d.SS l).1 U) ρ' q).1, (hss (d.L.nab.1 U) ρ' q).1, (hfn (d.L.GGi.1 ((d.SS l).1 U)) ρ' q).2.1, (hfn ((d.SS l).1 U) ρ' q).2.2, (hVd q).1, hVv]`. Rewrite `V2` using `[vl_sub P Bs hpl hk2 e he, (hnb ((d.SS l).1 U) ρ' q).2, (hss (d.L.nabs.1 U) ρ' q).1, (hfn (d.L.GGi.1 ((d.SS l).1 U)) ρ' q).1, (hfn ((d.SS l).1 U) ρ' q).2.2, (hVd q).2, hVv]`. Simplify using `only [hNU, hNsU, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at V1 V2`. Prove the components needed by the constructor for the conclusion.

Take the linear combination `V1 - (star q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * s l ρ' ρ0 q.1.2) * ha`. Take the linear combination `-V2 + (q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * s l ρ' ρ0 q.1.2) * ha`. Establish `hDt : ∀ q : MA.Qp P.r P.TT, M.Up P l ρ' ρ0 → NF.dZ (t l ρ' ρ0) q.1.2 = 0 ∧ NF.dZb (t l ρ' ρ0) q.1.2 = 0`. Introduce `q hup`. Establish `ha : (M.aC P ρ0 : ℂ) = (M.aC P ρ' : ℂ) - 1`.

Rewrite using `[Mx4.aC_up P l hl ρ' ρ0 hup]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `W1` using `congrArg (fun Φ => vl P Bs e Φ ρ' q) F1`. Establish `W2` using `congrArg (fun Φ => vl P Bs e Φ ρ' q) F2`.

Apply the tactic sequence `try simp only at W1 W2`. Rewrite `W1` using `[vl_sub P Bs hpl hk2 e he, (hss (d.L.nabs.1 U) ρ' q).2, (hnb ((star (d.SS l)).1 U) ρ' q).2, (hss (d.L.GGi.1 (d.L.ζ.1 U)) ρ' q).2, (hWd q).2, hWv]`. Rewrite `W2` using `[vl_sub P Bs hpl hk2 e he, (hss (d.L.nab.1 U) ρ' q).2, (hnb ((star (d.SS l)).1 U) ρ' q).1, (hss (d.L.GGi.1 (d.L.ζb.1 U)) ρ' q).2, (hWd q).1, hWv]`. Simplify using `only [hNU, hNsU, hGZU, hGZbU, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at W1 W2`. Prove the components needed by the constructor for the conclusion.

Take the linear combination `-W2 + (t l ρ' ρ0 q.1.2 * star q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹) * ha`. Take the linear combination `W1 - (t l ρ' ρ0 q.1.2 * q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹) * ha`. Establish `hZs : ∀ q : MA.Qp P.r P.TT, ¬ M.Up P l ρ0 ρ' → s l ρ' ρ0 q.1.2 = 0`. Introduce `q hup`. Set `f : M.Ty P → ℂ` to `fun σ => if σ = ρ0 then 1 else 0`.

Set `g : M.Ty P → ℂ` to `fun τ => if M.Up P l ρ0 τ then 1 else 0`. Establish `hfg : ∀ σ τ, M.Up P l σ τ → g τ = f σ`. Introduce `σ τ hστ`. Distinguish the cases in `h : σ = ρ0`. Substitute `h` using the available equality.

Simplify using `[f, g, hστ]`. Establish `: ¬ M.Up P l ρ0 τ` using `fun h' => h (up_pred hστ h')`. Simplify using `[f, g, h, this]`. Establish `h0` using `hR.2.2.2.1 l f g hfg`. Establish `h` using `congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => vl P Bs e (x.1 U) ρ' q) h0`.

Simplify using `only [pm, Module.End.mul_apply] at h`. Rewrite `h` using `[vl_kap P Bs d e hk, hVv, (hss _ ρ' q).1]`. Simplify using `only [vl_kap P Bs d e hk, hUv, f, g, hup, if_false, zero_mul] at h`. Establish `hdd : ∀ x : M.Ty P, ((if x = ρ0 then (1 : ℂ) else 0) * if x = ρ0 then (1 : ℂ) else 0) = if x = ρ0 then 1 else 0`. Apply the tactic sequence `intro x; split_ifs <;> simp`.

Simplify using `only [hdd, sum_delta, mul_one] at h`. Conclude with `h.symm`. Establish `hZt : ∀ q : MA.Qp P.r P.TT, ¬ M.Up P l ρ' ρ0 → t l ρ' ρ0 q.1.2 = 0`. Introduce `q hup`. Set `f : M.Ty P → ℂ` to `fun σ => if σ = ρ' then 1 else 0`.

Set `g : M.Ty P → ℂ` to `fun τ => if M.Up P l ρ' τ then 1 else 0`. Establish `hfg : ∀ σ τ, M.Up P l σ τ → g τ = f σ`. Introduce `σ τ hστ`. Distinguish the cases in `h : σ = ρ'`. Substitute `h` using the available equality.

Simplify using `[f, g, hστ]`. Establish `: ¬ M.Up P l ρ' τ` using `fun h' => h (up_pred hστ h')`. Simplify using `[f, g, h, this]`. Establish `h0` using `congrArg star (hR.2.2.2.1 l f g hfg)`. Establish `hsg : star (d.κ g) = d.κ g`.

Apply the tactic sequence `rw [hR.1]; congr 1; funext τ; simp only [g]; split_ifs <;> simp`. Establish `hsf : star (d.κ f) = d.κ f`. Apply the tactic sequence `rw [hR.1]; congr 1; funext τ; simp only [f]; split_ifs <;> simp`. Rewrite `h0` using `[star_mul, star_mul, hsg, hsf]`. Establish `h` using `congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => vl P Bs e (x.1 U) ρ' q) h0`.

Simplify using `only [pm, Module.End.mul_apply] at h`. Rewrite `h` using `[vl_kap P Bs d e hk, hWv, (hss _ ρ' q).2]`. Simplify using `only [vl_kap P Bs d e hk, hUv, f, g, hup, if_false, if_true] at h`. Simplify using `only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, one_mul] at h`. Conclude with `h.symm.trans (by simp [hup])`.

Set `qOf : ∀ ζ ∈ Ann P, MA.Qp P.r P.TT` to `fun ζ hζ => ⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩`. Establish `hCs : ∃ C : ℂ, ∀ ζ ∈ Ann P, s l ρ' ρ0 ζ = C`. Distinguish the cases in `hup : M.Up P l ρ0 ρ'`. Conclude with `const_of_wirt P hTT (hst l ρ' ρ0).1 fun ζ hζ => hDs (qOf ζ hζ) hup`. Conclude with `⟨0, fun ζ hζ => hZs (qOf ζ hζ) hup⟩`.

Establish `hCt : ∃ D : ℂ, ∀ ζ ∈ Ann P, t l ρ' ρ0 ζ = D`. Distinguish the cases in `hup : M.Up P l ρ' ρ0`. Conclude with `const_of_wirt P hTT (hst l ρ' ρ0).2 fun ζ hζ => hDt (qOf ζ hζ) hup`. Conclude with `⟨0, fun ζ hζ => hZt (qOf ζ hζ) hup⟩`. Take `⟨C, hC⟩` from `hCs`.

Take `⟨D, hD⟩` from `hCt`. Conclude with `⟨C, D, fun ζ hζ => ⟨hC ζ hζ, hD ζ hζ⟩⟩`.
-/
theorem second_shift_constant : GTSSConst := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hn s t hst hSL l hl ρ' ρ0
  classical
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hH.1
  have hk2 : 2 ≤ P.k := hH.2.1
  have hAL := hH.2.2.2.1
  have hS := hH.2.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hTT : 0 < P.TT := mul_pos hpl.1.T_pos hpl.1.T'_pos
  have pm : ∀ x y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), (x * y).1 = x.1 * y.1 := fun _ _ => rfl
  have ps : ∀ x y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), (x - y).1 = x.1 - y.1 := fun _ _ => rfl

  obtain ⟨U, hU, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he
    (fun σ => fnZ P (fun _ => if σ = ρ0 then (1 : ℂ) else 0))
  have hUt : ∀ σ, trR P Bs e U σ = fnZ P (fun _ => if σ = ρ0 then (1 : ℂ) else 0) := fun σ => congrFun hU σ
  have hUv : ∀ σ q, vl P Bs e U σ q = if σ = ρ0 then 1 else 0 := by
    intro σ q; unfold vl; rw [hUt σ]; exact fnZ_val P contDiffOn_const q
  have hdU : ∀ σ (q : MA.Qp P.r P.TT), (dzQ P (trR P Bs e U σ) : MA.Qp P.r P.TT → ℂ) q = 0 ∧
      (dzbQ P (trR P Bs e U σ) : MA.Qp P.r P.TT → ℂ) q = 0 := by
    intro σ q
    rw [hUt σ]
    refine ⟨?_, ?_⟩
    · rw [dzQ_apply P hTT.le, wirtinger_derivative_fibre_function P contDiffOn_const q]; simp [NF.dZ]
    · rw [dzbQ_apply P hTT.le, wirt_fnZ_zb P contDiffOn_const q]; simp [NF.dZb]
  have hfn := fun Φ ρ q => vl_fn P Bs X d hH e Φ ρ q
  have hnb := fun Φ ρ q => vl_nab P Bs d e hn Φ ρ q
  have hss := fun Φ ρ q => vl_SS P Bs d e s t hst hSL hl Φ ρ q

  have hNU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.nab.1 U) σ q = if σ = ρ0 then
      (M.aC P σ : ℂ) * (star q.1.2 * (((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * 1)) else 0 := by
    intro σ q
    rw [(hnb U σ q).1, (hdU σ q).1, hUv]
    split_ifs <;> simp
  have hNsU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.nabs.1 U) σ q = if σ = ρ0 then
      (M.aC P σ : ℂ) * (q.1.2 * (((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * 1)) else 0 := by
    intro σ q
    rw [(hnb U σ q).2, (hdU σ q).2, hUv]
    split_ifs <;> simp
  have hGZU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.GGi.1 (d.L.ζ.1 U)) σ q = if σ = ρ0 then
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (q.1.2 * 1) else 0 := by
    intro σ q
    rw [(hfn _ σ q).2.2, (hfn U σ q).1, hUv]
    split_ifs <;> simp
  have hGZbU : ∀ σ (q : MA.Qp P.r P.TT), vl P Bs e (d.L.GGi.1 (d.L.ζb.1 U)) σ q = if σ = ρ0 then
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (star q.1.2 * 1) else 0 := by
    intro σ q
    rw [(hfn _ σ q).2.2, (hfn U σ q).2.1, hUv]
    split_ifs <;> simp

  have hVeq : trR P Bs e ((d.SS l).1 U) ρ' = fnZ P (s l ρ' ρ0) := by
    apply Subtype.ext; funext q
    show vl P Bs e ((d.SS l).1 U) ρ' q = _
    rw [(hss U ρ' q).1, fnZ_val P (hst l ρ' ρ0).1 q]
    simp only [hUv, sum_delta, mul_one]
  have hWeq : trR P Bs e ((star (d.SS l)).1 U) ρ' = fnZ P (t l ρ' ρ0) := by
    apply Subtype.ext; funext q
    show vl P Bs e ((star (d.SS l)).1 U) ρ' q = _
    rw [(hss U ρ' q).2, fnZ_val P (hst l ρ' ρ0).2 q]
    simp only [hUv, sum_delta, mul_one]
  have hVv : ∀ q, vl P Bs e ((d.SS l).1 U) ρ' q = s l ρ' ρ0 q.1.2 := by
    intro q; unfold vl; rw [hVeq]; exact fnZ_val P (hst l ρ' ρ0).1 q
  have hWv : ∀ q, vl P Bs e ((star (d.SS l)).1 U) ρ' q = t l ρ' ρ0 q.1.2 := by
    intro q; unfold vl; rw [hWeq]; exact fnZ_val P (hst l ρ' ρ0).2 q
  have hVd : ∀ q : MA.Qp P.r P.TT, (dzQ P (trR P Bs e ((d.SS l).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q =
      NF.dZ (s l ρ' ρ0) q.1.2 ∧
      (dzbQ P (trR P Bs e ((d.SS l).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q = NF.dZb (s l ρ' ρ0) q.1.2 := by
    intro q; rw [hVeq]
    exact ⟨(dzQ_apply P hTT.le _ q).trans (wirtinger_derivative_fibre_function P (hst l ρ' ρ0).1 q),
      (dzbQ_apply P hTT.le _ q).trans (wirt_fnZ_zb P (hst l ρ' ρ0).1 q)⟩
  have hWd : ∀ q : MA.Qp P.r P.TT, (dzQ P (trR P Bs e ((star (d.SS l)).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q =
      NF.dZ (t l ρ' ρ0) q.1.2 ∧
      (dzbQ P (trR P Bs e ((star (d.SS l)).1 U) ρ') : MA.Qp P.r P.TT → ℂ) q = NF.dZb (t l ρ' ρ0) q.1.2 := by
    intro q; rw [hWeq]
    exact ⟨(dzQ_apply P hTT.le _ q).trans (wirtinger_derivative_fibre_function P (hst l ρ' ρ0).2 q),
      (dzbQ_apply P hTT.le _ q).trans (wirt_fnZ_zb P (hst l ρ' ρ0).2 q)⟩

  have hrel := hR.2.2.2.2.1 l hl
  have hGi : star d.L.GGi = d.L.GGi := by rw [hAL.2.2.2.2.2.2.2.2.2.2.2.1]; rfl
  have hZb : star d.L.ζb = d.L.ζ := by rw [← hS.1, star_star]
  have hNs : star d.L.nabs = d.L.nab := by rw [← hS.2.1, star_star]
  have E1 : d.L.nab.1 ((d.SS l).1 U) = (d.SS l).1 (d.L.nab.1 U) - d.L.ζb.1 (d.L.GGi.1 ((d.SS l).1 U)) := by
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) hrel.1
    simp only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h
    exact h
  have E2 : d.L.nabs.1 ((d.SS l).1 U) = (d.SS l).1 (d.L.nabs.1 U) - d.L.ζ.1 (d.L.GGi.1 ((d.SS l).1 U)) := by
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) hrel.2
    simp only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h
    exact h
  have F1 : (star (d.SS l)).1 (d.L.nabs.1 U) =
      d.L.nabs.1 ((star (d.SS l)).1 U) - (star (d.SS l)).1 (d.L.GGi.1 (d.L.ζ.1 U)) := by
    have h0 := congrArg star hrel.1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hS.2.1, hGi, hZb] at h0
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) h0
    simp only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h
    exact h
  have F2 : (star (d.SS l)).1 (d.L.nab.1 U) =
      d.L.nab.1 ((star (d.SS l)).1 U) - (star (d.SS l)).1 (d.L.GGi.1 (d.L.ζb.1 U)) := by
    have h0 := congrArg star hrel.2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hNs, hGi, hS.1] at h0
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 U) h0
    simp only [pm, ps, Module.End.mul_apply, LinearMap.sub_apply] at h
    exact h

  have hDs : ∀ q : MA.Qp P.r P.TT, M.Up P l ρ0 ρ' →
      NF.dZ (s l ρ' ρ0) q.1.2 = 0 ∧ NF.dZb (s l ρ' ρ0) q.1.2 = 0 := by
    intro q hup
    have ha : (M.aC P ρ' : ℂ) = (M.aC P ρ0 : ℂ) - 1 := by
      rw [Mx4.aC_up P l hl ρ0 ρ' hup]; push_cast; ring
    have V1 := congrArg (fun Φ => vl P Bs e Φ ρ' q) E1
    have V2 := congrArg (fun Φ => vl P Bs e Φ ρ' q) E2
    try simp only at V1 V2
    rw [vl_sub P Bs hpl hk2 e he, (hnb ((d.SS l).1 U) ρ' q).1, (hss (d.L.nab.1 U) ρ' q).1,
      (hfn (d.L.GGi.1 ((d.SS l).1 U)) ρ' q).2.1, (hfn ((d.SS l).1 U) ρ' q).2.2, (hVd q).1, hVv] at V1
    rw [vl_sub P Bs hpl hk2 e he, (hnb ((d.SS l).1 U) ρ' q).2, (hss (d.L.nabs.1 U) ρ' q).1,
      (hfn (d.L.GGi.1 ((d.SS l).1 U)) ρ' q).1, (hfn ((d.SS l).1 U) ρ' q).2.2, (hVd q).2, hVv] at V2
    simp only [hNU, hNsU, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at V1 V2
    constructor
    · linear_combination V1 - (star q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * s l ρ' ρ0 q.1.2) * ha
    · linear_combination -V2 + (q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * s l ρ' ρ0 q.1.2) * ha
  have hDt : ∀ q : MA.Qp P.r P.TT, M.Up P l ρ' ρ0 →
      NF.dZ (t l ρ' ρ0) q.1.2 = 0 ∧ NF.dZb (t l ρ' ρ0) q.1.2 = 0 := by
    intro q hup
    have ha : (M.aC P ρ0 : ℂ) = (M.aC P ρ' : ℂ) - 1 := by
      rw [Mx4.aC_up P l hl ρ' ρ0 hup]; push_cast; ring
    have W1 := congrArg (fun Φ => vl P Bs e Φ ρ' q) F1
    have W2 := congrArg (fun Φ => vl P Bs e Φ ρ' q) F2
    try simp only at W1 W2
    rw [vl_sub P Bs hpl hk2 e he, (hss (d.L.nabs.1 U) ρ' q).2, (hnb ((star (d.SS l)).1 U) ρ' q).2,
      (hss (d.L.GGi.1 (d.L.ζ.1 U)) ρ' q).2, (hWd q).2, hWv] at W1
    rw [vl_sub P Bs hpl hk2 e he, (hss (d.L.nab.1 U) ρ' q).2, (hnb ((star (d.SS l)).1 U) ρ' q).1,
      (hss (d.L.GGi.1 (d.L.ζb.1 U)) ρ' q).2, (hWd q).1, hWv] at W2
    simp only [hNU, hNsU, hGZU, hGZbU, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at W1 W2
    constructor
    · linear_combination -W2 + (t l ρ' ρ0 q.1.2 * star q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹) * ha
    · linear_combination W1 - (t l ρ' ρ0 q.1.2 * q.1.2 * ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹) * ha

  have hZs : ∀ q : MA.Qp P.r P.TT, ¬ M.Up P l ρ0 ρ' → s l ρ' ρ0 q.1.2 = 0 := by
    intro q hup
    let f : M.Ty P → ℂ := fun σ => if σ = ρ0 then 1 else 0
    let g : M.Ty P → ℂ := fun τ => if M.Up P l ρ0 τ then 1 else 0
    have hfg : ∀ σ τ, M.Up P l σ τ → g τ = f σ := by
      intro σ τ hστ
      by_cases h : σ = ρ0
      · subst h; simp [f, g, hστ]
      · have : ¬ M.Up P l ρ0 τ := fun h' => h (up_pred hστ h')
        simp [f, g, h, this]
    have h0 := hR.2.2.2.1 l f g hfg
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => vl P Bs e (x.1 U) ρ' q) h0
    simp only [pm, Module.End.mul_apply] at h
    rw [vl_kap P Bs d e hk, hVv, (hss _ ρ' q).1] at h
    simp only [vl_kap P Bs d e hk, hUv, f, g, hup, if_false, zero_mul] at h
    have hdd : ∀ x : M.Ty P, ((if x = ρ0 then (1 : ℂ) else 0) * if x = ρ0 then (1 : ℂ) else 0) =
        if x = ρ0 then 1 else 0 := by
      intro x; split_ifs <;> simp
    simp only [hdd, sum_delta, mul_one] at h
    exact h.symm
  have hZt : ∀ q : MA.Qp P.r P.TT, ¬ M.Up P l ρ' ρ0 → t l ρ' ρ0 q.1.2 = 0 := by
    intro q hup
    let f : M.Ty P → ℂ := fun σ => if σ = ρ' then 1 else 0
    let g : M.Ty P → ℂ := fun τ => if M.Up P l ρ' τ then 1 else 0
    have hfg : ∀ σ τ, M.Up P l σ τ → g τ = f σ := by
      intro σ τ hστ
      by_cases h : σ = ρ'
      · subst h; simp [f, g, hστ]
      · have : ¬ M.Up P l ρ' τ := fun h' => h (up_pred hστ h')
        simp [f, g, h, this]
    have h0 := congrArg star (hR.2.2.2.1 l f g hfg)
    have hsg : star (d.κ g) = d.κ g := by
      rw [hR.1]; congr 1; funext τ; simp only [g]; split_ifs <;> simp
    have hsf : star (d.κ f) = d.κ f := by
      rw [hR.1]; congr 1; funext τ; simp only [f]; split_ifs <;> simp
    rw [star_mul, star_mul, hsg, hsf] at h0
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => vl P Bs e (x.1 U) ρ' q) h0
    simp only [pm, Module.End.mul_apply] at h
    rw [vl_kap P Bs d e hk, hWv, (hss _ ρ' q).2] at h
    simp only [vl_kap P Bs d e hk, hUv, f, g, hup, if_false, if_true] at h
    simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
      one_mul] at h
    exact h.symm.trans (by simp [hup])

  let qOf : ∀ ζ ∈ Ann P, MA.Qp P.r P.TT := fun ζ hζ => ⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hCs : ∃ C : ℂ, ∀ ζ ∈ Ann P, s l ρ' ρ0 ζ = C := by
    by_cases hup : M.Up P l ρ0 ρ'
    · exact const_of_wirt P hTT (hst l ρ' ρ0).1 fun ζ hζ => hDs (qOf ζ hζ) hup
    · exact ⟨0, fun ζ hζ => hZs (qOf ζ hζ) hup⟩
  have hCt : ∃ D : ℂ, ∀ ζ ∈ Ann P, t l ρ' ρ0 ζ = D := by
    by_cases hup : M.Up P l ρ' ρ0
    · exact const_of_wirt P hTT (hst l ρ' ρ0).2 fun ζ hζ => hDt (qOf ζ hζ) hup
    · exact ⟨0, fun ζ hζ => hZt (qOf ζ hζ) hup⟩
  obtain ⟨C, hC⟩ := hCs
  obtain ⟨D, hD⟩ := hCt
  exact ⟨C, D, fun ζ hζ => ⟨hC ζ hζ, hD ζ hζ⟩⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSC
