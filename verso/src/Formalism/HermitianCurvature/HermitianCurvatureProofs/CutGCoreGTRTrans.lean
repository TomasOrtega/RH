import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefTraceCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `B.hsVec`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem hsVec_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  ext i
  simp

/- English proof (translation)
Unfold `B.hsVec`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

/- English proof (translation)
Unfold `SSC.vl`. Rewrite using `[SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]`. Unfold `rawR`. Simplify using `only [Submodule.coe_add, Pi.add_apply, hsVec_add, inner_add_right, mul_add]`.
-/
theorem vl_add (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (Φ + Ψ) ρ q = SSC.vl P Bs e Φ ρ q + SSC.vl P Bs e Ψ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_add, Pi.add_apply, hsVec_add, inner_add_right, mul_add]

/- English proof (translation)
Unfold `SSC.vl`. Rewrite using `[SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]`. Unfold `rawR`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, hsVec_smul, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vl_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (c • Φ) ρ q = c * SSC.vl P Bs e Φ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_smul, Pi.smul_apply, hsVec_smul, inner_smul_right]
  ring

end vals

/- English proof (translation)
Establish `h0 : MA.eulerQ (TT` using `P.TT) M.vz (1 : MA.SmQ P.r P.TT) = 0 := by`. Establish `h` using `Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vz 1 1`. Rewrite `h` using `[mul_one, one_mul, mul_one]`. Establish `h2 : MA.eulerQ (TT` using `P.TT) M.vz (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vz 1 = MA.eulerQ (TT := P.TT) M.vz 1 + 0 := by`. Rewrite using `[add_zero]`.

Conclude with `h.symm`. Conclude with `add_left_cancel h2`. Unfold `dzQ MA.DAlg.dzP MA.DAlg.mkP`. Establish `h0' : (MA.DQ P).ev M.vz 1 = 0` using `h0`. Use `show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0`.

Rewrite using `[h0', map_zero]`.
-/
theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vz 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vz 1 =
        MA.eulerQ (TT := P.TT) M.vz 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzQ MA.DAlg.dzP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vz 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [h0', map_zero]

/- English proof (translation)
Establish `h0 : MA.eulerQ (TT` using `P.TT) M.vzb (1 : MA.SmQ P.r P.TT) = 0 := by`. Establish `h` using `Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vzb 1 1`. Rewrite `h` using `[mul_one, one_mul, mul_one]`. Establish `h2 : MA.eulerQ (TT` using `P.TT) M.vzb (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vzb 1 = MA.eulerQ (TT := P.TT) M.vzb 1 + 0 := by`. Rewrite using `[add_zero]`.

Conclude with `h.symm`. Conclude with `add_left_cancel h2`. Unfold `dzbQ MA.DAlg.dzbP MA.DAlg.mkP`. Establish `h0' : (MA.DQ P).ev M.vzb 1 = 0` using `h0`. Use `show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0`.

Rewrite using `[h0', map_zero]`.
-/
theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vzb 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vzb 1 =
        MA.eulerQ (TT := P.TT) M.vzb 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzbQ MA.DAlg.dzbP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vzb 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [h0', map_zero]

/- English proof (translation)
Unfold `ThetaNF`. Both sides reduce to the same expression.
-/
theorem theta_fst {V : Type} [AddCommGroup V] [Module ℂ V] (P : M.Par) (d : Q.NFData P (Q.Pr V)) (Φ : V) :
    (ThetaNF P d).1 Φ = d.L.ζ.1 (d.L.nab.1 Φ) + d.L.ζb.1 (d.L.nabs.1 Φ) +
      (d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Φ +
      d.L.TT • d.L.GGi.1 ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Φ) := by
  unfold ThetaNF
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hC ρ m hm ζ hζ`. Establish `hpl` using `hyp.1`. Establish `hk2` using `hyp.2.1`. Establish `hTT : 0 ≤ P.TT` using `(mul_pos hpl.1.T_pos hpl.1.T'_pos).le`. Establish `hLTT : d.L.TT = ((P.TT : ℝ) : ℂ)`.

Rewrite using `[hyp.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]`. Both sides reduce to the same expression. Take `⟨Φ0, hΦ0, -⟩` from `SSTr.exists_tr P Bs hpl hk2 e he (fun _ => (1 : MA.SmQ P.r P.TT))`. Use `set Ψ0 := (d.κ (dTy P ρ)).1 Φ0 with hΨ0`. Establish `t0 : trR P Bs e Ψ0 ρ = 1`.

Rewrite using `[hΨ0, hk (dTy P ρ) Φ0, hΦ0, actA_kap]`. Simplify using `[dTy]`. Set `q0 : MA.Qp P.r P.TT` to `⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩`. Establish `v0 : SSC.vl P Bs e Ψ0 ρ q0 = 1`. Unfold `SSC.vl`.

Rewrite using `[t0]`. Both sides reduce to the same expression. Establish `t1 : trR P Bs e (d.L.nab.1 Ψ0) ρ = fnZ P (A ρ)`. Rewrite using `[(hC Ψ0 ρ).1, t0, GTRT.dzQ_one P hTT, mul_one, zero_add]`. Establish `t2 : trR P Bs e (d.L.nabs.1 Ψ0) ρ = fnZ P (B ρ)`.

Rewrite using `[(hC Ψ0 ρ).2, t0, GTRT.dzbQ_one P hTT, mul_one, neg_zero, zero_add]`. Establish `v1 : SSC.vl P Bs e (d.L.nab.1 Ψ0) ρ q0 = A ρ ζ`. Unfold `SSC.vl`. Rewrite using `[t1, fnZ_val P (hAB ρ).1]`. Establish `v2 : SSC.vl P Bs e (d.L.nabs.1 Ψ0) ρ q0 = B ρ ζ`.

Unfold `SSC.vl`. Rewrite using `[t2, fnZ_val P (hAB ρ).2]`. Establish `vm : SSC.vl P Bs e ((ThetaNF P d).1 Ψ0) ρ q0 = m`. Unfold `SSC.vl`. Rewrite using `[hm Ψ0, t0, GTRT.dzQ_one P hTT, GTRT.dzbQ_one P hTT, mul_zero, mul_zero, sub_zero, zero_add]`.

Use `show m * 1 = m`. Expand and normalize the polynomial expressions, which then agree. Establish `v3 : SSC.vl P Bs e ((d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Ψ0) ρ q0 = ((rhoSum P ρ : ℝ) : ℂ)`. Rewrite using `[SSC.vl_kap P Bs d e hk, v0, mul_one]`. Establish `v4 : SSC.vl P Bs e ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Ψ0) ρ q0 = ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ)`.

Rewrite using `[SSC.vl_kap P Bs d e hk, v0, mul_one]`. Use `clear_value Ψ0`. Establish `hfn` using `fun Ψ => SSC.vl_fn P Bs X d hyp e Ψ ρ q0`. Rewrite `vm` using `[GTRT.theta_fst, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_smul P Bs hpl hk2 e he, (hfn _).1, (hfn _).2.1, (hfn _).2.2, v3, v4, v1, v2, hLTT]`. Establish `hq : q0.1.2 = ζ` using `rfl`.

Rewrite `vm` using `[hq]`. Establish `hG : (Complex.normSq ζ : ℂ) - (P.TT : ℂ) ≠ 0`. Establish `: P.TT < Complex.normSq ζ` using `hζ`. Introduce `h0`. Establish `h1 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) = 0` using `by push_cast; exact h0`.

Establish `: Complex.normSq ζ - P.TT = 0` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← vm]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem radial_gauge_transition_holds : GTRTrans := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hC ρ m hm ζ hζ
  classical
  have hpl := hyp.1
  have hk2 := hyp.2.1
  have hTT : 0 ≤ P.TT := (mul_pos hpl.1.T_pos hpl.1.T'_pos).le
  have hLTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hyp.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  set Ψ0 := (d.κ (dTy P ρ)).1 Φ0 with hΨ0
  have t0 : trR P Bs e Ψ0 ρ = 1 := by
    rw [hΨ0, hk (dTy P ρ) Φ0, hΦ0, actA_kap]
    simp [dTy]
  let q0 : MA.Qp P.r P.TT := ⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have v0 : SSC.vl P Bs e Ψ0 ρ q0 = 1 := by
    unfold SSC.vl
    rw [t0]
    rfl
  have t1 : trR P Bs e (d.L.nab.1 Ψ0) ρ = fnZ P (A ρ) := by
    rw [(hC Ψ0 ρ).1, t0, GTRT.dzQ_one P hTT, mul_one, zero_add]
  have t2 : trR P Bs e (d.L.nabs.1 Ψ0) ρ = fnZ P (B ρ) := by
    rw [(hC Ψ0 ρ).2, t0, GTRT.dzbQ_one P hTT, mul_one, neg_zero, zero_add]
  have v1 : SSC.vl P Bs e (d.L.nab.1 Ψ0) ρ q0 = A ρ ζ := by
    unfold SSC.vl
    rw [t1, fnZ_val P (hAB ρ).1]
  have v2 : SSC.vl P Bs e (d.L.nabs.1 Ψ0) ρ q0 = B ρ ζ := by
    unfold SSC.vl
    rw [t2, fnZ_val P (hAB ρ).2]

  have vm : SSC.vl P Bs e ((ThetaNF P d).1 Ψ0) ρ q0 = m := by
    unfold SSC.vl
    rw [hm Ψ0, t0, GTRT.dzQ_one P hTT, GTRT.dzbQ_one P hTT, mul_zero, mul_zero, sub_zero, zero_add]
    show m * 1 = m
    ring
  have v3 : SSC.vl P Bs e ((d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Ψ0) ρ q0 = ((rhoSum P ρ : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  have v4 : SSC.vl P Bs e ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Ψ0) ρ q0 =
      ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  clear_value Ψ0

  have hfn := fun Ψ => SSC.vl_fn P Bs X d hyp e Ψ ρ q0
  rw [GTRT.theta_fst, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_add P Bs hpl hk2 e he,
    GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_smul P Bs hpl hk2 e he, (hfn _).1, (hfn _).2.1, (hfn _).2.2,
    v3, v4, v1, v2, hLTT] at vm
  have hq : q0.1.2 = ζ := rfl
  rw [hq] at vm
  have hG : (Complex.normSq ζ : ℂ) - (P.TT : ℂ) ≠ 0 := by
    have : P.TT < Complex.normSq ζ := hζ
    intro h0
    have h1 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have : Complex.normSq ζ - P.TT = 0 := by exact_mod_cast h1
    linarith
  rw [← vm]
  push_cast
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
