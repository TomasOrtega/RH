import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCTheta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def BsAt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0) :
    B.RealPlaceData P.k P.r Wp Wq :=
  { Bs with μsec := μ0, sec := h0 }

def GTRMove : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0)
      (e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameB P (BsAt P Bs μ0 h0) e0 →
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e Φ = trR P (BsAt P Bs μ0 h0) e0 Φ

def GTRConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ KapF P Bs d e ∧
      ∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ'

def GTRRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ ρ : M.Ty P, ∃ m : ℤ, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + ((m : ℂ)) • trR P Bs e Φ ρ

def GTRInt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ ρ : M.Ty P, ∃ n : ℤ, uSum P - rhoSum P ρ = n

def GTRTrans : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ (ρ : M.Ty P) (m : ℂ),
        (∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
          trR P Bs e ((ThetaNF P d).1 Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
            fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + m • trR P Bs e Φ ρ) →
        ∀ ζ ∈ Ann P, ζ * A ρ ζ + star ζ * B ρ ζ =
          m + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)

/- English proof (translation)
Introduce `j hj`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ (a j)).mp ?_` and prove the remaining obligations. Introduce `f`. Establish `hp0 : (∑ i ∈ Finset.range N, Polynomial.C (f (a i)) * Polynomial.X ^ i : Polynomial ℂ) = 0`. Apply `Polynomial.funext` to reduce the goal to its premises.

Introduce `Y`. Establish `hY` using `congrArg f (h Y)`. Simplify using `only [map_sum, map_smul, smul_eq_mul, map_zero] at hY`. Simplify using `only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]`. Rewrite using `[← hY]`.

Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`. Establish `hc` using `congrArg (fun q => q.coeff j) hp0`. Simplify `hc` using `[Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj]`.
-/
theorem poly_coeff_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = 0) : ∀ j < N, a j = 0 := by
  intro j hj
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (a j)).mp ?_
  intro f
  have hp0 : (∑ i ∈ Finset.range N, Polynomial.C (f (a i)) * Polynomial.X ^ i : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro Y
    have hY := congrArg f (h Y)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hY
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← hY]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hc := congrArg (fun q => q.coeff j) hp0
  simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj] using hc

/- English proof (translation)
Introduce `j hj`. Establish `hz : ∀ Y : ℂ, ∑ i ∈ Finset.range N, Y ^ i • (a - b) i = 0`. Introduce `Y`. Simplify using `only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, h Y, sub_self]`. Conclude with `sub_eq_zero.mp (poly_coeff_zero N (a - b) hz j hj)`.
-/
theorem poly_coeff_eq {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a b : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = ∑ j ∈ Finset.range N, Y ^ j • b j) :
    ∀ j < N, a j = b j := by
  intro j hj
  have hz : ∀ Y : ℂ, ∑ i ∈ Finset.range N, Y ^ i • (a - b) i = 0 := by
    intro Y
    simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, h Y, sub_self]
  exact sub_eq_zero.mp (poly_coeff_zero N (a - b) hz j hj)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem pr_fst_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (Y : ℂ) (x : Q.Pr V) : (Y • x).1 = Y • x.1 := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_fst_add {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : Q.Pr V) : (x + y).1 = x.1 + y.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_fst_one {V : Type*} [AddCommGroup V] [Module ℂ V] : (1 : Q.Pr V).1 = 1 := rfl

/- English proof (translation)
The claim follows from `Prod.fst_sum`.
-/
theorem pr_fst_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (s : Finset ℕ) (f : ℕ → Q.Pr V) :
    (∑ j ∈ s, f j).1 = ∑ j ∈ s, (f j).1 := Prod.fst_sum

/- English proof (translation)
Establish `hpos : 0 < Complex.normSq ζ - P.TT` using `sub_pos.mpr hζ`. Establish `hne : ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ≠ 0`. Rewrite using `[← Complex.ofReal_sub]`. Conclude with `hpos.ne'` after adjusting the coercions. Establish `haC : M.aC P ρ = uSum P / 2 - rhoSum P ρ` using `rfl`.

Establish `hre` using `congrArg Complex.re hA`. Establish `h1 : (ζ * A + star ζ * star A).re = 2 * (ζ * A).re`. Rewrite using `[← star_mul', Complex.add_re, Complex.star_def, Complex.conj_re]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hre` using `[h1, Complex.add_re, Complex.intCast_re, Complex.ofReal_re]`.

Establish `h2 : ζ * modA P ρ ζ = ((M.aC P ρ * Complex.normSq ζ / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)`. Unfold `modA`. Rewrite using `[Complex.star_def]`. Use `push_cast`. Rewrite using `[← Complex.mul_conj]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_sub, Complex.sub_re, h2, Complex.ofReal_re, haC]`. Establish `hA' : (ζ * A).re = ((m : ℝ) + (-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT))) / 2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hA']`.

Use `push_cast`. Rewrite using `[← hN]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem final_arith (P : M.Par) (ρ : M.Ty P) (A ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (m N : ℤ)
    (hN : uSum P - rhoSum P ρ = N)
    (hA : ζ * A + star ζ * star A =
      (m : ℂ) + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)) :
    (ζ * (modA P ρ ζ - A)).re = ((N - m : ℤ) : ℝ) / 2 := by
  have hpos : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  have hne : ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hpos.ne'
  have haC : M.aC P ρ = uSum P / 2 - rhoSum P ρ := rfl
  have hre := congrArg Complex.re hA
  have h1 : (ζ * A + star ζ * star A).re = 2 * (ζ * A).re := by
    rw [← star_mul', Complex.add_re, Complex.star_def, Complex.conj_re]; ring
  rw [h1, Complex.add_re, Complex.intCast_re, Complex.ofReal_re] at hre
  have h2 : ζ * modA P ρ ζ = ((M.aC P ρ * Complex.normSq ζ / (Complex.normSq ζ - P.TT) : ℝ) : ℂ) := by
    unfold modA
    rw [Complex.star_def]
    push_cast
    rw [← Complex.mul_conj]
    field_simp
  rw [mul_sub, Complex.sub_re, h2, Complex.ofReal_re, haC]
  have hA' : (ζ * A).re = ((m : ℝ) + (-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT))) / 2 := by
    linarith
  rw [hA']
  push_cast
  rw [← hN]
  field_simp
  ring

def GTCRefTraceOfCut : Prop :=
  GTRMove → GTRConst → GTRTopNF → GTRTopAct → GTRRot → GTRInt → GTRTrans → GTCReal → GTCRefTrace

/- English proof (translation)
Introduce `hMove hConst hNF hAct hRot hInt hTrans hReal Wp Wq _ _ _ _ _ _ P Bs X d hyp`. Take `⟨hpl, hk, hcs, hL, hS, hR, hQ⟩` from `hyp`. Establish `hcs0` using `Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos`. Use `set Bs0 := BsAt P Bs (TheSec.theSection P.k P.r Bs.z Bs.z') hcs0.1 with hBs0`. Establish `hyp0 : GTHyp P Bs0 X d` using `⟨hpl, hk, hcs0, hL, hS, hR, hQ⟩`.

Take `⟨e0, he0, hk0, hc0⟩` from `hConst Wp Wq P Bs0 X d hyp0`. Take `⟨A, B, hAB, hC⟩` from `gauge_locality_holds Wp Wq P Bs0 X d hyp0 e0 he0 hk0`. Take `⟨cA, hcA, sA, hsA⟩` from `hAct Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk X`. Establish `hTT : d.L.TT = ((P.TT : ℝ) : ℂ)`. Rewrite using `[hL.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]`.

Both sides reduce to the same expression. Take `⟨cN, hcN, sN, hsN⟩` from `hNF P _ d hpl.1 hk hS hR hTT`. Establish `hcoef : ∀ Y : ℂ, ∑ j ∈ Finset.range (P.k + 2), Y ^ j • cA j = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • (cN j).1`. Introduce `Y`. Rewrite using `[← hcA Y]`.

Establish `h1 : X.t Y 0 0 = (X.QQ Y 0 0).1` using `rfl`. Rewrite using `[h1, hQ Y, hcN Y, pr_fst_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => pr_fst_smul _ _`. Establish `hk'` using `poly_coeff_eq (P.k + 2) cA (fun j => (cN j).1) hcoef P.k (by omega)`. Establish `hTh : (ThetaNF P d).1 = cA P.k - ((sN : ℂ)) • (1 : Module.End ℂ _)`.

Rewrite using `[hk']`. Use `show (ThetaNF P d).1 = (cN P.k).1 - _`. Rewrite using `[hsN, pr_fst_add, pr_fst_smul, pr_fst_one, add_sub_cancel_right]`. Establish `hpt : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', (((ThetaNF P d).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)), Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q …`. Introduce `Φ x hx`.

Rewrite using `[hTh, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, hsA Φ x hx]`. Use `push_cast`. Rewrite using `[sub_smul]`. Normalize the expressions using the abelian group laws. Take `⟨e, he, htr⟩` from `hMove Wp Wq P Bs hpl hk _ hcs0.1 e0 he0`.

Establish `htrF : trR P Bs e = trR P Bs0 e0` using `funext htr`. Use `⟨e, he, ?_, A, B, hAB, ?_, fun ρ => ?_⟩` and prove the remaining obligations. Introduce `f Φ`. Rewrite using `[htrF]`. Conclude with `hk0 f Φ`.

Introduce `Φ ρ`. Rewrite using `[htrF]`. Conclude with `hC Φ ρ`. Take `⟨m, hm⟩` from `hRot Wp Wq P Bs0 X d hyp0 rfl e0 he0 hk0 hc0 (ThetaNF P d).1 (sA - sN) hpt ρ`. Take `⟨N, hN⟩` from `hInt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk ρ`.

Use `⟨N - m, fun ζ hζ => ?_⟩` and prove the remaining obligations. Establish `hT` using `hTrans Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ (m : ℂ) hm ζ hζ`. Rewrite `hT` using `[hReal Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ ζ hζ]`. Conclude with `final_arith P ρ (A ρ ζ) ζ hζ m N hN hT`.
-/
theorem gTCRefTrace_of_cut : GTCRefTraceOfCut := by
  intro hMove hConst hNF hAct hRot hInt hTrans hReal Wp Wq _ _ _ _ _ _ P Bs X d hyp
  obtain ⟨hpl, hk, hcs, hL, hS, hR, hQ⟩ := hyp
  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set Bs0 := BsAt P Bs (TheSec.theSection P.k P.r Bs.z Bs.z') hcs0.1 with hBs0
  have hyp0 : GTHyp P Bs0 X d := ⟨hpl, hk, hcs0, hL, hS, hR, hQ⟩
  obtain ⟨e0, he0, hk0, hc0⟩ := hConst Wp Wq P Bs0 X d hyp0
  obtain ⟨A, B, hAB, hC⟩ := gauge_locality_holds Wp Wq P Bs0 X d hyp0 e0 he0 hk0

  obtain ⟨cA, hcA, sA, hsA⟩ := hAct Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk X
  have hTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hL.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨cN, hcN, sN, hsN⟩ := hNF P _ d hpl.1 hk hS hR hTT
  have hcoef : ∀ Y : ℂ, ∑ j ∈ Finset.range (P.k + 2), Y ^ j • cA j =
      ∑ j ∈ Finset.range (P.k + 2), Y ^ j • (cN j).1 := by
    intro Y
    rw [← hcA Y]
    have h1 : X.t Y 0 0 = (X.QQ Y 0 0).1 := rfl
    rw [h1, hQ Y, hcN Y, pr_fst_sum]
    exact Finset.sum_congr rfl fun j _ => pr_fst_smul _ _
  have hk' := poly_coeff_eq (P.k + 2) cA (fun j => (cN j).1) hcoef P.k (by omega)
  have hTh : (ThetaNF P d).1 = cA P.k - ((sN : ℂ)) • (1 : Module.End ℂ _) := by
    rw [hk']
    show (ThetaNF P d).1 = (cN P.k).1 - _
    rw [hsN, pr_fst_add, pr_fst_smul, pr_fst_one, add_sub_cancel_right]
  have hpt : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (((ThetaNF P d).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
          Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
            ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
          (((sA - sN : ℤ) : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    intro Φ x hx
    rw [hTh, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub,
      Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, hsA Φ x hx]
    push_cast
    rw [sub_smul]
    abel
  obtain ⟨e, he, htr⟩ := hMove Wp Wq P Bs hpl hk _ hcs0.1 e0 he0
  have htrF : trR P Bs e = trR P Bs0 e0 := funext htr
  refine ⟨e, he, ?_, A, B, hAB, ?_, fun ρ => ?_⟩
  · intro f Φ
    rw [htrF]
    exact hk0 f Φ
  · intro Φ ρ
    rw [htrF]
    exact hC Φ ρ
  · obtain ⟨m, hm⟩ := hRot Wp Wq P Bs0 X d hyp0 rfl e0 he0 hk0 hc0 (ThetaNF P d).1 (sA - sN) hpt ρ
    obtain ⟨N, hN⟩ := hInt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk ρ
    refine ⟨N - m, fun ζ hζ => ?_⟩
    have hT := hTrans Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ (m : ℂ) hm ζ hζ
    rw [hReal Wp Wq P Bs0 X d hyp0 e0 he0 hk0 A B hAB hC ρ ζ hζ] at hT
    exact final_arith P ρ (A ρ ζ) ζ hζ m N hN hT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
