import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
open UpperHalfPlane hiding I

namespace GlobalTheory.HilbertThetaSeries.ArchLift

private noncomputable def cR (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i)

private noncomputable def cC (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cR i j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cR_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cR i j x = x i j := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cC_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cC i j x = (x i j : ℂ) := rfl

/- English proof (translation)
Establish `r : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => x i j) (cR i j) x0` using `fun i j => (cR i j).hasFDerivAt`. Establish `c : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => (x i j : ℂ)) (cC i j) x0` using `fun i j => (cC i j).hasFDerivAt`. Establish `hd` using `((r 0 0).fun_mul (r 1 1)).fun_sub ((r 0 1).fun_mul (r 1 0))`. Establish `hd2` using `hd.rpow_const (p := (k : ℝ) / 2) (Or.inl (by simp [h00, h01, h10, h11]))`. Establish `hd3` using `Complex.ofRealCLM.hasFDerivAt.comp x0 hd2`.

Establish `hden` using `((c 1 0).mul_const Complex.I).fun_add (c 1 1)`. Establish `hnum` using `((c 0 0).mul_const Complex.I).fun_add (c 0 1)`. Establish `hne : (x0 1 0 : ℂ) * Complex.I + x0 1 1 ≠ 0` using `by simp [h10, h11]`. Establish `hz` using `(hasDerivAt_zpow (-(k : ℤ)) _ (Or.inl hne)).comp_hasFDerivAt x0 hden`. Establish `hi` using `(hasDerivAt_inv hne).comp_hasFDerivAt x0 hden`.

Establish `hq` using `hnum.fun_mul hi`. Establish `hF2 : HasDerivAt F F' (((x0 0 0 : ℂ) * Complex.I + x0 0 1) * ((x0 1 0 : ℂ) * Complex.I + x0 1 1)⁻¹)`. Simplify `hF` using `[h00, h01, h10, h11]`. Establish `hc` using `hF2.comp_hasFDerivAt x0 hq`. Use `⟨_, (hd3.fun_mul hz).fun_mul hc, fun v => ?_⟩` and prove the remaining obligations.

Simplify using `[h00, h01, h10, h11, cR_apply, cC_apply]`. Take the linear combination `(-(v 1 0 : ℂ) * F') * Complex.I_mul_I`.
-/
theorem key (k : ℕ) (F : ℂ → ℂ) (F' : ℂ) (hF : HasDerivAt F F' Complex.I) (x0 : Fin 2 → Fin 2 → ℝ)
    (h00 : x0 0 0 = 1) (h01 : x0 0 1 = 0) (h10 : x0 1 0 = 0) (h11 : x0 1 1 = 1) :
    ∃ L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ,
      HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          F (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) L x0 ∧
      ∀ v : Fin 2 → Fin 2 → ℝ, L v = (k : ℂ) / 2 * (v 0 0 + v 1 1) * F Complex.I - k * (v 1 0 * Complex.I + v 1 1) * F Complex.I +
        (v 0 0 * Complex.I + v 0 1 + v 1 0 - v 1 1 * Complex.I) * F' := by
  have r : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => x i j) (cR i j) x0 := fun i j => (cR i j).hasFDerivAt
  have c : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => (x i j : ℂ)) (cC i j) x0 := fun i j => (cC i j).hasFDerivAt
  have hd := ((r 0 0).fun_mul (r 1 1)).fun_sub ((r 0 1).fun_mul (r 1 0))
  have hd2 := hd.rpow_const (p := (k : ℝ) / 2) (Or.inl (by simp [h00, h01, h10, h11]))
  have hd3 := Complex.ofRealCLM.hasFDerivAt.comp x0 hd2
  have hden := ((c 1 0).mul_const Complex.I).fun_add (c 1 1)
  have hnum := ((c 0 0).mul_const Complex.I).fun_add (c 0 1)
  have hne : (x0 1 0 : ℂ) * Complex.I + x0 1 1 ≠ 0 := by simp [h10, h11]
  have hz := (hasDerivAt_zpow (-(k : ℤ)) _ (Or.inl hne)).comp_hasFDerivAt x0 hden
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x0 hden
  have hq := hnum.fun_mul hi
  have hF2 : HasDerivAt F F' (((x0 0 0 : ℂ) * Complex.I + x0 0 1) * ((x0 1 0 : ℂ) * Complex.I + x0 1 1)⁻¹) := by
    simpa [h00, h01, h10, h11] using hF
  have hc := hF2.comp_hasFDerivAt x0 hq
  refine ⟨_, (hd3.fun_mul hz).fun_mul hc, fun v => ?_⟩
  simp [h00, h01, h10, h11, cR_apply, cC_apply]
  linear_combination (-(v 1 0 : ℂ) * F') * Complex.I_mul_I

noncomputable def arch {ι : Type} [Fintype ι] (k : ℕ) (g : (ι → ℂ) → ℂ) (x : Fin 2 → Fin 2 → ι → ℝ) : ℂ :=
  (((∏ v, (x 0 0 v * x 1 1 v - x 0 1 v * x 1 0 v)) ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
    (∏ v, ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)) ^ (-(k : ℤ)) *
      g fun v => ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrArg Complex.re h0`. Establish `h2` using `congrArg Complex.im h0`. Simplify using `at h1 h2`. Simplify using `[h1, h2] at h`.
-/
theorem den_ne {a b c d : ℝ} (h : 0 < a * d - b * c) : (c : ℂ) * Complex.I + d ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  simp at h1 h2
  simp [h1, h2] at h

/- English proof (translation)
Establish `h1` using `Complex.normSq_pos.2 (den_ne h)`. Establish `: (((a : ℂ) * Complex.I + b) * ((c : ℂ) * Complex.I + d)⁻¹).im = (a * d - b * c) / Complex.normSq ((c : ℂ) * Complex.I + d)`. Rewrite using `[← div_eq_mul_inv, Complex.div_im]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Check the signs of the components of the expression.
-/
theorem im_pos' {a b c d : ℝ} (h : 0 < a * d - b * c) :
    0 < (((a : ℂ) * Complex.I + b) * ((c : ℂ) * Complex.I + d)⁻¹).im := by
  have h1 := Complex.normSq_pos.2 (den_ne h)
  have : (((a : ℂ) * Complex.I + b) * ((c : ℂ) * Complex.I + d)⁻¹).im =
      (a * d - b * c) / Complex.normSq ((c : ℂ) * Complex.I + d) := by
    rw [← div_eq_mul_inv, Complex.div_im]
    simp
    ring
  rw [this]
  positivity

/- English proof (translation)
Rewrite using `[Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)`.
-/
theorem isOpen_up {ι : Type} [Fintype ι] : IsOpen {z : ι → ℂ | ∀ v, 0 < (z v).im} := by
  rw [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)

/- English proof (translation)
Establish `r : ∀ i j v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => x i j v) x`. Introduce `i j v`. Use `fun_prop`. Establish `c : ∀ i j v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => (x i j v : ℂ)) x` using `fun i j v => Complex.ofRealCLM.contDiff.contDiffAt.comp x (r i j v)`. Establish `hden : ∀ v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => (x 1 0 v : ℂ) * Complex.I + x 1 1 v) x` using `fun v => ((c 1 0 v).mul contDiffAt_const).add (c 1 1 v)`.

Establish `h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => (∏ v, (x 0 0 v * x 1 1 v - x 0 1 v * x 1 0 v)) ^ ((k : ℝ) / 2)) x` using `(contDiffAt_prod fun v _ => ((r 0 0 v).mul (r 1 1 v)).sub ((r 0 1 v).mul (r 1 0 v))).rpow_const_of_ne (Finset.prod_pos fun v _ => hx v).ne'`. Establish `h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => (∏ v, ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)) ^ (-(k : ℤ))) x`. Simplify using `only [zpow_neg, zpow_natCast]`. Conclude with `((contDiffAt_prod fun v _ => hden v).pow k).inv (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => den_ne (hx v)))`. Establish `h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (x : Fin 2 → Fin 2 → ι → ℝ) (v : ι) => ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹) x` using `contDiffAt_pi.2 fun v => (((c 0 0 v).mul contDiffAt_const).add (c 0 1 v)).mul ((hden v).inv (den_ne (hx v)))`.

Establish `h4 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (fun v : ι => ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹)` using `((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn isOpen_up hg _ (fun v => im_pos' (hx v))).contDiffAt).restrict_scalars ℝ`. Conclude with `((Complex.ofRealCLM.contDiff.contDiffAt.comp x h1).mul h2).mul (h4.comp x h3)`.
-/
theorem arch_smooth {ι : Type} [Fintype ι] (k : ℕ) (g : (ι → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g {z | ∀ v, 0 < (z v).im}) (x : Fin 2 → Fin 2 → ι → ℝ)
    (hx : ∀ v, 0 < x 0 0 v * x 1 1 v - x 0 1 v * x 1 0 v) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (arch k g) x := by
  have r : ∀ i j v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => x i j v) x := by
    intro i j v; fun_prop
  have c : ∀ i j v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => (x i j v : ℂ)) x :=
    fun i j v => Complex.ofRealCLM.contDiff.contDiffAt.comp x (r i j v)
  have hden : ∀ v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → Fin 2 → ι → ℝ => (x 1 0 v : ℂ) * Complex.I + x 1 1 v) x :=
    fun v => ((c 1 0 v).mul contDiffAt_const).add (c 1 1 v)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ =>
      (∏ v, (x 0 0 v * x 1 1 v - x 0 1 v * x 1 0 v)) ^ ((k : ℝ) / 2)) x :=
    (contDiffAt_prod fun v _ => ((r 0 0 v).mul (r 1 1 v)).sub ((r 0 1 v).mul (r 1 0 v))).rpow_const_of_ne
      (Finset.prod_pos fun v _ => hx v).ne'
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ =>
      (∏ v, ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)) ^ (-(k : ℤ))) x := by
    simp only [zpow_neg, zpow_natCast]
    exact ((contDiffAt_prod fun v _ => hden v).pow k).inv
      (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => den_ne (hx v)))
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (x : Fin 2 → Fin 2 → ι → ℝ) (v : ι) =>
      ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹) x :=
    contDiffAt_pi.2 fun v => (((c 0 0 v).mul contDiffAt_const).add (c 0 1 v)).mul ((hden v).inv (den_ne (hx v)))
  have h4 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (fun v : ι =>
      ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹) :=
    ((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn isOpen_up hg _ (fun v => im_pos' (hx v))).contDiffAt).restrict_scalars ℝ
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp x h1).mul h2).mul (h4.comp x h3)

/- English proof (translation)
Use `set x1 : Fin 2 → Fin 2 → ι → ℝ := Matrix.of.symm 1 with hx1`. Use `set y1 : Fin 2 → Fin 2 → ℝ := Matrix.of.symm 1 with hy1`. Establish `hgI : DifferentiableAt ℂ g (Function.update (fun _ => Complex.I) v Complex.I)`. Rewrite using `[Function.update_eq_self_iff.2 rfl]`. Conclude with `hg.differentiableAt (isOpen_up.mem_nhds fun _ => by simp)`.

Establish `hF : DifferentiableAt ℂ (fun z => g (Function.update (fun _ => Complex.I) v z)) Complex.I` using `hgI.comp Complex.I (hasFDerivAt_update _ _).differentiableAt`. Take `⟨L, hL, hv⟩` from `key k _ _ hF.hasDerivAt y1 (by simp [hy1]) (by simp [hy1]) (by simp [hy1]) (by simp [hy1])`. Set `S : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ι → ℝ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) v).comp (cR i j)`. Establish `hS : ∀ y, S y = fun i j => Pi.single v (y i j)` using `fun y => rfl`. Set `e : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ι → ℝ)` to `fun y => S y + (x1 - S y1)`.

Establish `he : HasFDerivAt e S y1` using `S.hasFDerivAt.add_const _`. Establish `he1 : e y1 = x1` using `by simp [e]`. Establish `hev : ∀ y i j, e y i j v = y i j`. Introduce `y i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [e, hS, hx1, hy1]`.

Establish `hew : ∀ y i j w, w ≠ v → e y i j w = y1 i j`. Introduce `y i j w hw`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [e, hS, hx1, hy1, hw]`. Establish `hA : DifferentiableAt ℝ (arch k g) (e y1)`. Rewrite using `[he1]`.

Conclude with `(arch_smooth k g hg x1 (by simp [hx1])).differentiableAt (by simp)`. Establish `hc` using `hA.hasFDerivAt.comp y1 he`. Establish `heq : arch k g ∘ e = fun x : Fin 2 → Fin 2 → ℝ => (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) * g (Function.update (fun _ => Complex.I) v (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹))`. Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp, arch]`.

Rewrite using `[Finset.prod_eq_single v (fun w _ hw => by simp [hew y _ _ w hw, hy1]) (by simp), Finset.prod_eq_single v (fun w _ hw => by simp [hew y _ _ w hw, hy1]) (by simp)]`. Simplify using `only [hev]`. Use `congr 2`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Simplify using `[hev]`. Simplify using `[hew y _ _ w hw, hy1, hw]`. Rewrite `hc` using `[heq, he1]`. Use `⟨deriv (fun z => g (Function.update (fun _ => Complex.I) v z)) Complex.I, fun y => ?_⟩` and prove the remaining obligations.

Use `hv y` as an intermediate fact. Rewrite `this` using `[hL.unique hc, Function.update_eq_self_iff.2 rfl]`. Conclude with `this`.
-/
theorem arch_der {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) (g : (ι → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g {z | ∀ v, 0 < (z v).im}) (v : ι) :
    ∃ F' : ℂ, ∀ y : Fin 2 → Fin 2 → ℝ,
      fderiv ℝ (arch k g) (Matrix.of.symm 1) (fun i j => Pi.single v (y i j)) =
        (k : ℂ) / 2 * (y 0 0 + y 1 1) * g (fun _ => Complex.I) - k * (y 1 0 * Complex.I + y 1 1) * g (fun _ => Complex.I) +
        (y 0 0 * Complex.I + y 0 1 + y 1 0 - y 1 1 * Complex.I) * F' := by
  set x1 : Fin 2 → Fin 2 → ι → ℝ := Matrix.of.symm 1 with hx1
  set y1 : Fin 2 → Fin 2 → ℝ := Matrix.of.symm 1 with hy1
  have hgI : DifferentiableAt ℂ g (Function.update (fun _ => Complex.I) v Complex.I) := by
    rw [Function.update_eq_self_iff.2 rfl]
    exact hg.differentiableAt (isOpen_up.mem_nhds fun _ => by simp)
  have hF : DifferentiableAt ℂ (fun z => g (Function.update (fun _ => Complex.I) v z)) Complex.I :=
    hgI.comp Complex.I (hasFDerivAt_update _ _).differentiableAt
  obtain ⟨L, hL, hv⟩ := key k _ _ hF.hasDerivAt y1 (by simp [hy1]) (by simp [hy1]) (by simp [hy1]) (by simp [hy1])
  let S : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ι → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
      (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) v).comp (cR i j)
  have hS : ∀ y, S y = fun i j => Pi.single v (y i j) := fun y => rfl
  let e : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ι → ℝ) := fun y => S y + (x1 - S y1)
  have he : HasFDerivAt e S y1 := S.hasFDerivAt.add_const _
  have he1 : e y1 = x1 := by simp [e]
  have hev : ∀ y i j, e y i j v = y i j := by
    intro y i j
    fin_cases i <;> fin_cases j <;> simp [e, hS, hx1, hy1]
  have hew : ∀ y i j w, w ≠ v → e y i j w = y1 i j := by
    intro y i j w hw
    fin_cases i <;> fin_cases j <;> simp [e, hS, hx1, hy1, hw]
  have hA : DifferentiableAt ℝ (arch k g) (e y1) := by
    rw [he1]
    exact (arch_smooth k g hg x1 (by simp [hx1])).differentiableAt (by simp)
  have hc := hA.hasFDerivAt.comp y1 he
  have heq : arch k g ∘ e = fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          g (Function.update (fun _ => Complex.I) v
            (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) := by
    funext y
    simp only [Function.comp, arch]
    rw [Finset.prod_eq_single v (fun w _ hw => by simp [hew y _ _ w hw, hy1]) (by simp),
      Finset.prod_eq_single v (fun w _ hw => by simp [hew y _ _ w hw, hy1]) (by simp)]
    simp only [hev]
    congr 2
    funext w
    by_cases hw : w = v
    · subst hw
      simp [hev]
    · simp [hew y _ _ w hw, hy1, hw]
  rw [heq, he1] at hc
  refine ⟨deriv (fun z => g (Function.update (fun _ => Complex.I) v z)) Complex.I, fun y => ?_⟩
  have := hv y
  rw [hL.unique hc, Function.update_eq_self_iff.2 rfl] at this
  exact this

end GlobalTheory.HilbertThetaSeries.ArchLift

/- English proof (translation)
Introduce `F _ _ _ k f hf`. Use `⟨ArchLift.arch k fun z => f fun v => ofComplex (z v), fun h hh => ?_, fun x hx => ?_, fun v D hD => ?_⟩` and prove the remaining obligations. Establish `hp : ∀ v, 0 < h.val 0 0 v * h.val 1 1 v - h.val 0 1 v * h.val 1 0 v` using `fun v => by`. Simplify `hh v` using `[Matrix.det_fin_two]`. Establish `hz : (fun v => ofComplex (((h.val 0 0 v : ℂ) * Complex.I + h.val 0 1 v) * ((h.val 1 0 v : ℂ) * Complex.I + h.val 1 1 v)⁻¹)) = act h fun _ => UpperHalfPlane.I`.

Use function extensionality and compare the values at `v`. Establish `hd : 0 < (GlobalTheory.HilbertThetaSeries.cmp v h).det.val`. Simplify `hp v` using `[GlobalTheory.HilbertThetaSeries.cmp, Matrix.det_fin_two]`. Rewrite using `[← ofComplex_apply (act h (fun _ => UpperHalfPlane.I) v), act, coe_smul_of_det_pos hd]`. Simplify using `[num, denom, GlobalTheory.HilbertThetaSeries.cmp, div_eq_mul_inv]`.

Establish `ha : ∀ v, |h.val.det v| = h.val 0 0 v * h.val 1 1 v - h.val 0 1 v * h.val 1 0 v` using `fun v => by`. Rewrite using `[abs_of_pos (hh v)]`. Simplify using `[Matrix.det_fin_two]`. Simplify using `only [ArchLift.arch, sl, sl0, Matrix.of_symm_apply, hz, ha, mul_assoc, zpow_neg, zpow_natCast, inv_pow]`. Simplify using `[denom, GlobalTheory.HilbertThetaSeries.cmp]`.

Conclude with `(ArchLift.arch_smooth k _ hf x fun v => by simpa [Matrix.det_fin_two] using hx v).contDiffWithinAt`. Take `⟨F', hF⟩` from `ArchLift.arch_der k _ hf v`. Establish `hE : ∀ i j : Fin 2, (Matrix.of.symm (Matrix.single i j (Pi.single v (1 : ℝ))) : Fin 2 → Fin 2 → InfinitePlace F → ℝ) = fun a b => Pi.single v (Matrix.single i j (1 : ℝ) a b)`. Introduce `i j`. Use function extensionality and compare the values at `a b`.

Simplify using `only [Matrix.single, Matrix.of_symm_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hI : ofComplex Complex.I = UpperHalfPlane.I`. Rewrite using `[← coe_I, ofComplex_apply]`. Establish `hD'` using `fun i j => (hD i j).trans ((congrArg _ (hE i j)).trans (hF fun a b => Matrix.single i j (1 : ℝ) a b))`.

Simplify using `only [hD', hI]`. Simplify using `[Matrix.single]`. Use `⟨Or.inl (mul_comm _ _), ?_⟩` and prove the remaining obligations. Take the linear combination `(k * f fun _ => UpperHalfPlane.I) * Complex.I_mul_I`.
-/
theorem GlobalTheory.HilbertThetaSeries.arch_lift : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)] (k : ℕ) (f : Hn F → ℂ), Hol f → ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ, (∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → A (Matrix.of.symm h.val) = sl k h f fun _ => UpperHalfPlane.I) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A {x | ∀ v, 0 < (Matrix.of x).det v} ∧ ∀ v, ∀ D : Fin 2 → Fin 2 → ℂ, (∀ i j, D i j = fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single i j (Pi.single v 1)))) → D 0 1 - D 1 0 = Complex.I * k * f (fun _ => UpperHalfPlane.I) ∧ D 0 0 - D 1 1 = Complex.I * (D 0 1 + D 1 0) := by
  intro F _ _ _ k f hf
  refine ⟨ArchLift.arch k fun z => f fun v => ofComplex (z v), fun h hh => ?_, fun x hx => ?_, fun v D hD => ?_⟩
  · have hp : ∀ v, 0 < h.val 0 0 v * h.val 1 1 v - h.val 0 1 v * h.val 1 0 v := fun v => by
      simpa [Matrix.det_fin_two] using hh v
    have hz : (fun v => ofComplex (((h.val 0 0 v : ℂ) * Complex.I + h.val 0 1 v) *
        ((h.val 1 0 v : ℂ) * Complex.I + h.val 1 1 v)⁻¹)) = act h fun _ => UpperHalfPlane.I := by
      funext v
      have hd : 0 < (GlobalTheory.HilbertThetaSeries.cmp v h).det.val := by
        simpa [GlobalTheory.HilbertThetaSeries.cmp, Matrix.det_fin_two] using hp v
      rw [← ofComplex_apply (act h (fun _ => UpperHalfPlane.I) v), act, coe_smul_of_det_pos hd]
      simp [num, denom, GlobalTheory.HilbertThetaSeries.cmp, div_eq_mul_inv]
    have ha : ∀ v, |h.val.det v| = h.val 0 0 v * h.val 1 1 v - h.val 0 1 v * h.val 1 0 v := fun v => by
      rw [abs_of_pos (hh v)]; simp [Matrix.det_fin_two]
    simp only [ArchLift.arch, sl, sl0, Matrix.of_symm_apply, hz, ha, mul_assoc, zpow_neg, zpow_natCast, inv_pow]
    simp [denom, GlobalTheory.HilbertThetaSeries.cmp]
  · exact (ArchLift.arch_smooth k _ hf x fun v => by simpa [Matrix.det_fin_two] using hx v).contDiffWithinAt
  · obtain ⟨F', hF⟩ := ArchLift.arch_der k _ hf v
    have hE : ∀ i j : Fin 2, (Matrix.of.symm (Matrix.single i j (Pi.single v (1 : ℝ))) :
        Fin 2 → Fin 2 → InfinitePlace F → ℝ) = fun a b => Pi.single v (Matrix.single i j (1 : ℝ) a b) := by
      intro i j
      funext a b
      simp only [Matrix.single, Matrix.of_symm_apply, Matrix.of_apply]
      split_ifs <;> simp
    have hI : ofComplex Complex.I = UpperHalfPlane.I := by
      rw [← coe_I, ofComplex_apply]
    have hD' := fun i j => (hD i j).trans ((congrArg _ (hE i j)).trans (hF fun a b => Matrix.single i j (1 : ℝ) a b))
    simp only [hD', hI]
    simp [Matrix.single]
    refine ⟨Or.inl (mul_comm _ _), ?_⟩
    linear_combination (k * f fun _ => UpperHalfPlane.I) * Complex.I_mul_I

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.arch_lift | exact GlobalTheory.HilbertThetaSeries.arch_lift | (intros; apply GlobalTheory.HilbertThetaSeries.arch_lift <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)] (k : ℕ) (f : Hn F → ℂ), Hol f → ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ, (∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → A (Matrix.of.symm h.val) = sl k h f fun _ => UpperHalfPlane.I) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A {x | ∀ v, 0 < (Matrix.of x).det v} ∧ ∀ v, ∀ D : Fin 2 → Fin 2 → ℂ, (∀ i j, D i j = fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single i j (Pi.single v 1)))) → D 0 1 - D 1 0 = Complex.I * k * f (fun _ => UpperHalfPlane.I) ∧ D 0 0 - D 1 1 = Complex.I * (D 0 1 + D 1 0) := by
  first | exact @GlobalTheory.HilbertThetaSeries.arch_lift | exact GlobalTheory.HilbertThetaSeries.arch_lift | (intros; apply GlobalTheory.HilbertThetaSeries.arch_lift <;> assumption)
