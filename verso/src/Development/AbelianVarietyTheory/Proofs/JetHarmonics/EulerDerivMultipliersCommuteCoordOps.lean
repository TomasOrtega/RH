import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF.MulCoord

noncomputable section

/- English proof (translation)
Establish `hopen : IsOpen (OmX m)`. Establish `: OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0}` using `by ext x; simp [OmX]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Set `pr : Fin m → ((Fin m → ℂ) →L[ℝ] ℂ)` to `fun a => ContinuousLinearMap.proj a`.

Set `R : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ)` to `fun a => Complex.reCLM.comp (pr a)`. Set `J : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ)` to `fun a => Complex.imCLM.comp (pr a)`. Establish `h1 : ∀ a, HasFDerivAt (fun x : Fin m → ℂ => Real.log (R a x * R a x + J a x * J a x)) ((R a c * R a c + J a c * J a c)⁻¹ • ((R a c • R a + R a c • R a) + (J a c • J a + J a c • J a))) c`. Introduce `a`. Use `HasFDerivAt.log (((R a).hasFDerivAt.mul (R a).hasFDerivAt).add ((J a).hasFDerivAt.mul (J a).hasFDerivAt)) ?_` and prove the remaining obligations.

Establish `: Complex.normSq (c a) ≠ 0` using `by simpa using hc a`. Simplify `this` using `[R, J, pr, Complex.normSq_apply]`. Establish `h2` using `(HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => h1 a).add_const (Real.log γ)`. Use `⟨_, h2.congr_of_eventuallyEq ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hopen.mem_nhds hc] with x hx`.

Establish `hx' : ∀ a, Complex.normSq (x a) ≠ 0` using `fun a => by simpa using hx a`. Rewrite using `[map_prod, Real.log_mul (Finset.prod_ne_zero_iff.2 fun a _ => hx' a) hγ.ne', Real.log_prod (fun a _ => hx' a)]`. Simplify using `[R, J, pr, Complex.normSq_apply]`. Introduce `l w`. Rewrite using `[ContinuousLinearMap.sum_apply, Finset.sum_eq_single l]`.

Simplify using `[R, J, pr, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`. Simplify using `[R, J, pr, Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules.
-/
theorem exists_fderiv_log {m : ℕ} (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℝ,
      HasFDerivAt (fun x : Fin m → ℂ => Real.log (Complex.normSq (∏ a, x a) * γ)) D c ∧
      ∀ l w, D (Pi.single l w) = 2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l) := by
  classical
  have hopen : IsOpen (OmX m) := by
    have : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  let pr : Fin m → ((Fin m → ℂ) →L[ℝ] ℂ) := fun a => ContinuousLinearMap.proj a
  let R : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.reCLM.comp (pr a)
  let J : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.imCLM.comp (pr a)
  have h1 : ∀ a, HasFDerivAt (fun x : Fin m → ℂ => Real.log (R a x * R a x + J a x * J a x))
      ((R a c * R a c + J a c * J a c)⁻¹ • ((R a c • R a + R a c • R a) + (J a c • J a + J a c • J a))) c := by
    intro a
    refine HasFDerivAt.log (((R a).hasFDerivAt.mul (R a).hasFDerivAt).add
      ((J a).hasFDerivAt.mul (J a).hasFDerivAt)) ?_
    have : Complex.normSq (c a) ≠ 0 := by simpa using hc a
    simpa [R, J, pr, Complex.normSq_apply] using this
  have h2 := (HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => h1 a).add_const (Real.log γ)
  refine ⟨_, h2.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hopen.mem_nhds hc] with x hx
    have hx' : ∀ a, Complex.normSq (x a) ≠ 0 := fun a => by simpa using hx a
    rw [map_prod, Real.log_mul (Finset.prod_ne_zero_iff.2 fun a _ => hx' a) hγ.ne',
      Real.log_prod (fun a _ => hx' a)]
    simp [R, J, pr, Complex.normSq_apply]
  · intro l w
    rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single l]
    · simp [R, J, pr, Complex.normSq_apply]
      ring
    · intro b _ hb
      simp [R, J, pr, Pi.single_eq_of_ne hb]
    · simp

/- English proof (translation)
Take `⟨D, hD, hDl⟩` from `exists_fderiv_log γ hγ c hc`. Establish `hh : Differentiable ℝ (iteratedDeriv q fun u : ℝ => φ (Real.exp u))` using `ContDiff.differentiable_iteratedDeriv q hφ (by exact_mod_cast ENat.coe_lt_top q)`. Establish `h1 : HasDerivAt (iteratedDeriv q fun u : ℝ => φ (Real.exp u)) (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ)) (Real.log (Complex.normSq (∏ a, c a) * γ))`. Rewrite using `[LE.ld, iteratedDeriv_succ]`. Conclude with `(hh _).hasDerivAt`.

Establish `h2` using `Complex.ofRealCLM.hasFDerivAt.comp c (h1.comp_hasFDerivAt c hD)`. Establish `h3 : HasFDerivAt (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) _ c` using `HasFDerivAt.smul h2 hf.hasFDerivAt`. Establish `key : ∀ w, fderiv ℝ (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c (Pi.single l w) = ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • fderiv ℝ f c (Pi.single l w) + ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) * (2 * ((c l).re * w.re + (c l). …`. Introduce `w`. Rewrite using `[h3.fderiv, ← hDl]`.

Simplify using `[LE.ld]`. Establish `hn : ((Complex.normSq (c l) : ℝ) : ℂ) ≠ 0` using `by simpa using hc l`. Establish `e1 : c l * (((c l).re : ℂ) - Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ)`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring`. Establish `e2 : star (c l) * (((c l).re : ℂ) + Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ)`.

Apply the tactic sequence `apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring`. Prove the components needed by the constructor for the conclusion. Simplify using `only [pOp, if_pos hc, wirt, key]`. Simplify using `only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]`. Use `push_cast`.

Use `match_scalars`. Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Take the linear combination `(LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e1`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [pbOp, if_pos hc, wirtBar, key]`. Simplify using `only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]`. Use `push_cast`. Use `match_scalars`. Expand and normalize the polynomial expressions, which then agree.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_mul {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ)
    (q : ℕ) (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) (f : (Fin m → ℂ) → E)
    (hf : DifferentiableAt ℝ f c) (l : Fin m) :
    pOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c ∧
    pbOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pbOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c := by
  obtain ⟨D, hD, hDl⟩ := exists_fderiv_log γ hγ c hc
  have hh : Differentiable ℝ (iteratedDeriv q fun u : ℝ => φ (Real.exp u)) :=
    ContDiff.differentiable_iteratedDeriv q hφ (by exact_mod_cast ENat.coe_lt_top q)
  have h1 : HasDerivAt (iteratedDeriv q fun u : ℝ => φ (Real.exp u))
      (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ)) (Real.log (Complex.normSq (∏ a, c a) * γ)) := by
    rw [LE.ld, iteratedDeriv_succ]
    exact (hh _).hasDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp c (h1.comp_hasFDerivAt c hD)
  have h3 : HasFDerivAt (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) _ c :=
    HasFDerivAt.smul h2 hf.hasFDerivAt
  have key : ∀ w, fderiv ℝ (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c
      (Pi.single l w) = ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • fderiv ℝ f c (Pi.single l w) +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) *
          (2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l)) : ℝ) : ℂ) • f c := by
    intro w
    rw [h3.fderiv, ← hDl]
    simp [LE.ld]
  have hn : ((Complex.normSq (c l) : ℝ) : ℂ) ≠ 0 := by simpa using hc l
  have e1 : c l * (((c l).re : ℂ) - Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have e2 : star (c l) * (((c l).re : ℂ) + Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  constructor
  · simp only [pOp, if_pos hc, wirt, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e1
    · ring
  · simp only [pbOp, if_pos hc, wirtBar, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e2
    · ring

section radial

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Use `LinearMap.ext fun Φ => Subtype.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `c g`. Distinguish the cases in `hx : (c, g) ∈ Q.DomR k r z z'`. Conclude with `h Φ c g hx`. Conclude with `((A Φ).2.1 (c, g) hx).trans ((B Φ).2.1 (c, g) hx).symm`.
-/
theorem end_ext (A B : Module.End ℂ (Q.RadSp k r z z' π π'))
    (h : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = (B Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g) : A = B := by
  refine LinearMap.ext fun Φ => Subtype.ext ?_
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR k r z z'
  · exact h Φ c g hx
  · exact ((A Φ).2.1 (c, g) hx).trans ((B Φ).2.1 (c, g) hx).symm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

/- English proof (translation)
Take `⟨U, F, hU, hxU, hF, hΦ⟩` from `Φ.2.2.1 (c, g) hx`. Establish `h1 : DifferentiableAt ℝ F (c, g)` using `(hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)`. Establish `h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c` using `h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))`. Use `h2.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun c' : Fin r → ℂ => (c', g)) c` using `(continuous_id.prodMk continuous_const).continuousAt`.

Use `filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds hxU)] with c' hc'`. Conclude with `hΦ (c', g) hc' hx.2.1`.
-/
theorem differentiableAt_coord (Φ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) (g : Q.Mx k r)
    (hx : (c, g) ∈ Q.DomR k r z z') :
    DifferentiableAt ℝ (fun c' => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c' g) c := by
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := Φ.2.2.1 (c, g) hx
  have h1 : DifferentiableAt ℝ F (c, g) :=
    (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c :=
    h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))
  refine h2.congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun c' : Fin r → ℂ => (c', g)) c := (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds hxU)] with c' hc'
  exact hΦ (c', g) hc' hx.2.1

/- English proof (translation)
Use `end_ext _ _ fun Φ c g hx => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, hA _ c g hx, hB, hB, hA _ c g hx, smul_comm]`.
-/
theorem commute_of_mul (A B : Module.End ℂ (Q.RadSp k r z z' π π')) (a b : (Fin r → ℂ) → Q.Mx k r → ℂ)
    (hA : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = a c g • (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)
    (hB : P5.multiplicationOperator B b) : Commute A B := by
  refine end_ext _ _ fun Φ c g hx => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hA _ c g hx, hB, hB, hA _ c g hx, smul_comm]

end radial

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ _ φ W hφ hW q`. Use `⟨fun l => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩` and prove the remaining obligations. Use `end_ext _ _ fun Φ c g hx => ?_` and prove the remaining obligations. Establish `h` using `(euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).1`. Rewrite using `[LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]`.

Simplify using `only [Q.crd, opL, hW q Φ]`. Conclude with `h`. Use `end_ext _ _ fun Φ c g hx => ?_` and prove the remaining obligations. Establish `h` using `(euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).2`. Rewrite using `[LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]`.

Simplify using `only [Q.crd, opL, hW q Φ]`. Conclude with `h`. Conclude with `commute_of_mul _ _ (fun c _ => c l) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)`. Conclude with `commute_of_mul _ _ (fun c _ => (c l)⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)`. Conclude with `commute_of_mul _ _ (fun c _ => star (c l)) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)`.

Conclude with `commute_of_mul _ _ (fun c _ => (star (c l))⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)`. Conclude with `commute_of_mul _ _ (fun _ g => Q.fnVal P.k P.r Bs.z Bs.z' j g) _ (fun Φ c g hx => X.fn_apply j Φ (c, g) hx) (hW q)`.
-/
theorem mul_coord : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ _ φ W hφ hW q
  refine ⟨fun l => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).1
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).2
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · exact commute_of_mul _ _ (fun c _ => c l) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (c l)⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => star (c l)) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (star (c l))⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun _ g => Q.fnVal P.k P.r Bs.z Bs.z' j g) _
      (fun Φ c g hx => X.fn_apply j Φ (c, g) hx) (hW q)

end

end GlobalTheory.HatNF.MulCoord
