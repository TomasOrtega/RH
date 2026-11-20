import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocSec
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG

noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Mn (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cT {ι : Type} [Fintype ι] : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Mᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun r M => by
        ext i j
        simp [conjTranspose_apply, Complex.conj_ofReal] }

/- English proof (translation)
Establish `hf' : ∀ i j, ContDiffAt ℝ k (fun y => f y i j) x` using `fun i j => contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j`. Establish `hg' : ∀ i j, ContDiffAt ℝ k (fun y => g y i j) x` using `fun i j => contDiffAt_pi.1 (contDiffAt_pi.1 hg i) j`. Use `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`. Conclude with `ContDiffAt.sum fun l _ => (hf' i l).mul (hg' l j)`.
-/
theorem contDiffAt_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    {f g : E → Matrix ι ι ℂ} {x : E} {k : WithTop ℕ∞} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    ContDiffAt ℝ k (fun y => f y * g y) x := by
  have hf' : ∀ i j, ContDiffAt ℝ k (fun y => f y i j) x := fun i j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j
  have hg' : ∀ i j, ContDiffAt ℝ k (fun y => g y i j) x := fun i j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hg i) j
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hf' i l).mul (hg' l j)

/- English proof (translation)
The claim follows from `contDiff_iff_contDiffAt.2 fun x => contDiffAt_mul' hf.contDiffAt hg.contDiffAt`.
-/
theorem contDiff_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    {f g : E → Matrix ι ι ℂ} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun y => f y * g y) :=
  contDiff_iff_contDiffAt.2 fun x => contDiffAt_mul' hf.contDiffAt hg.contDiffAt

/- English proof (translation)
Conclude with `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) b).comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) a)).analyticAt M0`.
-/
private theorem hasDerivAt_exp_smul_apply_zero {ι : Type} [Fintype ι] (M0 : Matrix ι ι ℂ) (a b : ι) :
    AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M a b) M0 := by
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) b).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) a)).analyticAt M0

/- English proof (translation)
Establish `e : (fun M => (F M).det) = ∑ σ : Equiv.Perm ι, fun M => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ l, F M (σ l) l`. Use extensionality with `M`. Simplify using `[Matrix.det_apply, Finset.sum_apply, Units.smul_def, zsmul_eq_mul]`. Rewrite using `[e]`. Use `Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul ?_` and prove the remaining obligations.

Establish `h` using `Finset.analyticAt_prod (𝕜 := ℂ) Finset.univ (f := fun l M => F M (σ l) l) (c := M0) fun l _ => hF _ _`. Establish `e2 : (∏ l : ι, fun M : Matrix ι ι ℂ => F M (σ l) l) = fun M => ∏ l, F M (σ l) l`. Use extensionality with `M`. Simplify using `[Finset.prod_apply]`. Rewrite `h` using `[e2]`. Then use the resulting hypothesis.
-/
private theorem analyticAt_det_of_analyticAt_entries {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ)
    (F : Matrix ι ι ℂ → Matrix ι ι ℂ) (hF : ∀ a b, AnalyticAt ℂ (fun M => F M a b) M0) :
    AnalyticAt ℂ (fun M => (F M).det) M0 := by
  have e : (fun M => (F M).det) =
      ∑ σ : Equiv.Perm ι, fun M => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ l, F M (σ l) l := by
    ext M
    simp [Matrix.det_apply, Finset.sum_apply, Units.smul_def, zsmul_eq_mul]
  rw [e]
  refine Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul ?_
  have h := Finset.analyticAt_prod (𝕜 := ℂ) Finset.univ (f := fun l M => F M (σ l) l) (c := M0)
    fun l _ => hF _ _
  have e2 : (∏ l : ι, fun M : Matrix ι ι ℂ => F M (σ l) l) = fun M => ∏ l, F M (σ l) l := by
    ext M
    simp [Finset.prod_apply]
  rwa [e2] at h

/- English proof (translation)
Simplify using `only [Matrix.adjugate_apply]`. Use `analyticAt_det_of_analyticAt_entries M0 (fun M => M.updateRow j (Pi.single i 1)) fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Simplify using `only [Matrix.updateRow_self]`.

Conclude with `analyticAt_const`. Simplify using `only [Matrix.updateRow_ne h]`. Conclude with `hasDerivAt_exp_smul_apply_zero M0 a b`.
-/
theorem analyticAt_adj {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) (i j : ι) :
    AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M.adjugate i j) M0 := by
  simp only [Matrix.adjugate_apply]
  refine analyticAt_det_of_analyticAt_entries M0 (fun M => M.updateRow j (Pi.single i 1)) fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne h]
    exact hasDerivAt_exp_smul_apply_zero M0 a b

/- English proof (translation)
Establish `hd : AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M.det) M0` using `analyticAt_det_of_analyticAt_entries M0 (fun M => M) fun a b => hasDerivAt_exp_smul_apply_zero M0 a b`. Use `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_` and prove the remaining obligations. Establish `key : ContDiffAt ℝ k (fun M : Matrix ι ι ℂ => (M.det)⁻¹ * M.adjugate i j) M0` using `((hd.inv h).mul (analyticAt_adj M0 i j)).contDiffAt.restrict_scalars ℝ`. Use `key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun M => ?_)` and prove the remaining obligations. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv']`.
-/
theorem contDiffAt_inv {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) (h : M0.det ≠ 0)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun M : Matrix ι ι ℂ => M⁻¹) M0 := by
  have hd : AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M.det) M0 :=
    analyticAt_det_of_analyticAt_entries M0 (fun M => M) fun a b => hasDerivAt_exp_smul_apply_zero M0 a b
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have key : ContDiffAt ℝ k (fun M : Matrix ι ι ℂ => (M.det)⁻¹ * M.adjugate i j) M0 :=
    ((hd.inv h).mul (analyticAt_adj M0 i j)).contDiffAt.restrict_scalars ℝ
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun M => ?_)
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

/- English proof (translation)
Use `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Conclude with `contDiffAt_pi.1 (contDiffAt_pi.1 hA i) j`. Conclude with `contDiffAt_pi.1 (contDiffAt_pi.1 hB i) j`. Conclude with `contDiffAt_pi.1 (contDiffAt_pi.1 hC i) j`.

Conclude with `contDiffAt_pi.1 (contDiffAt_pi.1 hD i) j`.
-/
theorem contDiffAt_fromBlocks {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C D : E → Mn n} {x : E} {k : WithTop ℕ∞} (hA : ContDiffAt ℝ k A x) (hB : ContDiffAt ℝ k B x)
    (hC : ContDiffAt ℝ k C x) (hD : ContDiffAt ℝ k D x) :
    ContDiffAt ℝ k (fun y => (fromBlocks (A y) (B y) (C y) (D y) : M2 n)) x := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  rcases i with i | i <;> rcases j with j | j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hA i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hB i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hC i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hD i) j

def reP (V : Mn n) : Mn n := (1 / 2 : ℂ) • (V + Vᴴ)

def imaginary (V : Mn n) : Mn n := (-(Complex.I / 2)) • (V - Vᴴ)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[reP]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reP_herm (V : Mn n) : (reP V)ᴴ = reP V := by
  ext i j
  simp [reP]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[imaginary]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem imaginaryPart_isHermitian (V : Mn n) : (imaginary V)ᴴ = imaginary V := by
  ext i j
  simp [imaginary]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [reP, imaginary, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reP_add_imP (V : Mn n) : reP V + Complex.I • imaginary V = V := by
  ext i j
  simp only [reP, imaginary, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Simplify using `[imaginary, h]`.
-/
theorem imaginaryPart_of_isHermitian {V : Mn n} (h : Vᴴ = V) : imaginary V = 0 := by simp [imaginary, h]

/- English proof (translation)
Rewrite using `[reP, h, ← two_smul ℂ V, smul_smul]`. Evaluate the numerical expressions.
-/
theorem reP_of_herm {V : Mn n} (h : Vᴴ = V) : reP V = V := by
  rw [reP, h, ← two_smul ℂ V, smul_smul]
  norm_num

def fM (a0 : Mn n) (V : Mn n) : Mn n := reP V + Complex.I • (a0 * (1 + imaginary V) * (1 + imaginary V) * a0ᴴ)

end PositivityTheory.Rg.Sw.HSt.CRSec
