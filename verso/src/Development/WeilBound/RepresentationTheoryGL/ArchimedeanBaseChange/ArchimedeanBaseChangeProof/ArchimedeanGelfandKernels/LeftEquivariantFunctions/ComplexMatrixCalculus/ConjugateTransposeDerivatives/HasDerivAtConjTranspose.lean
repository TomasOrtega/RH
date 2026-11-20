import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.CfSandwich
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffAdjugateEntry

noncomputable section

open Matrix
open scoped ComplexConjugate ContDiff

namespace PositivityTheory.RgBcC.Cxa

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Unfold `matL`. Conclude with `(LinearMap.toMatrix_mul (fb n) f g).symm`.
-/
theorem matL_mul (f g : abelian₂ n →ₗ[ℂ] abelian₂ n) : matL n f * matL n g = matL n (f * g) := by
  unfold matL; exact (LinearMap.toMatrix_mul (fb n) f g).symm

/- English proof (translation)
Establish `h` using `CliffordAlgebra.ι_mul_ι_add_swap (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) v w`. Simplify using `only [QuadraticMap.polar, _root_.zero_apply, sub_zero, map_zero] at h`. Establish `h' : ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w = -(ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)` using `eq_neg_of_add_eq_zero_left h`. Simplify using `only [creL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[matL_mul, matL_mul, ← map_neg]`.

Use `congr 1`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * x) = -(ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ v * x))`. Rewrite using `[← mul_assoc, h', ← mul_assoc, neg_mul]`.
-/
theorem creL_anticomm (v w : Md n → ℂ) : creL n v * creL n w = -(creL n w * creL n v) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) v w
  simp only [QuadraticMap.polar, _root_.zero_apply, sub_zero, map_zero] at h
  have h' : ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w = -(ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v) :=
    eq_neg_of_add_eq_zero_left h
  simp only [creL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [matL_mul, matL_mul, ← map_neg]
  congr 1
  refine LinearMap.ext fun x => ?_
  change ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * x) = -(ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ v * x))
  rw [← mul_assoc, h', ← mul_assoc, neg_mul]

/- English proof (translation)
Establish `h : ∑ i, ∑ j, T i j • (A i * A j) = -(∑ i, ∑ j, T i j • (A i * A j))` using `by conv_lhs => rw [Finset.sum_comm]`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hT j i, hA j i, smul_neg]`. Establish `h2 : (2 : ℂ) • ∑ i, ∑ j, T i j • (A i * A j) = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 2 [h]`. Conclude with `add_neg_cancel _`.

Conclude with `(smul_eq_zero.1 h2).resolve_left two_ne_zero`.
-/
theorem sum_symm_anticomm {ι R : Type} [Fintype ι] [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    (T : ι → ι → ℂ) (hT : ∀ i j, T i j = T j i) (A : ι → R) (hA : ∀ i j, A i * A j = -(A j * A i)) :
    ∑ i, ∑ j, T i j • (A i * A j) = 0 := by
  have h : ∑ i, ∑ j, T i j • (A i * A j) = -(∑ i, ∑ j, T i j • (A i * A j)) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j i, hA j i, smul_neg]
  have h2 : (2 : ℂ) • ∑ i, ∑ j, T i j • (A i * A j) = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `hi` using `(hasDerivAt_pi.1 h) i`. Conclude with `(hasDerivAt_pi.1 hi) j`. Introduce `h`.

Conclude with `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j`.
-/
theorem hasDerivAt_entry {f : ℝ → Mat n} {f' : Mat n} {t : ℝ} :
    HasDerivAt f f' t ↔ ∀ i j, HasDerivAt (fun s => f s i j) (f' i j) t := by
  constructor
  · intro h i j
    have hi := (hasDerivAt_pi.1 h) i
    exact (hasDerivAt_pi.1 hi) j
  · intro h
    exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j

/- English proof (translation)
Rewrite `*` using `[hasDerivAt_entry]`. Introduce `i j`. Simplify using `only [Matrix.mul_apply, Matrix.add_apply]`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `HasDerivAt.fun_sum fun k _ => by`.

Use `(hf i k).mul (hg k j)` as an intermediate fact. Apply the tactic sequence `convert this using 1 <;> first | rfl | ring`.
-/
theorem hasDerivAt_matmul {f g : ℝ → Mat n} {f' g' : Mat n} {t : ℝ} (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s * g s) (f' * g t + f t * g') t := by
  rw [hasDerivAt_entry] at *
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => by
    have := (hf i k).mul (hg k j)
    convert this using 1 <;> first | rfl | ring

/- English proof (translation)
Rewrite `*` using `[hasDerivAt_entry]`. Introduce `i j`. Simplify `(hf j i).star` using `[Matrix.conjTranspose_apply]`.
-/
theorem hasDerivAt_conjTranspose {f : ℝ → Mat n} {f' : Mat n} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s)ᴴ) f'ᴴ t := by
  rw [hasDerivAt_entry] at *
  intro i j
  simpa [Matrix.conjTranspose_apply] using (hf j i).star

/- English proof (translation)
Rewrite `hf` using `[hasDerivAt_entry]`. Simplify using `only [Matrix.trace, Matrix.diag]`. Conclude with `HasDerivAt.fun_sum fun i _ => hf i i`.
-/
theorem hasDerivAt_trace {f : ℝ → Mat n} {f' : Mat n} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).trace) f'.trace t := by
  rw [hasDerivAt_entry] at hf
  simp only [Matrix.trace, Matrix.diag]
  exact HasDerivAt.fun_sum fun i _ => hf i i

/- English proof (translation)
Establish `h` using `((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt (x := z t)).comp_hasDerivAt t hz`. Apply the tactic sequence `convert h using 1 <;> first | rfl | (funext s; rfl) | simp`.
-/
theorem hasDerivAt_re_ofReal {z : ℝ → ℂ} {z' : ℂ} {t : ℝ} (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => (((z s).re : ℝ) : ℂ)) ((z'.re : ℝ) : ℂ) t := by
  have h := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt (x := z t)).comp_hasDerivAt t hz
  convert h using 1 <;> first | rfl | (funext s; rfl) | simp

/- English proof (translation)
The claim follows from `isOpen_ne_fun (continuous_id.matrix_det) continuous_const`.
-/
theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

/- English proof (translation)
Establish `h` using `((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)`. Rewrite `h` using `[one_smul]`. Conclude with `h`.
-/
theorem hasDerivAt_line (X : Mat n) : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
  rw [one_smul] at h
  exact h

/- English proof (translation)
Establish `h1 : (1 : Mat n) ∈ GLs n` using `by simp [GLs]`. Establish `hdiff : DifferentiableAt ℝ (fun y : Mat n => y⁻¹) 1` using `((GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth.contDiffOn_inv (n := n)).differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds h1)`. Establish `hm` using `hasDerivAt_line X`. Establish `hc : HasDerivAt (fun t : ℝ => ((1 : Mat n) + t • X)⁻¹) (fderiv ℝ (fun y : Mat n => y⁻¹) 1 X) 0`. Use `hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hm (by simp)` as an intermediate fact.

Conclude with `this`. Use `set c' := fderiv ℝ (fun y : Mat n => y⁻¹) 1 X`. Establish `hprod` using `hasDerivAt_matmul hm hc`. Simplify using `only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul] at hprod`. Establish `hev : (fun t : ℝ => ((1 : Mat n) + t • X) * ((1 : Mat n) + t • X)⁻¹) =ᶠ[nhds 0] fun _ => (1 : Mat n)`.

Establish `hcont : Continuous fun t : ℝ => ((1 : Mat n) + t • X).det` using `(continuous_const.add (continuous_id.smul continuous_const)).matrix_det`. Establish `h0 : ((1 : Mat n) + (0 : ℝ) • X).det ≠ 0` using `by simp`. Use `filter_upwards [hcont.continuousAt.eventually_ne h0] with t ht`. Conclude with `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ht)`. Establish `hconst : HasDerivAt (fun t : ℝ => ((1 : Mat n) + t • X) * ((1 : Mat n) + t • X)⁻¹) 0 0` using `(hasDerivAt_const (0 : ℝ) (1 : Mat n)).congr_of_eventuallyEq hev`.

Establish `e` using `hprod.unique hconst`. Establish `: c' = -X` using `by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact e`. Rewrite `hc` using `[this]`. Conclude with `hc`.
-/
theorem hasDerivAt_inv_line (X : Mat n) : HasDerivAt (fun t : ℝ => ((1 : Mat n) + t • X)⁻¹) (-X) 0 := by
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hdiff : DifferentiableAt ℝ (fun y : Mat n => y⁻¹) 1 :=
    ((GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth.contDiffOn_inv (n := n)).differentiableOn (by simp)).differentiableAt
      (isOpen_GLs.mem_nhds h1)
  have hm := hasDerivAt_line X
  have hc : HasDerivAt (fun t : ℝ => ((1 : Mat n) + t • X)⁻¹) (fderiv ℝ (fun y : Mat n => y⁻¹) 1 X) 0 := by
    have := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hm (by simp)
    exact this
  set c' := fderiv ℝ (fun y : Mat n => y⁻¹) 1 X
  have hprod := hasDerivAt_matmul hm hc
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul] at hprod
  have hev : (fun t : ℝ => ((1 : Mat n) + t • X) * ((1 : Mat n) + t • X)⁻¹) =ᶠ[nhds 0] fun _ => (1 : Mat n) := by
    have hcont : Continuous fun t : ℝ => ((1 : Mat n) + t • X).det :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    have h0 : ((1 : Mat n) + (0 : ℝ) • X).det ≠ 0 := by simp
    filter_upwards [hcont.continuousAt.eventually_ne h0] with t ht
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ht)
  have hconst : HasDerivAt (fun t : ℝ => ((1 : Mat n) + t • X) * ((1 : Mat n) + t • X)⁻¹) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : Mat n)).congr_of_eventuallyEq hev
  have e := hprod.unique hconst
  have : c' = -X := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact e
  rw [this] at hc
  exact hc

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `hi` using `(hasDerivAt_pi.1 h) i`. Conclude with `(hasDerivAt_pi.1 hi) j`. Introduce `h`.

Conclude with `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j`.
-/
theorem hasDerivAt_entry' {ι : Type} [Fintype ι] {f : ℝ → Matrix ι ι ℂ} {f' : Matrix ι ι ℂ} {t : ℝ} :
    HasDerivAt f f' t ↔ ∀ i j, HasDerivAt (fun s => f s i j) (f' i j) t := by
  constructor
  · intro h i j
    have hi := (hasDerivAt_pi.1 h) i
    exact (hasDerivAt_pi.1 hi) j
  · intro h
    exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j

/- English proof (translation)
Rewrite using `[hasDerivAt_entry']`. Introduce `r s`. Simplify using `only [Matrix.transpose_apply, Mt, cf_apply, Matrix.of_apply]`. Establish `hc` using `hasDerivAt_inv_line X`. Establish `hA` using `hasDerivAt_matmul hc (hasDerivAt_const (0 : ℝ) (hbM r))`.

Establish `hB` using `hasDerivAt_matmul hA (hasDerivAt_conjTranspose hc)`. Establish `hP` using `hasDerivAt_matmul hB (hasDerivAt_const (0 : ℝ) (hbM s))`. Establish `hR` using `hasDerivAt_re_ofReal (hasDerivAt_trace hP)`. Use `hR using 1` and compare the differences between its conclusion and the goal. Simplify using `only [zero_smul, add_zero, inv_one, Matrix.mul_zero, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_neg, hX.eq, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_add, Matrix.trace_neg, Complex.add_re, Complex.neg_re]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_Mt_curve (X : Mat n) (hX : X.IsHermitian) :
    HasDerivAt (fun t : ℝ => (Mt (((1 : Mat n) + t • X)⁻¹))ᵀ)
      (Matrix.of fun r s => -((((X * hbM r * hbM s + hbM r * X * hbM s).trace).re : ℝ) : ℂ)) 0 := by
  rw [hasDerivAt_entry']
  intro r s
  simp only [Matrix.transpose_apply, Mt, cf_apply, Matrix.of_apply]
  have hc := hasDerivAt_inv_line X
  have hA := hasDerivAt_matmul hc (hasDerivAt_const (0 : ℝ) (hbM r))
  have hB := hasDerivAt_matmul hA (hasDerivAt_conjTranspose hc)
  have hP := hasDerivAt_matmul hB (hasDerivAt_const (0 : ℝ) (hbM s))
  have hR := hasDerivAt_re_ofReal (hasDerivAt_trace hP)
  convert hR using 1
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_zero, Matrix.conjTranspose_one, Matrix.mul_one,
    Matrix.one_mul, Matrix.conjTranspose_neg, hX.eq, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_add,
    Matrix.trace_neg, Complex.add_re, Complex.neg_re]
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `m'`. Rewrite using `[cf_apply, (hbOrtho n).1, Pi.single_apply]`. Distinguish the cases in `h : m = m'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Simplify using the standard rewrite rules.
-/
theorem cf_hbM (m : Md n) : cf n (hbM m) = Pi.single m 1 := by
  funext m'
  rw [cf_apply, (hbOrtho n).1, Pi.single_apply]
  by_cases h : m = m'
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]; simp

end PositivityTheory.RgBcC.Cxa

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)
open Cxa

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n`. Take `⟨hC, hD⟩` from `hG n`. Distinguish the cases in `hd : DifferentiableAt ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1`. Establish `key : ∀ X : Mat n, X.IsHermitian → fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 X = ∑ r, ∑ s, (-((((X * hbM r * hbM s + hbM r * X * hbM s).trace).re : ℝ) : ℂ)) • (creL n (Pi.single r 1) * annL n (Pi.single s 1))`. Introduce `X hX`.

Establish `h1 : HasDerivAt (fun t : ℝ => gamM (Mt (((1 : Mat n) + t • X)⁻¹))ᵀ) (fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 X) 0` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line X) (by simp)`. Establish `hg1 : (Mt ((1 : Mat n))⁻¹)ᵀ = 1` using `by rw [inv_one, (mtLaws n).1, Matrix.transpose_one]`. Establish `hgam : HasFDerivAt (gamM (n` using `n)) (fderiv ℂ (gamM (n := n)) 1) 1 := (hC.differentiable (by simp) 1).hasFDerivAt`. Establish `h2` using `(hgam.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_Mt_curve X hX) (by simp only [zero_smul, add_zero]; exact hg1.symm)`. Rewrite using `[h1.unique h2]`.

Use `show (fderiv ℂ gamM 1) _ = _`. Rewrite using `[hD]`. Simplify using `only [Matrix.of_apply]`. Establish `hre : ∀ p : Fin n × Fin n, hb p = hbM (finProdFinEquiv p)` using `fun p => by simp [hbM]`. Establish `hsum : ∑ p : Fin n × Fin n, creL n (cf n (hb p)) * fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p) = ∑ m : Md n, creL n (Pi.single m 1) * fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hbM m)`.

Rewrite using `[← finProdFinEquiv.sum_comp]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[hre p, cf_hbM]`. Rewrite using `[hsum]`. Establish `hterm : ∀ m : Md n, creL n (Pi.single m 1) * fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hbM m) = ∑ r, ∑ s, (-((((hbM m * hbM r * hbM s + hbM r * hbM m * hbM s).trace).re : ℝ) : ℂ)) • (creL n (Pi.single m 1) * creL n (Pi.single r 1) * annL n (Pi.single s 1))`.

Introduce `m`. Rewrite using `[key _ ((hbOrtho n).2 m), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm]`. Use `congr 1`. Rewrite using `[mul_assoc]`. Simplify using `only [hterm]`. Use `conv_lhs => arg 2`.

Use extensionality with `m`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Establish `hz` using `sum_symm_anticomm (fun m r' => -((((hbM m * hbM r' * hbM s + hbM r' * hbM m * hbM s).trace).re : ℝ) : ℂ)) (fun i j => by rw [add_comm]) (fun m => creL n (Pi.single m 1)) (fun i j => creL_anticomm _ _)`.

Simplify using `only [← smul_mul_assoc] at hz`. Simplify using `only [← smul_mul_assoc, ← Finset.sum_mul]`. Rewrite using `[hz, zero_mul]`. Simplify using `[fderiv_zero_of_not_differentiableAt hd]`.
-/
theorem wedgeDer_of (hG : GamDer) : WedgeDer := by
  intro n
  obtain ⟨hC, hD⟩ := hG n
  by_cases hd : DifferentiableAt ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1
  · have key : ∀ X : Mat n, X.IsHermitian →
        fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 X = ∑ r, ∑ s,
          (-((((X * hbM r * hbM s + hbM r * X * hbM s).trace).re : ℝ) : ℂ)) •
            (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
      intro X hX
      have h1 : HasDerivAt (fun t : ℝ => gamM (Mt (((1 : Mat n) + t • X)⁻¹))ᵀ)
          (fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 X) 0 :=
        hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line X) (by simp)
      have hg1 : (Mt ((1 : Mat n))⁻¹)ᵀ = 1 := by rw [inv_one, (mtLaws n).1, Matrix.transpose_one]
      have hgam : HasFDerivAt (gamM (n := n)) (fderiv ℂ (gamM (n := n)) 1) 1 :=
        (hC.differentiable (by simp) 1).hasFDerivAt
      have h2 := (hgam.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_Mt_curve X hX)
        (by simp only [zero_smul, add_zero]; exact hg1.symm)
      rw [h1.unique h2]
      show (fderiv ℂ gamM 1) _ = _
      rw [hD]
      simp only [Matrix.of_apply]
    have hre : ∀ p : Fin n × Fin n, hb p = hbM (finProdFinEquiv p) := fun p => by simp [hbM]
    have hsum : ∑ p : Fin n × Fin n, creL n (cf n (hb p)) * fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p) =
        ∑ m : Md n, creL n (Pi.single m 1) * fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hbM m) := by
      rw [← finProdFinEquiv.sum_comp]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hre p, cf_hbM]
    rw [hsum]
    have hterm : ∀ m : Md n, creL n (Pi.single m 1) * fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hbM m) =
        ∑ r, ∑ s, (-((((hbM m * hbM r * hbM s + hbM r * hbM m * hbM s).trace).re : ℝ) : ℂ)) •
          (creL n (Pi.single m 1) * creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
      intro m
      rw [key _ ((hbOrtho n).2 m), Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_smul_comm]
      congr 1
      rw [mul_assoc]
    simp only [hterm]
    conv_lhs => arg 2; ext m; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hz := sum_symm_anticomm (fun m r' => -((((hbM m * hbM r' * hbM s + hbM r' * hbM m * hbM s).trace).re : ℝ) : ℂ))
      (fun i j => by rw [add_comm]) (fun m => creL n (Pi.single m 1)) (fun i j => creL_anticomm _ _)
    simp only [← smul_mul_assoc] at hz
    simp only [← smul_mul_assoc, ← Finset.sum_mul]
    rw [hz, zero_mul]
  · simp [fderiv_zero_of_not_differentiableAt hd]

end PositivityTheory.RgBcC
