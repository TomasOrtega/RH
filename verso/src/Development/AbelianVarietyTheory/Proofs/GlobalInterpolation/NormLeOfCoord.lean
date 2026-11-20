import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds

noncomputable section

namespace GlobalTheory.LvT.PtNorm

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
open Formalism.REAL (fockF)
open Formalism.L2.DIV (fockL fockS)
open scoped ComplexOrder Matrix

/- English proof (translation)
The claim follows from `hA.hadamard hB`.
-/
theorem psd_had {κ : Type} {A B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.of fun i j => A i j * B i j).PosSemidef := hA.hadamard hB

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `Matrix.posSemidef_vecMulVec_self_star (fun _ : κ => (1 : ℂ))`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec]`. Simplify using `using Matrix.PosSemidef.zero`. Consider the case `insert τ s hτ ih`. Take `⟨h1, h2⟩` from `ih`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `psd_had (hB τ) h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[Finset.prod_insert hτ]`. Establish `h3` using `(psd_had (hAB τ) (h2.add h1)).add (psd_had (hB τ) h2)`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[Finset.prod_insert hτ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psd_prod {ι κ : Type} [Fintype κ] (A B : ι → Matrix κ κ ℂ) (hB : ∀ τ, (B τ).PosSemidef)
    (hAB : ∀ τ, (A τ - B τ).PosSemidef) (s : Finset ι) :
    (Matrix.of fun i j => ∏ τ ∈ s, B τ i j).PosSemidef ∧
      ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - (Matrix.of fun i j => ∏ τ ∈ s, B τ i j)).PosSemidef := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : κ => (1 : ℂ))
      convert h using 1
      ext i j
      simp [Matrix.vecMulVec]
    · simpa using Matrix.PosSemidef.zero
  | insert τ s hτ ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · convert psd_had (hB τ) h1 using 1
      ext i j
      simp [Finset.prod_insert hτ]
    · have h3 := (psd_had (hAB τ) (h2.add h1)).add (psd_had (hB τ) h2)
      convert h3 using 1
      ext i j
      simp [Finset.prod_insert hτ]
      ring

/- English proof (translation)
Establish `h` using `Formalism.L2.Col.map_fockS (RingHom.id ℂ) g f (fun _ => rfl)`. Simplify using `only [RingHom.id_apply, MvPolynomial.map_id] at h`. Rewrite using `[Formalism.L2.DIV.fockL_apply, h]`.
-/
theorem fockF_eq {σ : Type} (f g : MvPolynomial σ ℂ) : fockF f g = fockL g f := by
  have h := Formalism.L2.Col.map_fockS (RingHom.id ℂ) g f (fun _ => rfl)
  simp only [RingHom.id_apply, MvPolynomial.map_id] at h
  rw [Formalism.L2.DIV.fockL_apply, h]

/- English proof (translation)
Distinguish the cases in `hf : f = 0`. Simplify using `[hf]`. Rewrite using `[← fockF_eq]`. Conclude with `(Formalism.L2.DIV.ps_fockF_pos f hf).le`.
-/
theorem fockL_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ fockL f f := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [← fockF_eq]; exact (Formalism.L2.DIV.ps_fockF_pos f hf).le

def gram {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : Matrix κ κ ℂ := Matrix.of fun i j => fockL (v i) (v j)

/- English proof (translation)
Simplify using `only [gram, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_dot {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ (gram v) *ᵥ x = fockL (∑ i, x i • v i) (∑ i, x i • v i) := by
  simp only [gram, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]`. Conclude with `(Formalism.L2.DIV.fockL_symm _ _).symm`.
-/
theorem gram_herm {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : (gram v).IsHermitian := by
  ext i j
  simp only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact (Formalism.L2.DIV.fockL_symm _ _).symm

/- English proof (translation)
The claim follows from `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gram_herm v) fun x => by rw [gram_dot]; exact fockL_nonneg _`.
-/
theorem gram_psd {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) : (gram v).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gram_herm v) fun x => by rw [gram_dot]; exact fockL_nonneg _

/- English proof (translation)
Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_` and prove the remaining obligations. Use `Matrix.IsHermitian.sub ?_ (gram_herm _)` and prove the remaining obligations. Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_smul, (gram_herm v).eq]`. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, gram_dot, gram_dot]`. Establish `e : ∑ i, x i • F (v i) = F (∑ i, x i • v i)` using `by simp`. Rewrite using `[e]`. Establish `hm : ∑ i, x i • v i ∈ V` using `V.sum_mem fun i _ => V.smul_mem _ (hv i)`. Establish `h1` using `h _ hm`.

Establish `h2` using `(Complex.le_def.mp (fockL_nonneg (∑ i, x i • v i))).2`. Establish `h3` using `(Complex.le_def.mp (fockL_nonneg (F (∑ i, x i • v i)))).2`. Use `Complex.le_def.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [smul_eq_mul, Complex.zero_im, Complex.sub_im, Complex.im_ofReal_mul, ← h2, ← h3]`. Simplify using the standard rewrite rules.
-/
theorem gram_sub_psd {σ σ' κ : Type} [Fintype κ] (V : Submodule ℂ (MvPolynomial σ ℂ))
    (F : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ' ℂ) (C : ℝ)
    (h : ∀ f ∈ V, (fockL (F f) (F f)).re ≤ C * (fockL f f).re) (v : κ → MvPolynomial σ ℂ) (hv : ∀ i, v i ∈ V) :
    ((C : ℂ) • gram v - gram fun i => F (v i)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.sub ?_ (gram_herm _)
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (gram_herm v).eq]
    simp
  · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, gram_dot, gram_dot]
    have e : ∑ i, x i • F (v i) = F (∑ i, x i • v i) := by simp
    rw [e]
    have hm : ∑ i, x i • v i ∈ V := V.sum_mem fun i _ => V.smul_mem _ (hv i)
    have h1 := h _ hm
    have h2 := (Complex.le_def.mp (fockL_nonneg (∑ i, x i • v i))).2
    have h3 := (Complex.le_def.mp (fockL_nonneg (F (∑ i, x i • v i)))).2
    refine Complex.le_def.mpr ⟨?_, ?_⟩
    · simp only [smul_eq_mul, Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul]; linarith
    · simp only [smul_eq_mul, Complex.zero_im, Complex.sub_im, Complex.im_ofReal_mul, ← h2, ← h3]; simp

def eN {n : ℕ} (l : DomWeight n) : ℝ := (fockF (extremal ℂ n l) (extremal ℂ n l)).re

/- English proof (translation)
The claim follows from `(Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).1`.
-/
theorem eN_pos {n : ℕ} (l : DomWeight n) : 0 < eN l :=
  (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).1

/- English proof (translation)
Establish `h` using `(Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).2`. Conclude with `Complex.ext (by simp [eN]) (by simpa using h.symm)`.
-/
theorem eN_eq {n : ℕ} (l : DomWeight n) : fockF (extremal ℂ n l) (extremal ℂ n l) = (eN l : ℂ) := by
  have h := (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).2
  exact Complex.ext (by simp [eN]) (by simpa using h.symm)

def sqL {n : ℕ} (l : DomWeight n) (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  detPow ℂ n g l.detShift • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose).toLinearMap

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}
  (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))

def brT (X : Ch D u) (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)) (τ : D.what₂.Tau) : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ :=
  ((sqrtT X ^ (-X.fm.deg τ) : ℂˣ) : ℂ) • br τ

end GlobalTheory.LvT.PtNorm
