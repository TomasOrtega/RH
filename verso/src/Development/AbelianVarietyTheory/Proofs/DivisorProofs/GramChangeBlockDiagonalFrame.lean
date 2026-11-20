import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.HermFrame

/- English proof (translation)
Simplify using `only [chTwo, wedge, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]`.
-/
theorem chTwo_eq_trace_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {n : Type*} [Fintype n] [DecidableEq n] (H : E → Matrix n n ℂ)
    (z ξ₁ η₁ ξ₂ η₂ : E) : chTwo H z ξ₁ η₁ ξ₂ η₂ = kappa ^ 2 / 2 *
      ((curv H z ξ₁ η₁ * curv H z ξ₂ η₂).trace + (curv H z ξ₂ η₂ * curv H z ξ₁ η₁).trace
        - (curv H z ξ₁ η₂ * curv H z ξ₂ η₁).trace - (curv H z ξ₂ η₁ * curv H z ξ₁ η₂).trace) := by
  simp only [chTwo, wedge, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

/- English proof (translation)
The claim follows from `e.sum_comp fun a => M a a`.
-/
theorem trace_submatrix_of_equiv {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n)
    (M : Matrix n n ℂ) : (M.submatrix e e).trace = M.trace :=
  e.sum_comp fun a => M a a

/- English proof (translation)
Introduce `D ι _ _ m n _ _ U K T G hU hK hT hb hG z hz`. Establish `hcard : Fintype.card n = Fintype.card (Σ τ : ι, Fin (m τ))`. Use `(LinearEquiv.ofBijective (T z).mulVecLin (hb z hz)).finrank_eq` as an intermediate fact. Simplify `this` using `only [Module.finrank_fintype_fun_eq_card]`. Set `e : n ≃ Σ τ : ι, Fin (m τ)` to `Fintype.equivOfCardEq hcard`.

Set `A : V D → Matrix (Σ τ : ι, Fin (m τ)) (Σ τ : ι, Fin (m τ)) ℂ` to `fun u => (T u).submatrix id e.symm`. Set `B : V D → Matrix (Σ τ : ι, Fin (m τ)) (Σ τ : ι, Fin (m τ)) ℂ` to `fun u => Matrix.blockDiagonal' fun τ => dualGram (K τ u)`. Establish `hn` using `hU.mem_nhds hz`. Establish `hB : IsHermFrame U B` using `isHermFrame_blockDiagonal' hU fun τ => (hK τ).isHermFrame.dual`. Establish `hA : MContDiffAt 2 A z` using `fun a b => ((GlobalTheory.ChartGlue.contDiffOn_real hU (hT a (e.symm b))).contDiffAt hn).of_le (by norm_cast)`.

Establish `hAu : IsUnit (A z).det`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]`. Introduce `w`. Take `⟨v, hv⟩` from `(hb z hz).2 w`. Use `⟨v ∘ e.symm, ?_⟩` and prove the remaining obligations.

Simplify using `only [A]`. Rewrite using `[Matrix.submatrix_mulVec_equiv, ← hv]`. Establish `hv' : (v ∘ e.symm) ∘ e.symm.symm = v` using `by funext a; simp`. Rewrite using `[hv']`. Both sides reduce to the same expression.

Establish `hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0` using `by filter_upwards [hn] with x hx η`. Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `dbar (fun u => T u a (e.symm b)) x η = 0`. Rewrite using `[GlobalTheory.dbar_eq_zero ((hT a (e.symm b)).differentiableAt (hU.mem_nhds hx))]`. Both sides reduce to the same expression.

Establish `hGe : G =ᶠ[𝓝 z] fun u => ((A u)ᵀ * B u * (A u)ᴴᵀ).submatrix e e` using `by filter_upwards [hn] with x hx`. Rewrite using `[hG x hx]`. Use extensionality with `a b`. Simplify using `[chg, A, B, Matrix.mul_apply]`. Establish `hc : ∀ ξ η, curv G z ξ η = ((A z)⁻¹ * (Matrix.blockDiagonal' fun τ => -(curv (K τ) z ξ η)ᵀ) * A z).submatrix e e` using `fun ξ η => by`.

Rewrite using `[curv_congr hGe, curv_submatrix_equiv (fun u => (A u)ᵀ * B u * (A u)ᴴᵀ) e, curv_changeFrame (hB.two hz) (hB.isUnit z hz) hA hAu hA0, curv_blockDiagonal' (H := fun τ u => dualGram (K τ u)) (fun τ => (hK τ).isHermFrame.dual.two hz) (fun τ => (hK τ).isHermFrame.dual.isUnit z hz)]`. Simplify using `only [fun τ => curv_dual ((hK τ).isHermFrame.two hz) ((hK τ).isHermFrame.isUnit z hz) ξ η]`. Establish `ht : ∀ M : Matrix (Σ τ : ι, Fin (m τ)) (Σ τ : ι, Fin (m τ)) ℂ, ((A z)⁻¹ * M * A z).trace = M.trace` using `fun M => by`. Rewrite using `[Matrix.trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left _ _ hAu]`. Establish `hm : ∀ ξ η ξ' η', (curv G z ξ η * curv G z ξ' η').trace = ∑ τ, (curv (K τ) z ξ' η' * curv (K τ) z ξ η).trace` using `fun ξ η ξ' η' => by`.

Rewrite using `[hc, hc, Matrix.submatrix_mul_equiv, trace_submatrix_of_equiv, Matrix.mul_assoc _ (A z), Matrix.mul_assoc (A z)⁻¹ _ (A z), Matrix.mul_nonsing_inv_cancel_left _ _ hAu, ← Matrix.mul_assoc, Matrix.mul_assoc (A z)⁻¹, ht, ← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← Matrix.transpose_mul, Matrix.trace_transpose]`. Use `⟨?_, fun ξ η => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ξ₁ η₁ ξ₂ η₂`.

Simplify using `only [chTwo_eq_trace_mul, hm, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, trace_submatrix_of_equiv, ht, Matrix.trace_blockDiagonal', ← Finset.sum_neg_distrib]`. Simplify using `only [Matrix.trace_neg, Matrix.trace_transpose]`.
-/
theorem chTwo_chg_blockDiagonal'_dualGram : ∀ (D : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Set (V D)) (K : ∀ τ : ι, V D → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (T : V D → Matrix (Σ τ : ι, Fin (m τ)) n ℂ) (G : V D → Matrix n n ℂ), IsOpen U → (∀ τ, IsPosFrame U (K τ)) → (∀ j b, DifferentiableOn ℂ (fun u => T u j b) U) → (∀ u ∈ U, Function.Bijective (T u).mulVec) → (∀ u ∈ U, G u = chg (T u) (Matrix.blockDiagonal' fun τ => dualGram (K τ u))) → ∀ z ∈ U, chTwo G z = (fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (K τ) z ξ₁ η₁ ξ₂ η₂) ∧ ∀ ξ η, (curv G z ξ η).trace = -∑ τ, (curv (K τ) z ξ η).trace := by
  intro D ι _ _ m n _ _ U K T G hU hK hT hb hG z hz
  have hcard : Fintype.card n = Fintype.card (Σ τ : ι, Fin (m τ)) := by
    have := (LinearEquiv.ofBijective (T z).mulVecLin (hb z hz)).finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card] using this
  let e : n ≃ Σ τ : ι, Fin (m τ) := Fintype.equivOfCardEq hcard
  let A : V D → Matrix (Σ τ : ι, Fin (m τ)) (Σ τ : ι, Fin (m τ)) ℂ :=
    fun u => (T u).submatrix id e.symm
  let B : V D → Matrix (Σ τ : ι, Fin (m τ)) (Σ τ : ι, Fin (m τ)) ℂ :=
    fun u => Matrix.blockDiagonal' fun τ => dualGram (K τ u)
  have hn := hU.mem_nhds hz
  have hB : IsHermFrame U B := isHermFrame_blockDiagonal' hU fun τ => (hK τ).isHermFrame.dual
  have hA : MContDiffAt 2 A z := fun a b =>
    ((GlobalTheory.ChartGlue.contDiffOn_real hU (hT a (e.symm b))).contDiffAt hn).of_le (by norm_cast)
  have hAu : IsUnit (A z).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    obtain ⟨v, hv⟩ := (hb z hz).2 w
    refine ⟨v ∘ e.symm, ?_⟩
    simp only [A]
    rw [Matrix.submatrix_mulVec_equiv, ← hv]
    have hv' : (v ∘ e.symm) ∘ e.symm.symm = v := by funext a; simp
    rw [hv']
    rfl
  have hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0 := by
    filter_upwards [hn] with x hx η
    ext a b
    change dbar (fun u => T u a (e.symm b)) x η = 0
    rw [GlobalTheory.dbar_eq_zero ((hT a (e.symm b)).differentiableAt (hU.mem_nhds hx))]
    rfl
  have hGe : G =ᶠ[𝓝 z] fun u => ((A u)ᵀ * B u * (A u)ᴴᵀ).submatrix e e := by
    filter_upwards [hn] with x hx
    rw [hG x hx]
    ext a b
    simp [chg, A, B, Matrix.mul_apply]
  have hc : ∀ ξ η, curv G z ξ η = ((A z)⁻¹ *
      (Matrix.blockDiagonal' fun τ => -(curv (K τ) z ξ η)ᵀ) * A z).submatrix e e := fun ξ η => by
    rw [curv_congr hGe, curv_submatrix_equiv (fun u => (A u)ᵀ * B u * (A u)ᴴᵀ) e,
      curv_changeFrame (hB.two hz) (hB.isUnit z hz) hA hAu hA0,
      curv_blockDiagonal' (H := fun τ u => dualGram (K τ u))
        (fun τ => (hK τ).isHermFrame.dual.two hz) (fun τ => (hK τ).isHermFrame.dual.isUnit z hz)]
    simp only [fun τ => curv_dual ((hK τ).isHermFrame.two hz) ((hK τ).isHermFrame.isUnit z hz) ξ η]
  have ht : ∀ M : Matrix (Σ τ : ι, Fin (m τ)) (Σ τ : ι, Fin (m τ)) ℂ,
      ((A z)⁻¹ * M * A z).trace = M.trace := fun M => by
    rw [Matrix.trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left _ _ hAu]
  have hm : ∀ ξ η ξ' η', (curv G z ξ η * curv G z ξ' η').trace =
      ∑ τ, (curv (K τ) z ξ' η' * curv (K τ) z ξ η).trace := fun ξ η ξ' η' => by
    rw [hc, hc, Matrix.submatrix_mul_equiv, trace_submatrix_of_equiv, Matrix.mul_assoc _ (A z),
      Matrix.mul_assoc (A z)⁻¹ _ (A z), Matrix.mul_nonsing_inv_cancel_left _ _ hAu,
      ← Matrix.mul_assoc, Matrix.mul_assoc (A z)⁻¹, ht, ← Matrix.blockDiagonal'_mul,
      Matrix.trace_blockDiagonal']
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← Matrix.transpose_mul, Matrix.trace_transpose]
  refine ⟨?_, fun ξ η => ?_⟩
  · funext ξ₁ η₁ ξ₂ η₂
    simp only [chTwo_eq_trace_mul, hm, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  · rw [hc, trace_submatrix_of_equiv, ht, Matrix.trace_blockDiagonal', ← Finset.sum_neg_distrib]
    simp only [Matrix.trace_neg, Matrix.trace_transpose]

end GlobalTheory.HermFrame
