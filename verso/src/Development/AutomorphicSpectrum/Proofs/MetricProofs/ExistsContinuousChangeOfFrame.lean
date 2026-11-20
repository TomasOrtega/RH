import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.SolveCoeff

private def colMat {g m : ℕ} (v : Fin m → Fin g → ℂ) : Matrix (Fin g) (Fin m) ℂ :=
  Matrix.of fun a i => v i a

/- English proof (translation)
Use extensionality with `a i`. Simplify using `only [colMat, Matrix.of_apply, Matrix.mul_apply]`. Rewrite using `[h i]`. Simplify using `[Finset.sum_apply, mul_comm]`.
-/
private lemma colMat_eq_mul {g m : ℕ} (M f : Fin m → Fin g → ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i, f i = ∑ j, C j i • M j) : colMat f = colMat M * C := by
  ext a i
  simp only [colMat, Matrix.of_apply, Matrix.mul_apply]
  rw [h i]
  simp [Finset.sum_apply, mul_comm]

/- English proof (translation)
Establish `hu : IsUnit (Aᴴ * A).det` using `isUnit_iff_ne_zero.mpr hd`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`.
-/
private lemma solve_eq {g m : ℕ} (A : Matrix (Fin g) (Fin m) ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (hd : (Aᴴ * A).det ≠ 0) : (Aᴴ * A)⁻¹ * Aᴴ * (A * C) = C := by
  have hu : IsUnit (Aᴴ * A).det := isUnit_iff_ne_zero.mpr hd
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

open scoped ComplexOrder in
/- English proof (translation)
Establish `hinj : Function.Injective (colMat M).mulVec`. Introduce `x y hxy`. Establish `hz : ∑ i, (x - y) i • M i = 0`. Use function extensionality and compare the values at `a`. Establish `h1 : (colMat M *ᵥ (x - y)) a = 0`.

Rewrite using `[Matrix.mulVec_sub, hxy, sub_self]`. Both sides reduce to the same expression. Simplify `h1` using `[Matrix.mulVec, dotProduct, colMat, mul_comm, Finset.sum_apply]`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h _ hz i)`.

Establish `hinj2 : Function.Injective ((colMat M)ᴴ * colMat M).mulVec`. Introduce `x y hxy`. Apply `hinj` to reduce the goal to its premises. Establish `h0 : ((colMat M)ᴴ * colMat M) *ᵥ (x - y) = 0`. Rewrite using `[Matrix.mulVec_sub, hxy, sub_self]`.

Establish `h1` using `(Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).1 h0`. Rewrite `h1` using `[Matrix.mulVec_sub]`. Conclude with `sub_eq_zero.1 h1`. Use `(Matrix.mulVec_injective_iff_isUnit).1 hinj2` as an intermediate fact. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero`.
-/
private lemma gram_det_ne {g m : ℕ} (M : Fin m → Fin g → ℂ) (h : LinearIndependent ℂ M) :
    ((colMat M)ᴴ * colMat M).det ≠ 0 := by
  have hinj : Function.Injective (colMat M).mulVec := by
    intro x y hxy
    have hz : ∑ i, (x - y) i • M i = 0 := by
      funext a
      have h1 : (colMat M *ᵥ (x - y)) a = 0 := by
        rw [Matrix.mulVec_sub, hxy, sub_self]; rfl
      simpa [Matrix.mulVec, dotProduct, colMat, mul_comm, Finset.sum_apply] using h1
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h _ hz i)
  have hinj2 : Function.Injective ((colMat M)ᴴ * colMat M).mulVec := by
    intro x y hxy
    apply hinj
    have h0 : ((colMat M)ᴴ * colMat M) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).1 h0
    rw [Matrix.mulVec_sub] at h1
    exact sub_eq_zero.1 h1
  have := (Matrix.mulVec_injective_iff_isUnit).1 hinj2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

/- English proof (translation)
Establish `c : Continuous (fun p : Matrix (Fin l) (Fin k) ℂ × Matrix (Fin k) (Fin r) ℂ => p.1 * p.2)` using `continuous_fst.matrix_mul continuous_snd`. Conclude with `c.continuousAt.comp (hA.prodMk hB)`.
-/
private lemma cat_mul {X : Type} [TopologicalSpace X] {x : X} {l k r : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} {B : X → Matrix (Fin k) (Fin r) ℂ}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) : ContinuousAt (fun z => A z * B z) x := by
  have c : Continuous (fun p : Matrix (Fin l) (Fin k) ℂ × Matrix (Fin k) (Fin r) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact c.continuousAt.comp (hA.prodMk hB)

/- English proof (translation)
Establish `c : Continuous (fun N : Matrix (Fin l) (Fin k) ℂ => Nᴴ)` using `continuous_id.matrix_conjTranspose`. Conclude with `c.continuousAt.comp hA`.
-/
private lemma cat_conj {X : Type} [TopologicalSpace X] {x : X} {l k : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z)ᴴ) x := by
  have c : Continuous (fun N : Matrix (Fin l) (Fin k) ℂ => Nᴴ) :=
    continuous_id.matrix_conjTranspose
  exact c.continuousAt.comp hA

/- English proof (translation)
Establish `c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.det)` using `continuous_id.matrix_det`. Conclude with `c.continuousAt.comp hA`.
-/
private lemma cat_det {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).det) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.det) := continuous_id.matrix_det
  exact c.continuousAt.comp hA

/- English proof (translation)
Establish `c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.adjugate)` using `continuous_id.matrix_adjugate`. Conclude with `c.continuousAt.comp hA`.
-/
private lemma cat_adj {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).adjugate) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.adjugate) :=
    continuous_id.matrix_adjugate
  exact c.continuousAt.comp hA

/- English proof (translation)
Use `continuousAt_pi.2 fun a => continuousAt_pi.2 fun i => ?_` and prove the remaining obligations. Conclude with `(continuous_apply a).continuousAt.comp (h i)`.
-/
private lemma colMat_continuousAt {n g m : ℕ} (M : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (h : ∀ i, ContinuousAt (fun z => M z i) 0) : ContinuousAt (fun z => colMat (M z)) 0 := by
  refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun i => ?_
  exact (continuous_apply a).continuousAt.comp (h i)

/- English proof (translation)
Establish `hA : ContinuousAt (fun z => colMat (M z)) 0` using `colMat_continuousAt M hM`. Establish `hF : ContinuousAt (fun z => colMat (f z)) 0` using `colMat_continuousAt f hf`. Establish `hG : ContinuousAt (fun z => (colMat (M z))ᴴ * colMat (M z)) 0` using `cat_mul (cat_conj hA) hA`. Establish `hdet : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z)).det) 0` using `cat_det hG`. Establish `hd0` using `gram_det_ne (M 0) hli`.

Establish `hinv : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹) 0`. Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv']`. Conclude with `(hdet.inv₀ hd0).smul (cat_adj hG)`. Use `⟨fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z), cat_mul (cat_mul hinv (cat_conj hA)) hF, ?_, ?_⟩` and prove the remaining obligations. Use `show ((colMat (M 0))ᴴ * colMat (M 0))⁻¹ * (colMat (M 0))ᴴ * colMat (f 0) = T₀`.

Rewrite using `[colMat_eq_mul (M 0) (f 0) T₀ h0]`. Conclude with `solve_eq _ _ hd0`. Use `filter_upwards [hspan, hdet.eventually_ne hd0] with z hz hdz i`. Establish `hc : ∀ i, ∃ c : Fin m → ℂ, ∑ j, c j • M z j = f z i` using `fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hz i)`. Use `choose c hc using hc`.

Establish `hcol : colMat (f z) = colMat (M z) * Matrix.of (fun j i => c i j)` using `colMat_eq_mul (M z) (f z) _ (fun i => by simpa using (hc i).symm)`. Establish `hT : ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z) = Matrix.of (fun j i => c i j)`. Rewrite using `[hcol]`. Conclude with `solve_eq _ _ hdz`. Simplify using `only [hT, Matrix.of_apply]`.

Conclude with `(hc i).symm`.
-/
theorem coeff_continuous (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (T₀ : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i, ContinuousAt (fun z => M z i) 0)
    (hf : ∀ i, ContinuousAt (fun z => f z i) 0) (hli : LinearIndependent ℂ (M 0))
    (h0 : ∀ i, f 0 i = ∑ j, T₀ j i • M 0 j)
    (hspan : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) :
    ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧
      ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  have hA : ContinuousAt (fun z => colMat (M z)) 0 := colMat_continuousAt M hM
  have hF : ContinuousAt (fun z => colMat (f z)) 0 := colMat_continuousAt f hf
  have hG : ContinuousAt (fun z => (colMat (M z))ᴴ * colMat (M z)) 0 :=
    cat_mul (cat_conj hA) hA
  have hdet : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z)).det) 0 := cat_det hG
  have hd0 := gram_det_ne (M 0) hli
  have hinv : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹) 0 := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hdet.inv₀ hd0).smul (cat_adj hG)
  refine ⟨fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z),
    cat_mul (cat_mul hinv (cat_conj hA)) hF, ?_, ?_⟩
  · show ((colMat (M 0))ᴴ * colMat (M 0))⁻¹ * (colMat (M 0))ᴴ * colMat (f 0) = T₀
    rw [colMat_eq_mul (M 0) (f 0) T₀ h0]
    exact solve_eq _ _ hd0
  · filter_upwards [hspan, hdet.eventually_ne hd0] with z hz hdz i
    have hc : ∀ i, ∃ c : Fin m → ℂ, ∑ j, c j • M z j = f z i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hz i)
    choose c hc using hc
    have hcol : colMat (f z) = colMat (M z) * Matrix.of (fun j i => c i j) :=
      colMat_eq_mul (M z) (f z) _ (fun i => by simpa using (hc i).symm)
    have hT : ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z)
        = Matrix.of (fun j i => c i j) := by
      rw [hcol]; exact solve_eq _ _ hdz
    simp only [hT, Matrix.of_apply]
    exact (hc i).symm

end GlobalTheory.CompanionTheory.Ar.SolveCoeff
