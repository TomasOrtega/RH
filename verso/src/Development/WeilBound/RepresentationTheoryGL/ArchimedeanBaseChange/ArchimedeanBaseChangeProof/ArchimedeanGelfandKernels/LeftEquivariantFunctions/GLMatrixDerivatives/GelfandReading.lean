import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructureStatement

noncomputable section

open Matrix Filter
open scoped ContDiff Topology ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.GelfandReading

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def coordsL (n : ℕ) : Mat n →L[ℝ] (Fin n × Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := coords
      map_add' := fun A B => by
        funext p
        simp [coords, Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun r A => by
        funext p
        simp [coords, Matrix.trace_smul] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coordsL_apply (A : Mat n) : coordsL n A = coords A := rfl

/- English proof (translation)
The claim follows from `isOpen_compl_singleton.preimage (continuous_id.matrix_det)`.
-/
theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_compl_singleton.preimage (continuous_id.matrix_det)

/- English proof (translation)
Establish `hb0 : b.det ≠ 0` using `hb'`. Establish `hd : IsUnit b.det` using `Ne.isUnit hb0`. Establish `hkk : (b⁻¹ * a) * (b⁻¹ * a)ᴴ = 1`. Establish `e1 : b⁻¹ * a * (b⁻¹ * a)ᴴ = b⁻¹ * (a * aᴴ) * b⁻¹ᴴ`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Establish `e2 : b⁻¹ * (b * bᴴ) * b⁻¹ᴴ = (b⁻¹ * b) * (b⁻¹ * b)ᴴ`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[e1, h, e2, Matrix.nonsing_inv_mul b hd, conjTranspose_one, Matrix.one_mul]`. Establish `hmem : b⁻¹ * a ∈ Matrix.unitaryGroup (Fin n) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`.

Conclude with `hkk`. Establish `key` using `hFk b hb' ⟨_, hmem⟩`. Simplify using `only at key`. Rewrite `key` using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv b hd, Matrix.one_mul]`. Conclude with `key`.
-/
theorem eq_of_mul_conj {Z : Type} {F : Mat n → Z}
    (hFk : ∀ x ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (x * k.1) = F x)
    {a b : Mat n} (hb' : b ∈ GLs n) (h : a * aᴴ = b * bᴴ) : F a = F b := by
  have hb0 : b.det ≠ 0 := hb'
  have hd : IsUnit b.det := Ne.isUnit hb0
  have hkk : (b⁻¹ * a) * (b⁻¹ * a)ᴴ = 1 := by
    have e1 : b⁻¹ * a * (b⁻¹ * a)ᴴ = b⁻¹ * (a * aᴴ) * b⁻¹ᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have e2 : b⁻¹ * (b * bᴴ) * b⁻¹ᴴ = (b⁻¹ * b) * (b⁻¹ * b)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e1, h, e2, Matrix.nonsing_inv_mul b hd, conjTranspose_one, Matrix.one_mul]
  have hmem : b⁻¹ * a ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hkk
  have key := hFk b hb' ⟨_, hmem⟩
  simp only at key
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv b hd, Matrix.one_mul] at key
  exact key

/- English proof (translation)
Simplify using `only [GLs, Set.mem_setOf_eq]`. Introduce `hdet`. Establish `hp : PosDef (hOf v)` using `hv`. Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit`. Rewrite `hu` using `[← hσ2 v hv, det_mul, hdet, zero_mul]`.

Conclude with `not_isUnit_zero hu`.
-/
theorem cone_mem_GLs {σ : (Fin n × Fin n → ℝ) → Mat n} (hσ2 : ∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) {v}
    (hv : v ∈ cone n) : σ v ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq]
  intro hdet
  have hp : PosDef (hOf v) := hv
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
  rw [← hσ2 v hv, det_mul, hdet, zero_mul] at hu
  exact not_isUnit_zero hu

/- English proof (translation)
Introduce `n Z _ _ σ F hσ hσ2 hF hFk v hv x hx hxv X hX`. Rewrite using `[show ((2 : ℂ) • (x * X * xᴴ)) = (2 : ℕ) • (x * X * xᴴ) by rw [two_smul, two_nsmul]]`. Take `⟨-, -, hcoords, hcoords', -, -, -, -⟩` from `hHb n`. Establish `hopen : IsOpen (cone n)` using `(GlobalTheory.T.positive_cone_structure n).1`. Establish `hexp : ∀ t : ℝ, (x + t • (x * X)) * (x + t • (x * X))ᴴ = x * xᴴ + t • ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • ((x * X) * (x * X)ᴴ)`.

Introduce `t`. Simplify using `only [conjTranspose_add, conjTranspose_smul, star_trivial, conjTranspose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Use `module`. Establish `hw : ∀ t : ℝ, coords ((x + t • (x * X)) * (x + t • (x * X))ᴴ) = v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)`. Introduce `t`.

Rewrite using `[hexp t, ← coordsL_apply, map_add, map_add, map_smul (coordsL n) t, map_smul (coordsL n) (t ^ 2), coordsL_apply, coordsL_apply, coordsL_apply, hxv, hcoords']`. Establish `hhOf : ∀ t : ℝ, hOf (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)) = (x + t • (x * X)) * (x + t • (x * X))ᴴ`. Introduce `t`. Rewrite using `[← hw t]`. Conclude with `hcoords _ (isHermitian_mul_conjTranspose_self _)`.

Establish `hwd : HasDerivAt (fun t : ℝ => v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)) (coords ((2 : ℕ) • (x * X * xᴴ))) 0`. Establish `h1` using `((hasDerivAt_id (0:ℝ)).smul_const (coords ((2 : ℕ) • (x * X * xᴴ)))).const_add v`. Establish `h2` using `(hasDerivAt_pow 2 (0:ℝ)).smul_const (coords ((x * X) * (x * X)ᴴ))`. Conclude with `(h1.add h2).congr_deriv (by simp)`. Establish `hγd : HasDerivAt (fun t : ℝ => x + t • (x * X)) (x * X) 0` using `(((hasDerivAt_id (0:ℝ)).smul_const (x * X)).const_add x).congr_deriv (by simp)`.

Establish `hFx : HasFDerivAt F (fderiv ℝ F x) x` using `((hF.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)).hasFDerivAt`. Establish `hmaps : Set.MapsTo σ (cone n) (GLs n)` using `fun w hw' => cone_mem_GLs hσ2 hw'`. Establish `hFσ : HasFDerivAt (fun w => F (σ w)) (fderiv ℝ (fun w => F (σ w)) v) v` using `(((hF.comp hσ hmaps).differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hv)).hasFDerivAt`. Establish `d1 : HasDerivAt (fun t : ℝ => F (x + t • (x * X))) (fderiv ℝ F x (x * X)) 0` using `hFx.comp_hasDerivAt_of_eq 0 hγd (by simp)`. Establish `d2 : HasDerivAt (fun t : ℝ => F (σ (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)))) (fderiv ℝ (fun w => F (σ w)) v (coords ((2 : ℕ) • (x * X * xᴴ)))) 0` using `hFσ.comp_hasDerivAt_of_eq 0 hwd (by simp)`.

Establish `hev : (fun t : ℝ => F (x + t • (x * X))) =ᶠ[nhds 0] (fun t : ℝ => F (σ (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ))))`. Establish `hin : ∀ᶠ t in nhds (0:ℝ), v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ) ∈ cone n` using `hwd.continuousAt.preimage_mem_nhds (by simpa using hopen.mem_nhds hv)`. Use `filter_upwards [hin] with t ht`. Conclude with `eq_of_mul_conj hFk (cone_mem_GLs hσ2 ht) (by rw [hσ2 _ ht, hhOf t])`. Conclude with `(d2.congr_of_eventuallyEq hev).unique d1`.
-/
theorem frameDer_of (hHb : HbFacts) : FrameDer := by
  intro n Z _ _ σ F hσ hσ2 hF hFk v hv x hx hxv X hX
  rw [show ((2 : ℂ) • (x * X * xᴴ)) = (2 : ℕ) • (x * X * xᴴ) by rw [two_smul, two_nsmul]]
  obtain ⟨-, -, hcoords, hcoords', -, -, -, -⟩ := hHb n
  have hopen : IsOpen (cone n) := (GlobalTheory.T.positive_cone_structure n).1
  have hexp : ∀ t : ℝ, (x + t • (x * X)) * (x + t • (x * X))ᴴ =
      x * xᴴ + t • ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • ((x * X) * (x * X)ᴴ) := by
    intro t
    simp only [conjTranspose_add, conjTranspose_smul, star_trivial, conjTranspose_mul, hX.eq,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    module
  have hw : ∀ t : ℝ, coords ((x + t • (x * X)) * (x + t • (x * X))ᴴ) =
      v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ) := by
    intro t
    rw [hexp t, ← coordsL_apply, map_add, map_add, map_smul (coordsL n) t, map_smul (coordsL n) (t ^ 2),
      coordsL_apply, coordsL_apply, coordsL_apply, hxv, hcoords']
  have hhOf : ∀ t : ℝ, hOf (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)) =
      (x + t • (x * X)) * (x + t • (x * X))ᴴ := by
    intro t
    rw [← hw t]
    exact hcoords _ (isHermitian_mul_conjTranspose_self _)
  have hwd : HasDerivAt (fun t : ℝ => v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ))
      (coords ((2 : ℕ) • (x * X * xᴴ))) 0 := by
    have h1 := ((hasDerivAt_id (0:ℝ)).smul_const (coords ((2 : ℕ) • (x * X * xᴴ)))).const_add v
    have h2 := (hasDerivAt_pow 2 (0:ℝ)).smul_const (coords ((x * X) * (x * X)ᴴ))
    exact (h1.add h2).congr_deriv (by simp)
  have hγd : HasDerivAt (fun t : ℝ => x + t • (x * X)) (x * X) 0 :=
    (((hasDerivAt_id (0:ℝ)).smul_const (x * X)).const_add x).congr_deriv (by simp)
  have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)).hasFDerivAt
  have hmaps : Set.MapsTo σ (cone n) (GLs n) := fun w hw' => cone_mem_GLs hσ2 hw'
  have hFσ : HasFDerivAt (fun w => F (σ w)) (fderiv ℝ (fun w => F (σ w)) v) v :=
    (((hF.comp hσ hmaps).differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hv)).hasFDerivAt
  have d1 : HasDerivAt (fun t : ℝ => F (x + t • (x * X))) (fderiv ℝ F x (x * X)) 0 :=
    hFx.comp_hasDerivAt_of_eq 0 hγd (by simp)
  have d2 : HasDerivAt (fun t : ℝ => F (σ (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ))))
      (fderiv ℝ (fun w => F (σ w)) v (coords ((2 : ℕ) • (x * X * xᴴ)))) 0 :=
    hFσ.comp_hasDerivAt_of_eq 0 hwd (by simp)
  have hev : (fun t : ℝ => F (x + t • (x * X))) =ᶠ[nhds 0]
      (fun t : ℝ => F (σ (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)))) := by
    have hin : ∀ᶠ t in nhds (0:ℝ),
        v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ) ∈ cone n :=
      hwd.continuousAt.preimage_mem_nhds (by simpa using hopen.mem_nhds hv)
    filter_upwards [hin] with t ht
    exact eq_of_mul_conj hFk (cone_mem_GLs hσ2 ht) (by rw [hσ2 _ ht, hhOf t])
  exact (d2.congr_of_eventuallyEq hev).unique d1

end PositivityTheory.RgBcC.LfSt.GelfandReading
