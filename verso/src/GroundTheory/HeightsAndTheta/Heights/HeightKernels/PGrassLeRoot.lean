import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianRootBound

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def cone {R : Type*} [CommRing R] (y : (Σ k, ι k) → R) : MRing ι →ₐ[ℤ] MvPolynomial K R :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [cone]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]`. Simplify using `[cone]`.
-/
theorem map_cone {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (y : (Σ k, ι k) → R)
    (g : MRing ι) : MvPolynomial.map φ (cone y g) = cone (fun p => φ (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [cone]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [cone]

/- English proof (translation)
Set `φ : MvPolynomial (Fin f × Fin j × Fin m) ℚ →+* ℂ` to `(aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom`. Use `show φ _ = _`. Rewrite using `[grassPolyCoord, RingHom.map_det, rootCoord]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, colsOf, onePipe, submatrix_apply, of_apply, id]`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) (p.2.1.orderEmbOfFin p.2.2 b)` and prove the remaining obligations. Simplify using `[Fin.append_left, Matrix.one_apply, apply_ite φ]`. Simplify using `[Fin.append_right, φ]`.
-/
theorem eval_grassPolyCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval (fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2) (grassPolyCoord f j m p) =
      rootCoord ζ p := by
  let φ : MvPolynomial (Fin f × Fin j × Fin m) ℚ →+* ℂ :=
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom
  show φ _ = _
  rw [grassPolyCoord, RingHom.map_det, rootCoord]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, colsOf, onePipe, submatrix_apply, of_apply, id]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) (p.2.1.orderEmbOfFin p.2.2 b)
  · simp [Fin.append_left, Matrix.one_apply, apply_ite φ]
  · simp [Fin.append_right, φ]

end GrassmannianRootBound

open GrassmannianRootBound in

/- English proof (translation)
Introduce `f j m ζ g hg`. Establish `h0 : mConeMap (grassCoord f j m) g = 0` using `hg`. Establish `h1 : cone (grassPolyCoord f j m) g = 0`. Apply `MvPolynomial.map_injective (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)) (IsFractionRing.injective _ _)` to reduce the goal to its premises. Rewrite using `[map_cone, map_zero]`.

Conclude with `h0`. Establish `h2` using `congrArg (MvPolynomial.map (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom) h1`. Rewrite `h2` using `[map_cone, map_zero]`. Use `show (aeval fun p => MvPolynomial.C (rootCoord ζ p) * MvPolynomial.X p.1) g = 0`. Simplify `h2` using `[cone, eval_grassPolyCoord]`.
-/
theorem GrassLeRoot.proof : GrassLeRoot.Statement := by
  intro f j m ζ g hg
  have h0 : mConeMap (grassCoord f j m) g = 0 := hg
  have h1 : cone (grassPolyCoord f j m) g = 0 := by
    apply MvPolynomial.map_injective (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m))
      (IsFractionRing.injective _ _)
    rw [map_cone, map_zero]
    exact h0
  have h2 := congrArg (MvPolynomial.map
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom) h1
  rw [map_cone, map_zero] at h2
  show (aeval fun p => MvPolynomial.C (rootCoord ζ p) * MvPolynomial.X p.1) g = 0
  simpa [cone, eval_grassPolyCoord] using h2

end

end GroundTheory.Heights₂.Heights
