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
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem map_cone {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (y : (Σ k, ι k) → R)
    (g : MRing ι) : MvPolynomial.map φ (cone y g) = cone (fun p => φ (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [cone]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [cone]

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
