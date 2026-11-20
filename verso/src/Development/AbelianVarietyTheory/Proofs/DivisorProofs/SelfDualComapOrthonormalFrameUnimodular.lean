import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePull

/- English proof (translation)
Introduce `D V fr Λ hG hΛ v`. Establish `hstar : ∀ x : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = x) → ∃ b : 𝓞 D.host.E, (b : D.host.E) = star x`. Introduce and unpack `x ⟨b, rfl⟩`. Conclude with `⟨Formalism.L2.Pj.barE D b, Formalism.L2.Pj.barE_eq_star D b⟩`. Establish `hcT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 = fr.1ᴴ`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `key : ∀ w : Fin V.rank → D.host.E, ∑ i, ∑ j, star ((fr.1 *ᵥ w) i) * V.gram i j * (fr.1 *ᵥ v) j = ∑ j, star (w j) * v j`. Introduce `w`. Establish `e1 : ∀ x y : Fin V.rank → D.host.E, ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y)`.

Introduce `x y`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hcT, hG, Matrix.one_mulVec]`. Both sides reduce to the same expression.

Establish `hsum : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (w j) * v j) = ∑ j, star (v j) * w j`. Introduce `w`. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', star_star, mul_comm]`.

Establish `hsum' : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (v j) * w j) = ∑ j, star (w j) * v j`. Introduce `w`. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', star_star, mul_comm]`.

Express the relevant statement in the definitionally equal form `fr.1 *ᵥ v ∈ Λ ↔ ∀ w, fr.1 *ᵥ w ∈ Λ → ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star (v j) * w j`. Rewrite using `[hΛ.2]`. Prove the components needed by the constructor for the conclusion. Introduce `H w hw`. Use `hstar _ (H _ hw)` as an intermediate fact.

Rewrite `this` using `[key, hsum]`. Then use the resulting hypothesis. Introduce `H x hx`. Establish `hw : fr.1 *ᵥ ((fr⁻¹).1 *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Use `hstar _ (H ((fr⁻¹).1 *ᵥ x) (by rw [hw]; exact hx))` as an intermediate fact.

Rewrite `this` using `[hsum', ← key, hw]`. Conclude with `this`.
-/
theorem unimod_comap_frame : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).Unimod := by
  intro D V fr Λ hG hΛ v
  have hstar : ∀ x : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = x) → ∃ b : 𝓞 D.host.E, (b : D.host.E) = star x := by
    rintro x ⟨b, rfl⟩
    exact ⟨Formalism.L2.Pj.barE D b, Formalism.L2.Pj.barE_eq_star D b⟩
  have hcT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 = fr.1ᴴ := by
    ext i j
    rfl
  have key : ∀ w : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star ((fr.1 *ᵥ w) i) * V.gram i j * (fr.1 *ᵥ v) j = ∑ j, star (w j) * v j := by
    intro w
    have e1 : ∀ x y : Fin V.rank → D.host.E,
        ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
      intro x y
      simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      rfl
    rw [e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← hcT, hG, Matrix.one_mulVec]
    rfl
  have hsum : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (w j) * v j) = ∑ j, star (v j) * w j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hsum' : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (v j) * w j) = ∑ j, star (w j) * v j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  change fr.1 *ᵥ v ∈ Λ ↔ ∀ w, fr.1 *ᵥ w ∈ Λ → ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star (v j) * w j
  rw [hΛ.2]
  constructor
  · intro H w hw
    have := hstar _ (H _ hw)
    rwa [key, hsum] at this
  · intro H x hx
    have hw : fr.1 *ᵥ ((fr⁻¹).1 *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := hstar _ (H ((fr⁻¹).1 *ᵥ x) (by rw [hw]; exact hx))
    rw [hsum', ← key, hw] at this
    exact this

end GlobalTheory.FramePull
