import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem locHeight_ti {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) :
    locHeight (ti g) = locHeight g := by
  have hv : ∀ i j, ((ti g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) j i := fun _ _ => rfl
  have hi : ∀ i j, (((ti g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      (g : Matrix (Fin n) (Fin n) E) j i := fun _ _ => rfl
  refine le_antisymm (locHeight_le (one_le_locHeight g) (fun i j => ?_) fun i j => ?_)
    (locHeight_le (one_le_locHeight _) (fun i j => ?_) fun i j => ?_)
  · rw [hv]; exact norm_inv_apply_le_locHeight g j i
  · rw [hi]; exact norm_apply_le_locHeight g j i
  · rw [← hi]; exact norm_inv_apply_le_locHeight (ti g) j i
  · rw [← hv]; exact norm_apply_le_locHeight (ti g) j i

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem infAt_ti {K : Type*} [Field K] [NumberField K] {n : ℕ} (w : InfinitePlace K)
    (g : AdelicGLn.AdelicGL K n) : infAt w (ti g) = ti (infAt w g) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) b a)).1 w =
    (((infAt w g)⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion) b a
  rw [← Reduction.infAt_inv]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem finAt_ti {K : Type*} [Field K] [NumberField K] {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (g : AdelicGLn.AdelicGL K n) : finAt v (ti g) = ti (finAt v g) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) b a)).2 v =
    (((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion K)) b a
  rw [← Reduction.finAt_inv]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem height_ti {K : Type*} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    height (ti g) = height g := by
  simp only [height, infAt_ti, finAt_ti, locHeight_ti]

/- English proof (translation)
Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem hasModerateGrowth_comp_ti :
    ∀ φ : G3 → ℂ, HasModerateGrowth φ → HasModerateGrowth (fun g : G3 => φ (ti g)) := by
  rintro φ ⟨C, N, h⟩
  exact ⟨C, N, fun g => by simpa only [height_ti] using h (ti g)⟩

end GlobalTheory.CompanionTheory.UnfoldingAlt

end
