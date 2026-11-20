import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.AvgCont

/- English proof (translation)
Use `show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}`. Use `isClosed_eq ?_ continuous_const` and prove the remaining obligations. Conclude with `((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id`.
-/
theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  refine isClosed_eq ?_ continuous_const
  exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id

/- English proof (translation)
Establish `hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε` using `hy`. Establish `hm' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε` using `hm`. Use `show (y * m)ᴴ * Formalism.REAL.Jm ε * (y * m) = Formalism.REAL.Jm ε`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [hy', hm']`.
-/
theorem mul_mem_UJset_of_inUJ {n : ℕ} {ε : Fin n → Bool} {y m : Matrix (Fin n) (Fin n) ℂ}
    (hy : y ∈ UJset ε) (hm : Formalism.REAL.inUJ ε m) : y * m ∈ UJset ε := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have hm' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hm
  show (y * m)ᴴ * Formalism.REAL.Jm ε * (y * m) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc mᴴ * yᴴ * Formalism.REAL.Jm ε * (y * m) = mᴴ * (yᴴ * Formalism.REAL.Jm ε * y) * m := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hy', hm']

/- English proof (translation)
The claim follows from `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`.
-/
theorem continuous_maximalCompactSubgroup_toMatrix {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

/- English proof (translation)
Introduce `n ε f hf e he`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))`. Use `haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))`. Use `haveI : LocallyCompactSpace (UJset ε) := (isClosed_UJset ε).isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Set `F : UJset ε → Formalism.REAL.KG ε → ℂ` to `fun y k => e k * f ((y : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK k)`. Establish `hF : Continuous (Function.uncurry F)`. Use `(he.comp continuous_snd).mul ?_` and prove the remaining obligations. Establish `hmaps : ∀ p : UJset ε × Formalism.REAL.KG ε, (p.1 : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK p.2 ∈ UJset ε` using `fun p => mul_mem_UJset_of_inUJ p.1.2 ((p.2 : Formalism.REAL.UJ ε).2)`. Conclude with `hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).matrix_mul ((continuous_maximalCompactSubgroup_toMatrix ε).comp continuous_snd)) hmaps`.

Establish `h` using `continuous_parametric_integral_of_continuous (μ := Formalism.REAL.muK ε) hF isCompact_univ`. Simplify using `only [Measure.restrict_univ] at h`. Conclude with `h`.
-/
theorem continuousOn_avg_right_translates : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ),
    ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  intro n ε f hf e he
  rw [continuousOn_iff_continuous_restrict]
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (UJset ε) :=
    (isClosed_UJset ε).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let F : UJset ε → Formalism.REAL.KG ε → ℂ := fun y k => e k * f ((y : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK k)
  have hF : Continuous (Function.uncurry F) := by
    refine (he.comp continuous_snd).mul ?_
    have hmaps : ∀ p : UJset ε × Formalism.REAL.KG ε,
        (p.1 : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK p.2 ∈ UJset ε :=
      fun p => mul_mem_UJset_of_inUJ p.1.2 ((p.2 : Formalism.REAL.UJ ε).2)
    exact hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).matrix_mul
        ((continuous_maximalCompactSubgroup_toMatrix ε).comp continuous_snd)) hmaps
  have h := continuous_parametric_integral_of_continuous (μ := Formalism.REAL.muK ε) hF isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

end GlobalTheory.AvgCont
