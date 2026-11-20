import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates

noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

section MeasUJ

variable {n : ℕ} (ε : Fin n → Bool)

def jU (g : Formalism.REAL.UJ ε) : Fin n → Fin n → ℂ := ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jU_eq (g : Formalism.REAL.UJ ε) : (jU ε g : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.uMat g := rfl

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem inUJ_val (g : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := g.2

/- English proof (translation)
Apply `Units.inv_eq_of_mul_eq_one_left` to reduce the goal to its premises. Establish `hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm ε` using `inUJ_val ε g`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [hg]`.

Use `_ = 1 := Formalism.REAL.Jm_mul_self ε`.
-/
theorem inv_val (g : Formalism.REAL.UJ ε) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      Formalism.REAL.Jm ε * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε := by
  apply Units.inv_eq_of_mul_eq_one_left
  have hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm ε := inUJ_val ε g
  calc Formalism.REAL.Jm ε * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Formalism.REAL.Jm ε * (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
          simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [hg]
    _ = 1 := Formalism.REAL.Jm_mul_self ε

/- English proof (translation)
Establish `hcont : Continuous (jU ε)` using `by show Continuous fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)`. Conclude with `(Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val`. Establish `hinj : Function.Injective (jU ε)` using `fun a b h => Subtype.ext (Units.ext h)`. Set `φ : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ` to `fun m => ((m : Matrix (Fin n) (Fin n) ℂ), MulOpposite.op (Formalism.REAL.Jm ε * (m : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε))`. Establish `hφ : Continuous φ` using `continuous_id.prodMk (MulOpposite.continuous_op.comp ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))`.

Establish `hcomp : φ ∘ jU ε = Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘ Subtype.val`. Use function extensionality and compare the values at `g`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, φ, Units.embedProduct_apply, MulOpposite.op_inj]`. Conclude with `(inv_val ε g).symm`.

Use `⟨Topology.IsInducing.of_comp hcont hφ ?_, hinj⟩` and prove the remaining obligations. Rewrite using `[hcomp]`. Conclude with `(Units.isEmbedding_embedProduct.comp IsEmbedding.subtypeVal).isInducing`.
-/
theorem jU_isEmbedding : IsEmbedding (jU ε) := by
  have hcont : Continuous (jU ε) := by
    show Continuous fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
    exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val
  have hinj : Function.Injective (jU ε) := fun a b h => Subtype.ext (Units.ext h)
  let φ : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun m => ((m : Matrix (Fin n) (Fin n) ℂ),
      MulOpposite.op (Formalism.REAL.Jm ε * (m : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε))
  have hφ : Continuous φ :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : φ ∘ jU ε = Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘ Subtype.val := by
    funext g
    refine Prod.ext rfl ?_
    simp only [Function.comp_apply, φ, Units.embedProduct_apply, MulOpposite.op_inj]
    exact (inv_val ε g).symm
  refine ⟨Topology.IsInducing.of_comp hcont hφ ?_, hinj⟩
  rw [hcomp]
  exact (Units.isEmbedding_embedProduct.comp IsEmbedding.subtypeVal).isInducing

/- English proof (translation)
Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `inUJ_val ε g`. Introduce `hm`.

Conclude with `⟨⟨Matrix.nonsingInvUnit (m : Matrix (Fin n) (Fin n) ℂ) (isUnit_iff_ne_zero.mpr (det_ne_zero_of_inUJ ε hm)), hm⟩, rfl⟩`.
-/
theorem jU_range : Set.range (jU ε) = {m : Fin n → Fin n → ℂ | Formalism.REAL.inUJ ε (m : Matrix (Fin n) (Fin n) ℂ)} := by
  ext m
  constructor
  · rintro ⟨g, rfl⟩
    exact inUJ_val ε g
  · intro hm
    exact ⟨⟨Matrix.nonsingInvUnit (m : Matrix (Fin n) (Fin n) ℂ)
      (isUnit_iff_ne_zero.mpr (det_ne_zero_of_inUJ ε hm)), hm⟩, rfl⟩

/- English proof (translation)
Establish `hcl : IsClosed (Set.range (jU ε))`. Rewrite using `[jU_range]`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Conclude with `(⟨jU_isEmbedding ε, hcl⟩ : IsClosedEmbedding (jU ε)).measurableEmbedding`.
-/
theorem jU_measurableEmbedding : MeasurableEmbedding (jU ε) := by
  have hcl : IsClosed (Set.range (jU ε)) := by
    rw [jU_range]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact (⟨jU_isEmbedding ε, hcl⟩ : IsClosedEmbedding (jU ε)).measurableEmbedding

/- English proof (translation)
Use `(jU_measurableEmbedding ε).measurable_comp_iff.mp ?_` and prove the remaining obligations. Establish `h : (jU ε ∘ fun c => toUJ ε (hM c)) = fun c => (M c : Fin n → Fin n → ℂ)`. Use function extensionality and compare the values at `c`. Conclude with `(jU_eq ε _).trans (uMat_toUJ ε (hM c))`. Rewrite using `[h]`.

Conclude with `measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hmeas i j`.
-/
theorem measurable_toUJ {α : Type*} [MeasurableSpace α] (M : α → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ c, IsIsom ε (M c)) (hmeas : ∀ i j, Measurable fun c => M c i j) :
    Measurable fun c => toUJ ε (hM c) := by
  refine (jU_measurableEmbedding ε).measurable_comp_iff.mp ?_
  have h : (jU ε ∘ fun c => toUJ ε (hM c)) = fun c => (M c : Fin n → Fin n → ℂ) := by
    funext c
    exact (jU_eq ε _).trans (uMat_toUJ ε (hM c))
  rw [h]
  exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hmeas i j

end MeasUJ

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
