import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix
open scoped ComplexOrder

section Steps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `M g x hx w`. Use `set k : GL ι ℂ := ((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w with hk`. Establish `hne : invApply g (vecAt v x) w ≠ 0`. Introduce `hz`. Establish `hz' : (k : Matrix ι ι ℂ) *ᵥ vecAt v x w = 0` using `hz`.

Establish `h2 : ((k⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ ((k : Matrix ι ι ℂ) *ᵥ vecAt v x w) = 0`. Rewrite using `[hz', mulVec_zero]`. Rewrite `h2` using `[mulVec_mulVec, Units.inv_mul, one_mulVec]`. Conclude with `h₁ x hx w h2`. Establish `hpos` using `(M.posDef w).dotProduct_mulVec_pos hne`.

Conclude with `(Complex.pos_iff.mp hpos).1`.
-/
theorem WeightPos.proof (h : GroundTheory.Automorphic.HermitianForm F E W) (v : Basis ι E W)
    (h₁ : VecAtNeZero.Statement v) : WeightPos.Statement h v := by
  intro M g x hx w
  set k : GL ι ℂ := ((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w with hk
  have hne : invApply g (vecAt v x) w ≠ 0 := by
    intro hz
    have hz' : (k : Matrix ι ι ℂ) *ᵥ vecAt v x w = 0 := hz
    have h2 : ((k⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ ((k : Matrix ι ι ℂ) *ᵥ vecAt v x w) = 0 := by
      rw [hz', mulVec_zero]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at h2
    exact h₁ x hx w h2
  have hpos := (M.posDef w).dotProduct_mulVec_pos hne
  exact (Complex.pos_iff.mp hpos).1

end Steps

end GroundTheory.Heights₂.Heights.FiniteCovolume
