import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinVol

/- English proof (translation)
Use `haveI := GroundTheory.Global.isHaarMeasure_normOneMeasure k`. Use `haveI : Countable ↥(GroundTheory.Global.diagonalNormOne k).op := by haveI := GroundTheory.Global.countable_diagonalNormOne k`. Use `Function.Injective.countable (f := fun x : ↥(GroundTheory.Global.diagonalNormOne k).op => (⟨x.1.unop, Subgroup.mem_op.mp x.2⟩ : ↥(GroundTheory.Global.diagonalNormOne k))) ?_` and prove the remaining obligations. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `MulOpposite.unop_injective` to reduce the goal to its premises. Conclude with `congrArg Subtype.val h`. Establish `hfin : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) < ⊤` using `GroundTheory.Global.normOneMeasure_normOneFundamentalDomain_lt_top k`. Establish `hne : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) ≠ 0` using `(GroundTheory.Global.isFundamentalDomain_normOneFundamentalDomain k (GroundTheory.Global.normOneMeasure k)).measure_ne_zero (NeZero.ne _)`. Use `⟨(GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k)).toReal, ENNReal.toReal_pos hne hfin.ne, ?_⟩` and prove the remaining obligations.

Establish `h2 : volChar (1 : HeckeCharacter k) = ∫ _u in GroundTheory.Global.normOneFundamentalDomain k, (1 : ℂ) ∂GroundTheory.Global.normOneMeasure k`. Unfold `volChar`. Use `congr 1`. Rewrite using `[h2, MeasureTheory.setIntegral_const]`. Simplify using `[Measure.real]`.
-/
theorem volChar_one_eq {k : Type} [Field k] [NumberField k] :
    ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ) := by
  haveI := GroundTheory.Global.isHaarMeasure_normOneMeasure k
  haveI : Countable ↥(GroundTheory.Global.diagonalNormOne k).op := by
    haveI := GroundTheory.Global.countable_diagonalNormOne k
    refine Function.Injective.countable (f := fun x : ↥(GroundTheory.Global.diagonalNormOne k).op =>
      (⟨x.1.unop, Subgroup.mem_op.mp x.2⟩ : ↥(GroundTheory.Global.diagonalNormOne k))) ?_
    intro x y h
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val h
  have hfin : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) < ⊤ :=
    GroundTheory.Global.normOneMeasure_normOneFundamentalDomain_lt_top k
  have hne : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) ≠ 0 :=
    (GroundTheory.Global.isFundamentalDomain_normOneFundamentalDomain k
      (GroundTheory.Global.normOneMeasure k)).measure_ne_zero (NeZero.ne _)
  refine ⟨(GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k)).toReal,
    ENNReal.toReal_pos hne hfin.ne, ?_⟩
  have h2 : volChar (1 : HeckeCharacter k) =
      ∫ _u in GroundTheory.Global.normOneFundamentalDomain k, (1 : ℂ) ∂GroundTheory.Global.normOneMeasure k := by
    unfold volChar
    congr 1
  rw [h2, MeasureTheory.setIntegral_const]
  simp [Measure.real]

end GlobalTheory.CompanionTheory.EpsteinVol
