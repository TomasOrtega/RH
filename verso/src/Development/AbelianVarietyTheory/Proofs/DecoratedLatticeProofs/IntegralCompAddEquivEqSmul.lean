import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfTwist

/- English proof (translation)
Use `haveI : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'`. Set `hT : G ≃ₜ G` to `{ toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }`. Establish `hemb : MeasurableEmbedding T` using `hT.measurableEmbedding`. Use `⟨((ν.map T).addHaarScalarFactor ν : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩` and prove the remaining obligations. Introduce `φ`.

Establish `e` using `Measure.isAddLeftInvariant_eq_smul (ν.map T) ν`. Rewrite using `[← hemb.integral_map φ]`. Use `(congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_` and prove the remaining obligations. Use `show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _`. Rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.
-/
theorem integral_comp_addEquiv_eq_smul {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsAddHaarMeasure] (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : G → ℂ, ∫ x, φ (T x) ∂ν = r * ∫ x, φ x ∂ν := by
  haveI : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'
  let hT : G ≃ₜ G := { toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hemb : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨((ν.map T).addHaarScalarFactor ν : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩
  intro φ
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  rw [← hemb.integral_map φ]
  refine (congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_
  show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/- English proof (translation)
Take `⟨i1, i2, -⟩` from `Formalism.IndefR.Eqv.ae_facts D`. Establish `: {x : Mx D m n | ∀ i j, c * x i j = x i j} = ⋂ i, ⋂ j, {x : Mx D m n | c * x i j = x i j}`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Use `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_` and prove the remaining obligations. Conclude with `continuous_const.mul ((continuous_apply j).comp (continuous_apply i))`. Conclude with `(continuous_apply j).comp (continuous_apply i)`.
-/
theorem isClosed_fix (D : D7) (m n : ℕ) (c : AE D) : IsClosed {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
  obtain ⟨i1, i2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have : {x : Mx D m n | ∀ i j, c * x i j = x i j} = ⋂ i, ⋂ j, {x : Mx D m n | c * x i j = x i j} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  · exact (continuous_apply j).comp (continuous_apply i)

/- English proof (translation)
Introduce `D m n c H hH _ _ ν _ h a`. Take `⟨i1, i2, i3, i4, -⟩` from `lattice_Mx D m n`. Establish `key : ∀ y : Mx D m n, y ∈ H ↔ c • y = y`. Introduce `y`. Rewrite using `[hH]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use extensionality with `i j`. Simplify using `using hy i j`. Introduce `hy i j`.

Simplify using `using congrFun (congrFun hy i) j`. Establish `mem : ∀ (g : GL (Fin m) (AE D)) (b : GL (Fin n) (AE D)) (y : Mx D m n), y ∈ H → g.1 ⬝ y ⬝ b.1 ∈ H`. Introduce `g b y hy`. Rewrite `hy`, the goal using `[key]`. Use `show c • (g.1 * y * b.1) = g.1 * y * b.1`.

Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, hy]`. Establish `hcl : IsClosed (H : Set (Mx D m n))`. Establish `: (H : Set (Mx D m n)) = {x : Mx D m n | ∀ i j, c * x i j = x i j}`. Use extensionality with `x`. Conclude with `hH x`.

Rewrite using `[this]`. Conclude with `isClosed_fix D m n c`. Use `haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology`. Set `T : H ≃+ H` to `{ toFun := fun x => ⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ invFun := fun x => ⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ left_inv := fun x => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (h⁻¹).1 * (h.1 * x.1 * a.1) * (a⁻¹).1 = x.1`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Use `right_inv := fun x => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show h.1 * ((h⁻¹).1 * x.1 * (a⁻¹).1) * a.1 = x.1`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Use the proof step `map_add' := fun x y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show h.1 * (x.1 + y.1) * a.1 = h.1 * x.1 * a.1 + h.1 * y.1 * a.1`.

Rewrite using `[Matrix.mul_add, Matrix.add_mul] }`. Establish `hc : Continuous T` using `by show Continuous fun x : H => (⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ : H)`. Conclude with `Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _`. Establish `hc' : Continuous T.symm` using `by show Continuous fun x : H => (⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ : H)`. Conclude with `Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _`.

Take `⟨r, hr, hφ⟩` from `integral_comp_addEquiv_eq_smul ν T hc hc'`. Conclude with `⟨r, hr, fun φ => hφ (fun x : H => φ x.1)⟩`.
-/
theorem integral_twist_fix_eq_smul : ∀ (D : D7) (m n : ℕ) (c : AE D) (H : AddSubgroup (Mx D m n)), (∀ x, x ∈ H ↔ ∀ i j, c * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure] (h : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ φ : Mx D m n → ℂ, ∫ x : H, φ (h.1 ⬝ x.1 ⬝ a.1) ∂ν = r * ∫ x : H, φ x.1 ∂ν := by
  intro D m n c H hH _ _ ν _ h a
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  have key : ∀ y : Mx D m n, y ∈ H ↔ c • y = y := by
    intro y
    rw [hH]
    constructor
    · intro hy; ext i j; simpa using hy i j
    · intro hy i j; simpa using congrFun (congrFun hy i) j
  have mem : ∀ (g : GL (Fin m) (AE D)) (b : GL (Fin n) (AE D)) (y : Mx D m n), y ∈ H → g.1 ⬝ y ⬝ b.1 ∈ H := by
    intro g b y hy
    rw [key] at hy ⊢
    show c • (g.1 * y * b.1) = g.1 * y * b.1
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hcl : IsClosed (H : Set (Mx D m n)) := by
    have : (H : Set (Mx D m n)) = {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
      ext x; exact hH x
    rw [this]; exact isClosed_fix D m n c
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  let T : H ≃+ H :=
    { toFun := fun x => ⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩
      invFun := fun x => ⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (h⁻¹).1 * (h.1 * x.1 * a.1) * (a⁻¹).1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
          Matrix.mul_one]
      right_inv := fun x => by
        apply Subtype.ext
        show h.1 * ((h⁻¹).1 * x.1 * (a⁻¹).1) * a.1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
      map_add' := fun x y => by
        apply Subtype.ext
        show h.1 * (x.1 + y.1) * a.1 = h.1 * x.1 * a.1 + h.1 * y.1 * a.1
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous T := by
    show Continuous fun x : H => (⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hc' : Continuous T.symm := by
    show Continuous fun x : H => (⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  obtain ⟨r, hr, hφ⟩ := integral_comp_addEquiv_eq_smul ν T hc hc'
  exact ⟨r, hr, fun φ => hφ (fun x : H => φ x.1)⟩

end GlobalTheory.HalfTwist
