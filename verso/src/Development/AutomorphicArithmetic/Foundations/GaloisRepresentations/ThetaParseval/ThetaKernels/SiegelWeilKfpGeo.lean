import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def rot_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) : d.G :=
  (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => R.ι w (yrot d.n (R.sg w) t)).prod
/- English proof (translation)
Unfold `_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k`. Use `d.K.list_prod_mem fun x hx => ?_` and prove the remaining obligations. Take `⟨w, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `_root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)`.
-/
theorem rot_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t ∈ d.K := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k
  refine d.K.list_prod_mem fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)
/- English proof (translation)
Take `⟨s, -, hs1, hs2, -, -⟩` from `Place.exists_sec d.cm d.B.emb`. Use `⟨s (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W, ?_, fun w => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Rewrite using `[← smul_mul_assoc, hs2, zero_mul]`.

Use extensionality with `i j`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs1]`.
-/
theorem exists_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) :
    ∃ W' : Mx F E d.m d.n, finOne F • W' = 0 ∧ ∀ w, d.cw w W' = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W := by
  obtain ⟨s, -, hs1, hs2, -, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨s (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W, ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← smul_mul_assoc, hs2, zero_mul]
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs1]
def tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) : Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_tw_k R W).choose
def vline_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (z : ℂ) : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (realAd F z.re • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F z.im • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ
/- English proof (translation)
Use `set bas := Algebra.TensorProduct.basis (AF F) d.bs`. Establish `key : ∀ z : AE F E, finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0`. Introduce `z`. Rewrite using `[← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]`. Simplify using `only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, finOne_mul_eq_zero_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.zero_apply]`. Use `(key _).2 fun l => ?_` and prove the remaining obligations.

Conclude with `congrFun h (i, j, l)`. Introduce `h`. Use function extensionality and compare the values at `⟨i, j, l⟩`. Conclude with `(key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l`.
-/
theorem fin_eq_zero_iff_k (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X = 0 ↔ finOne F • X = 0 := by
  set bas := Algebra.TensorProduct.basis (AF F) d.bs
  have key : ∀ z : AE F E, finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0 := by
    intro z
    rw [← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]
    simp only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      finOne_mul_eq_zero_iff]
  constructor
  · intro h
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    refine (key _).2 fun l => ?_
    exact congrFun h (i, j, l)
  · intro h
    funext ⟨i, j, l⟩
    exact (key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l
end PositivityTheory.SiegelWeilFormula.KFP
end
end
