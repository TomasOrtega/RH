import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem cw_mul'_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B := Matrix.map_mul
/- English proof (translation)
The claim follows from `Matrix.map_add _ (map_add _) A B`.
-/
theorem cw_add'_k (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A + B) = d.cw w A + d.cw w B := Matrix.map_add _ (map_add _) A B
/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem cw_one'_k (w : InfinitePlace F) : d.cw w (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cw_transpose'_k (w : InfinitePlace F) {p q : Type} (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ := rfl
/- English proof (translation)
Rewrite using `[incM, incM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem incM_b_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
/- English proof (translation)
Rewrite using `[incM, incM, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem incM_b_inv_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) :
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
      incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
/- English proof (translation)
Establish `e : mat2 (x * y) = mat2 x * mat2 y` using `rfl`. Simplify using `only [inFrame, e, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]`.
-/
theorem inFrame_mul'_k (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]
/- English proof (translation)
Establish `e : mat2 (1 : d.G) = 1` using `rfl`. Simplify using `only [inFrame, e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_inv_mul_k]`.
-/
theorem inFrame_one'_k : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_inv_mul_k]
/- English proof (translation)
Simplify using `only [inFrame, Matrix.mul_assoc]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]`.
-/
theorem matrixRep_eq_frameConj (x : d.G) : mat2 x = incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * inFrame d.b x *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
  simp only [inFrame, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]
/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _`. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_one'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_one'_k]`. Consider the case `cons a L ih`.

Introduce `hL`. Rewrite `hL` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, _root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, ih hL.2]`. Distinguish the cases in `h : w' = a`. Substitute `h` using the available equality.

Simplify using `[hL.1]`. Rewrite using `[R.off_w a w' (f a) h, Matrix.one_mul]`. Simplify using `[h]`.
-/
theorem cw_inFrame_prod'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (f : InfinitePlace F → GR d.n) (w' : InfinitePlace F) :
    ∀ L : List (InfinitePlace F), L.Nodup → d.cw w' (inFrame d.b ((L.map fun w => R.ι w (f w)).prod)) =
      if w' ∈ L then d.cw w' (inFrame d.b (R.ι w' (f w'))) else 1 := by
  intro L
  induction L with
  | nil => intro _; simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_one'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_one'_k]
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, _root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, ih hL.2]
    by_cases h : w' = a
    · subst h
      simp [hL.1]
    · rw [R.off_w a w' (f a) h, Matrix.one_mul]
      simp [h]
/- English proof (translation)
Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_inFrame_prod'_k R (fun w => yrot d.n (R.sg w) t) w _ (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ w)), R.at_w, mR_yrot]`.
-/
theorem dZ_cw_rot'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) (w : InfinitePlace F) :
    dZ d.n R.ζ * d.cw w (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t)) = yrotM d.n (R.sg w) t * dZ d.n R.ζ := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_inFrame_prod'_k R (fun w => yrot d.n (R.sg w) t) w _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ w)), R.at_w, mR_yrot]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
