import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `Units.ext (GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol _)`.
-/
private theorem cj_cj (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (UpperTheory.Gal.Int.Div.cj E z) = z :=
  Units.ext (GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol _)

/- English proof (translation)
Rewrite using `[quo_apply, _root_.map_div, cj_cj, div_mul_div_comm, mul_comm z, div_self']`.
-/
private theorem cj_quo_mul (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (quo E z) * quo E z = 1 := by
  rw [quo_apply, _root_.map_div, cj_cj, div_mul_div_comm, mul_comm z, div_self']

/- English proof (translation)
Establish `hy : conjAd E (y : Ad E) * (y : Ad E) = 1` using `congrArg Units.val h`. Establish `e : ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = Matrix.diagonal fun _ => (y : Ad E)` using `rfl`. Use `show (((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).map (conjAd E)).transpose * 1 * ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1`. Rewrite using `[e, Matrix.mul_one, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]`. Simplify using `only [Function.comp_apply, hy]`.

Conclude with `Matrix.diagonal_one`.
-/
private theorem scal_mem (a : ℕ) (y : Ideles E) (h : UpperTheory.Gal.Int.Div.cj E y * y = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin a) y ∈ UA E a := by
  have hy : conjAd E (y : Ad E) * (y : Ad E) = 1 := congrArg Units.val h
  have e : ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) =
      Matrix.diagonal fun _ => (y : Ad E) := rfl
  show (((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).map (conjAd E)).transpose * 1 *
    ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1
  rw [e, Matrix.mul_one, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  simp only [Function.comp_apply, hy]
  exact Matrix.diagonal_one

/- English proof (translation)
Establish `h : Continuous ((Matrix.scalar (Fin a)).toMonoidHom : Ad E →* Matrix (Fin a) (Fin a) (Ad E))` using `Continuous.matrix_diagonal (A := fun (x : Ad E) (_ : Fin a) => x) (continuous_pi fun _ => continuous_id)`. Conclude with `Continuous.units_map _ h`.
-/
private theorem continuous_scal (a : ℕ) :
    Continuous (fun y : Ideles E => (Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a)) :=
by
  have h : Continuous ((Matrix.scalar (Fin a)).toMonoidHom : Ad E →* Matrix (Fin a) (Fin a) (Ad E)) :=
    Continuous.matrix_diagonal (A := fun (x : Ad E) (_ : Fin a) => x) (continuous_pi fun _ => continuous_id)
  exact Continuous.units_map _ h

/- English proof (translation)
The claim follows from `continuous_id.div' (Continuous.units_map _ GlobalTheory.BCT.GlobLev.continuous_conj_ad)`.
-/
private theorem continuous_quo : Continuous (quo E) :=
  continuous_id.div' (Continuous.units_map _ GlobalTheory.BCT.GlobLev.continuous_conj_ad)

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) (Matrix.diagonal (fun _ => (k : E)) i j) = Matrix.diagonal (fun _ => algebraMap E (Ad E) (k : E)) i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
private theorem ratGL_scalar (a : ℕ) (k : Eˣ) :
    ratGL E a (Matrix.GeneralLinearGroup.scalar (Fin a) k) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (diagUnits E k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap E (Ad E) (Matrix.diagonal (fun _ => (k : E)) i j) =
    Matrix.diagonal (fun _ => algebraMap E (Ad E) (k : E)) i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/- English proof (translation)
Establish `e : UpperTheory.Gal.Int.Div.cj E (diagUnits E k) = diagUnits E (Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k)` using `Units.ext (conjAd_algebraMap (k : E))`. Rewrite using `[quo_apply, e, _root_.map_div]`.
-/
private theorem quo_diag (k : Eˣ) :
    quo E (diagUnits E k) =
      diagUnits E (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) := by
  have e : UpperTheory.Gal.Int.Div.cj E (diagUnits E k) =
      diagUnits E (Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) :=
    Units.ext (conjAd_algebraMap (k : E))
  rw [quo_apply, e, _root_.map_div]

end

/- English proof (translation)
Introduce `E _ _ _ a`. Use `⟨MonoidHom.codRestrict ((Matrix.GeneralLinearGroup.scalar (Fin a)).comp (quo E)) (UA E a) (fun z => scal_mem a _ (cj_quo_mul z)), fun z => rfl, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk ((continuous_scal a).comp continuous_quo) _`. Introduce `z x`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations.

Conclude with `(Matrix.scalar_commute ((quo E z : Ideles E) : Ad E) (fun r => mul_comm _ r) x.1.val).eq`. Introduce `k`. Use `Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.scalar (Fin a) (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k), ?_⟩` and prove the remaining obligations. Rewrite using `[ratGL_scalar, ← quo_diag]`. Both sides reduce to the same expression.

Introduce `z hz`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z) = 1`. Rewrite using `[quo_apply, hz, div_self', map_one]`.
-/
theorem UpperTheory.Gal.Int.Div.zetaEx_of :
    ZetaEx := by
  intro E _ _ _ a
  refine ⟨MonoidHom.codRestrict ((Matrix.GeneralLinearGroup.scalar (Fin a)).comp (quo E)) (UA E a)
    (fun z => scal_mem a _ (cj_quo_mul z)), fun z => rfl, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk ((continuous_scal a).comp continuous_quo) _
  · intro z x
    refine Subtype.ext (Units.ext ?_)
    exact (Matrix.scalar_commute ((quo E z : Ideles E) : Ad E) (fun r => mul_comm _ r) x.1.val).eq
  · intro k
    refine Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.scalar (Fin a)
      (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k), ?_⟩
    rw [ratGL_scalar, ← quo_diag]
    rfl
  · intro z hz
    refine Subtype.ext ?_
    change Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z) = 1
    rw [quo_apply, hz, div_self', map_one]
