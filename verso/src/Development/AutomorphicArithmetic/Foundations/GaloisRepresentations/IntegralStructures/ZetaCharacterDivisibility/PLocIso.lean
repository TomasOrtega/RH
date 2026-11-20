import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTranspose
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

open GlobalTheory.SplitPts in
private noncomputable def cEq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cpl w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc (conjE E) w) ⟨(conjLoc (conjE E) w).injective, fun y => ⟨psi w y, conjLoc_psi w y⟩⟩

open GlobalTheory.SplitPts in
/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)`.
-/
private theorem conjInvT_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (g : GL (Fin a) ((cpl w).adicCompletion E)) :
    GlobalTheory.LFun.ConjPlace.invT (cEq w) a g = invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((invT a R h)⁻¹ : GL (Fin a) R).val.transpose = h.val`. Rewrite using `[← map_inv]`. Express the relevant statement in the definitionally equal form `(((h⁻¹)⁻¹ : GL (Fin a) R).val.transpose).transpose = h.val`. Rewrite using `[inv_inv, Matrix.transpose_transpose]`.
-/
private theorem invT_invT {R : Type} [CommRing R] {a : ℕ} (h : GL (Fin a) R) : invT a R (invT a R h) = h := by
  apply Units.ext
  change ((invT a R h)⁻¹ : GL (Fin a) R).val.transpose = h.val
  rw [← map_inv]
  change (((h⁻¹)⁻¹ : GL (Fin a) R).val.transpose).transpose = h.val
  rw [inv_inv, Matrix.transpose_transpose]

open GlobalTheory.SplitPts in
/- English proof (translation)
Rewrite using `[MulEquiv.symm_apply_eq, conjInvT_eq, invT_map, show Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (Matrix.GeneralLinearGroup.map (psi w) h) = h from Units.ext (Matrix.ext fun i j => conjLoc_psi w _), invT_invT]`.
-/
private theorem conjInvT_symm_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    (h : GL (Fin a) (w.adicCompletion E)) :
    (GlobalTheory.LFun.ConjPlace.invT (cEq w) a).symm h = invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := by
  rw [MulEquiv.symm_apply_eq, conjInvT_eq, invT_map,
    show Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (Matrix.GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _), invT_invT]

open GlobalTheory.SplitPts in
/- English proof (translation)
Introduce `E _ _ _ a w hw`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `locU`. Rewrite using `[(over_split hw).2.1]`. Set `e` to `GlobalTheory.LFun.ConjPlace.invT (cEq w) a`.

Establish `hc1 : Continuous e`. Establish `e1 : (e : GL (Fin a) ((cpl w).adicCompletion E) → GL (Fin a) (w.adicCompletion E)) = fun g => invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g)` using `funext (conjInvT_eq w)`. Rewrite using `[e1]`. Conclude with `(continuous_invT _).comp (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec (conjE E) w).1))`. Establish `hc2 : Continuous e.symm`.

Establish `e1 : (e.symm : GL (Fin a) (w.adicCompletion E) → GL (Fin a) ((cpl w).adicCompletion E)) = fun h => invT a _ (Matrix.GeneralLinearGroup.map (psi w) h)` using `funext (conjInvT_symm_eq w)`. Rewrite using `[e1]`. Conclude with `(continuous_invT _).comp (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))`. Use `⟨{ e with continuous_toFun := hc1, continuous_invFun := hc2 }, fun x => ?_, fun g hg => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e (cLoc (cpl w) x) = cLoc w x`.

Establish `h` using `comp_eq x w`. Rewrite using `[conjInvT_eq w]`. Use `set m := Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (cLoc (cpl w) x) with hm`. Establish `h' : m.val.transpose * (cLoc w x).val = 1` using `h`. Apply `Units.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `((m⁻¹ : GL (Fin a) _).val).transpose = (cLoc w x).val`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul, Matrix.mul_assoc]`. Use `_ = (cLoc w x).val := by`. Rewrite using `[Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]`.

Conclude with `(GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (cEq w) (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff (cEq w) (conjLoc_spec (conjE E) w).2.2) g).1 hg`. Introduce `V _ _ σ hσ`. Establish `h1` using `GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap (cEq w).symm (conjLoc_spec (conjE E) w).1 (σ.comp (GlobalTheory.TypeTame.invTranspose a)) (GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose _ a V σ hσ)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `σ (e g) = σ (GlobalTheory.TypeTame.invTranspose a (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g))`. Rewrite using `[conjInvT_eq w]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Int.Div.locIso_of :
    LocIso := by
  intro E _ _ _ a w hw
  refine ⟨?_, ?_⟩
  · unfold locU
    rw [(over_split hw).2.1]
  let e := GlobalTheory.LFun.ConjPlace.invT (cEq w) a
  have hc1 : Continuous e := by
    have e1 : (e : GL (Fin a) ((cpl w).adicCompletion E) → GL (Fin a) (w.adicCompletion E)) =
        fun g => invT a _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g) := funext (conjInvT_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec (conjE E) w).1))
  have hc2 : Continuous e.symm := by
    have e1 : (e.symm : GL (Fin a) (w.adicCompletion E) → GL (Fin a) ((cpl w).adicCompletion E)) =
        fun h => invT a _ (Matrix.GeneralLinearGroup.map (psi w) h) := funext (conjInvT_symm_eq w)
    rw [e1]
    exact (continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))
  refine ⟨{ e with continuous_toFun := hc1, continuous_invFun := hc2 }, fun x => ?_, fun g hg => ?_, ?_⟩
  · change e (cLoc (cpl w) x) = cLoc w x
    have h := comp_eq x w
    rw [conjInvT_eq w]
    set m := Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) (cLoc (cpl w) x) with hm
    have h' : m.val.transpose * (cLoc w x).val = 1 := h
    apply Units.ext
    change ((m⁻¹ : GL (Fin a) _).val).transpose = (cLoc w x).val
    calc ((m⁻¹ : GL (Fin a) _).val).transpose
        = ((m⁻¹ : GL (Fin a) _).val).transpose * (m.val.transpose * (cLoc w x).val) := by rw [h', Matrix.mul_one]
      _ = (m.val * (m⁻¹ : GL (Fin a) _).val).transpose * (cLoc w x).val := by
          rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (cLoc w x).val := by
          rw [Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  · exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (cEq w)
      (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff (cEq w) (conjLoc_spec (conjE E) w).2.2) g).1 hg
  · intro V _ _ σ hσ
    have h1 := GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap (cEq w).symm
      (conjLoc_spec (conjE E) w).1 (σ.comp (GlobalTheory.TypeTame.invTranspose a))
      (GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose _ a V σ hσ)
    convert h1 using 1
    refine MonoidHom.ext fun g => ?_
    change σ (e g) = σ (GlobalTheory.TypeTame.invTranspose a (Matrix.GeneralLinearGroup.map (conjLoc (conjE E) w) g))
    rw [conjInvT_eq w]
    rfl
