import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
The claim follows from `map_cornerGL_of_zero _ _ (fun _ => rfl) k`.
-/
private theorem fst_finGL' {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) k

/- English proof (translation)
Establish `h` using `GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)`. Rewrite `h` using `[fst_finGL']`. Conclude with `h.symm.trans (by simp)`.
-/
private theorem det_fst {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    ((Matrix.GeneralLinearGroup.det (finGL E 2 k) : (A E)ˣ) : A E).1 = 1 := by
  have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)
  rw [fst_finGL'] at h
  exact h.symm.trans (by simp)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Rewrite using `[ideleNorm_fst, hx]`. Conclude with `Finset.prod_eq_one fun w _ => map_one _`.
-/
private theorem norm_fst {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : (A E)ˣ) (hx : (x : A E).1 = 1) : ((ideleNorm F E x : (A F)ˣ) : A F).1 = 1 := by
  funext v
  rw [ideleNorm_fst, hx]
  exact Finset.prod_eq_one fun w _ => map_one _

/- English proof (translation)
Establish `h` using `TR.infGL_mul_finGL (dM t)`. Establish `h1 : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1`. Establish `ht' : TR.pInf F (t : A F) = 1`. Express the relevant statement in the definitionally equal form `(TR.infEq F).symm (t : A F).1 = 1`. Rewrite using `[ht]`.

Conclude with `map_one _`. Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [ht']`. Rewrite `h` using `[h1, map_one, one_mul]`.

Conclude with `h`.
-/
private theorem dM_of_fst {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (t : (A F)ˣ) (ht : (t : A F).1 = 1) :
    finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t := by
  have h := TR.infGL_mul_finGL (dM t)
  have h1 : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1 := by
    have ht' : TR.pInf F (t : A F) = 1 := by
      change (TR.infEq F).symm (t : A F).1 = 1
      rw [ht]; exact map_one _
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht']
  rw [h1, map_one, one_mul] at h
  exact h

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _`. Set `κ : GL (Fin 2) (Af E) →* GL (Fin 2) (Af F)` to `{ toFun := fun k => Matrix.GeneralLinearGroup.map (pFin F) (dM (nu F (finGL E 2 k))) map_one' := by simp [nu] map_mul' := fun a b => by simp [nu, dM_mul] }`. Use `⟨κ, ?_, fun k => (dM_of_fst _ (norm_fst _ (det_fst k))).symm⟩` and prove the remaining obligations. Establish `hp : Continuous (pFin F)` using `continuous_snd`. Establish `hm : Continuous (Matrix.GeneralLinearGroup.map (n` using `Fin 2) (pFin F)) := Continuous.units_map _ (Continuous.matrix_map continuous_id hp)`.

Establish `hf : Continuous (finGL E 2)` using `Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))`. Conclude with `hm.comp (continuous_dM.comp (continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp hf)))`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.finTr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (_D : Dat F E), FinTr F E := by
  intro F E _ _ _ _ _ _ _ _
  let κ : GL (Fin 2) (Af E) →* GL (Fin 2) (Af F) :=
    { toFun := fun k => Matrix.GeneralLinearGroup.map (pFin F) (dM (nu F (finGL E 2 k)))
      map_one' := by simp [nu]
      map_mul' := fun a b => by simp [nu, dM_mul] }
  refine ⟨κ, ?_, fun k => (dM_of_fst _ (norm_fst _ (det_fst k))).symm⟩
  have hp : Continuous (pFin F) := continuous_snd
  have hm : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (pFin F)) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id hp)
  have hf : Continuous (finGL E 2) := Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  exact hm.comp (continuous_dM.comp (continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp hf)))
