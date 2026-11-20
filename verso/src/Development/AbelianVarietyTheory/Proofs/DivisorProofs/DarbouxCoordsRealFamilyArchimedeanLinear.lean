import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.RealDirCoord

/- English proof (translation)
Use `Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)` and prove the remaining obligations. Conclude with `(NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)`. Conclude with `(NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)`.
-/
theorem continuous_ringEquiv_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Both sides reduce to the same expression. Consider the case `tmul a x`. Rewrite using `[TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]`.

Use `congr 1`. Use `show ((0 : Ainf F) * a.1, (1 : Af F) * a.2) = ((0 : Ainf F), a.2)`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb => rw [smul_add, ha, hb, map_add, map_add]`. Both sides reduce to the same expression.
-/
theorem eps_smul_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (z : AF F ⊗[F] E) :
    (pairA F 0 1) • z = LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul a x =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    congr 1
    show ((0 : Ainf F) * a.1, (1 : Af F) * a.2) = ((0 : Ainf F), a.2)
    simp
  | add a b ha hb => rw [smul_add, ha, hb, map_add, map_add]; rfl

/- English proof (translation)
The claim follows from `eps_smul_gen z`.
-/
theorem eps_smul_eq (D : D7) (z : AE D) :
    (pairA D.host.F 0 1) • z =
      LinearMap.rTensor D.host.E (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (finPart D z) :=
  eps_smul_gen z

/- English proof (translation)
The claim follows from `one_mul x.2`.
-/
theorem eps_mul_snd {F : Type} [Field F] [NumberField F] (x : AF F) :
    (pairA F 0 1 * x).2 = x.2 := one_mul x.2

/- English proof (translation)
Introduce `D S T κ _ e k L hL hfin`. Establish `hε : ∀ t, (pairA D.host.F 0 1) • L t = 0`. Introduce `t`. Use extensionality with `i j`. Establish `h0 : finPart D (L t i j) = 0` using `congrFun (congrFun (hfin t) i) j`.

Rewrite using `[Matrix.smul_apply, eps_smul_eq, h0, LinearMap.map_zero]`. Both sides reduce to the same expression. Establish `hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0`. Introduce `t i`. Establish `h` using `congrArg e (hε t)`.

Rewrite `h` using `[LinearEquiv.map_smul, LinearEquiv.map_zero]`. Establish `h1` using `congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)`. Establish `h2` using `congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)`. Conclude with `⟨(eps_mul_snd _).symm.trans h1, (eps_mul_snd _).symm.trans h2⟩`. Establish `he : Continuous e` using `by haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩ haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) := inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin _ → Fin _ → AE D))`.

Conclude with `IsModuleTopology.continuous_of_linearMap e.toLinearMap`. Establish `hc : ∀ (p : ((κ → AF D.host.F) × (κ → AF D.host.F)) → (κ → AF D.host.F)), Continuous p → (∀ x y, p (x + y) = p x + p y) → ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1`. Introduce `p hp hadd`. Set `f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace D.host.F)` to `{ toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1 map_zero' := by`. Use function extensionality and compare the values at `i`.

Establish `h0 : p 0 = 0` using `by simpa using hadd 0 0`. Rewrite using `[map_zero, LinearEquiv.map_zero, h0]`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)`. Use the proof step `map_add' := by`. Introduce `a b`.

Use function extensionality and compare the values at `i`. Rewrite using `[map_add, LinearEquiv.map_add, hadd]`. Conclude with `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) _ _ }`. Establish `hf : Continuous f`. Use `continuous_pi fun i => ?_` and prove the remaining obligations.

Conclude with `(continuous_ringEquiv_mixed D.host.F).comp (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))`. Conclude with `⟨f.toRealLinearMap hf, fun t i => rfl⟩`. Take `⟨P, hP⟩` from `hc Prod.fst continuous_fst (fun _ _ => rfl)`. Take `⟨Q, hQ⟩` from `hc Prod.snd continuous_snd (fun _ _ => rfl)`. Use `⟨P, Q, fun t => ?_⟩` and prove the remaining obligations.

Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Use `show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i), 0)`. Rewrite using `[hP, RingEquiv.symm_apply_apply]`. Conclude with `Prod.ext rfl (hsnd t i).1`. Use `show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i), 0)`.

Rewrite using `[hQ, RingEquiv.symm_apply_apply]`. Conclude with `Prod.ext rfl (hsnd t i).2`.
-/
theorem darboux_real_coords : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  intro D S T κ _ e k L hL hfin

  have hε : ∀ t, (pairA D.host.F 0 1) • L t = 0 := by
    intro t
    ext i j
    have h0 : finPart D (L t i j) = 0 := congrFun (congrFun (hfin t) i) j
    rw [Matrix.smul_apply, eps_smul_eq, h0, LinearMap.map_zero]
    rfl
  have hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0 := by
    intro t i
    have h := congrArg e (hε t)
    rw [LinearEquiv.map_smul, LinearEquiv.map_zero] at h
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)
    have h2 := congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)
    exact ⟨(eps_mul_snd _).symm.trans h1, (eps_mul_snd _).symm.trans h2⟩

  have he : Continuous e := by
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
      inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin _ → Fin _ → AE D))
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc : ∀ (p : ((κ → AF D.host.F) × (κ → AF D.host.F)) → (κ → AF D.host.F)), Continuous p →
      (∀ x y, p (x + y) = p x + p y) →
      ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F),
        ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1 := by
    intro p hp hadd
    let f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace D.host.F) :=
      { toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1
        map_zero' := by
          funext i
          have h0 : p 0 = 0 := by simpa using hadd 0 0
          rw [map_zero, LinearEquiv.map_zero, h0]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
        map_add' := by
          intro a b
          funext i
          rw [map_add, LinearEquiv.map_add, hadd]
          exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) _ _ }
    have hf : Continuous f := by
      refine continuous_pi fun i => ?_
      exact (continuous_ringEquiv_mixed D.host.F).comp
        (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))
    exact ⟨f.toRealLinearMap hf, fun t i => rfl⟩
  obtain ⟨P, hP⟩ := hc Prod.fst continuous_fst (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := hc Prod.snd continuous_snd (fun _ _ => rfl)
  refine ⟨P, Q, fun t => ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i), 0)
    rw [hP, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).1
  · show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i), 0)
    rw [hQ, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).2

end GlobalTheory.RealDirCoord
