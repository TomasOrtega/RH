import Development.AutomorphicArithmetic.AdelicQuotients.ThetaLiftContinuous
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
/- English proof (translation)
Introduce `T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ`. Establish `cX : Cpt σ X.J` using `T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)`. Establish `cW : Cpt σ W.J` using `T.cpt F E σ B d W d 0 hp.base (Or.inr hp.skew) (by simp)`. Take `⟨t1, t2, -⟩` from `(T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp).1 Φ hΦ`. Take `⟨C, hC⟩` from `cX.bdd₂ cW (f := fun x => theta om Φ x.1 x.2) t1 fun γ hγ δ hδ g g' => t2 γ hγ δ hδ g g'`.

Take `⟨C', hC'⟩` from `cX.bdd hφ.1 hφ.2`. Establish `hfin : M.μ M.dom < ⊤` using `cX.fin _ _ hp.good.haar hp.good.dom`. Use `haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩`. Use `haveI := cW.sc`. Use `haveI : FirstCountableTopology (UA σ W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _`.

Establish `hs : Continuous fun g => star (φ g)` using `hφ.1.star`. Unfold `lift`. Use `continuous_of_dominated (bound := fun _ => C * C') (fun h => ?_) (fun h => ?_) (integrable_const _) ?_` and prove the remaining obligations. Conclude with `((t1.comp (continuous_id.prodMk continuous_const)).mul hs).aestronglyMeasurable`. Use `Eventually.of_forall fun g => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_star]`. Conclude with `mul_le_mul (hC (g, h)) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC (g, h)))`. Use `Eventually.of_forall fun g => ?_` and prove the remaining obligations. Conclude with `(t1.comp (continuous_const.prodMk continuous_id)).mul continuous_const`.
-/
theorem UpperTheory.continuous_thetaLift_of_definite :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → Continuous (lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ
  have cX : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have cW : Cpt σ W.J := T.cpt F E σ B d W d 0 hp.base (Or.inr hp.skew) (by simp)
  obtain ⟨t1, t2, -⟩ := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp).1 Φ hΦ
  obtain ⟨C, hC⟩ := cX.bdd₂ cW (f := fun x => theta om Φ x.1 x.2) t1 fun γ hγ δ hδ g g' => t2 γ hγ δ hδ g g'
  obtain ⟨C', hC'⟩ := cX.bdd hφ.1 hφ.2
  have hfin : M.μ M.dom < ⊤ := cX.fin _ _ hp.good.haar hp.good.dom
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI := cW.sc
  haveI : FirstCountableTopology (UA σ W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hs : Continuous fun g => star (φ g) := hφ.1.star
  unfold lift
  refine continuous_of_dominated (bound := fun _ => C * C') (fun h => ?_) (fun h => ?_) (integrable_const _) ?_
  · exact ((t1.comp (continuous_id.prodMk continuous_const)).mul hs).aestronglyMeasurable
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hC (g, h)) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC (g, h)))
  · refine Eventually.of_forall fun g => ?_
    exact (t1.comp (continuous_const.prodMk continuous_id)).mul continuous_const
end
