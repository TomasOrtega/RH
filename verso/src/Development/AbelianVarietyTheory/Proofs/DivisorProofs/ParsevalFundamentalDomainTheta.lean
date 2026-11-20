import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaUnfold

open GlobalTheory.WeilM
open scoped Classical

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Continuous fun x : InfiniteAdeleRing F => ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)), (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))`. Use `Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)`.
-/
theorem continuous_infToMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

/- English proof (translation)
The claim follows from `inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))`.
-/
theorem adele_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Use `(f.continuous.comp ?_).mul (hg.1.continuous.comp ?_)` and prove the remaining obligations. Conclude with `continuous_pi fun i => (continuous_infToMixed F).comp (continuous_fst.comp (continuous_apply i))`.

Conclude with `continuous_pi fun i => continuous_snd.comp (continuous_apply i)`. Consider the case `zero => exact continuous_const`. Consider the case `add Φ Ψ _ _ h1 h2 => exact h1.add h2`. Consider the case `smul c Φ _ h => exact continuous_const.mul h`.
-/
theorem schA_continuous (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine (f.continuous.comp ?_).mul (hg.1.continuous.comp ?_)
    · exact continuous_pi fun i =>
        (continuous_infToMixed F).comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact continuous_const.mul h

def ratEquiv (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → F) ≃ GlobalTheory.ThetaParseval.ratVec F κ :=
  Equiv.ofBijective
    (fun ξ => ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i), (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ξ, rfl⟩⟩)
    ⟨fun a b h => funext fun i => (haveI := adele_nontrivial F; (algebraMap F (AdeleRing (𝓞 F) F)).injective) (congrFun (congrArg Subtype.val h) i),
     fun y => by
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y.1).1 y.2
      exact ⟨ξ, Subtype.ext hξ.symm⟩⟩

/- English proof (translation)
Introduce `F _ _ κ _ μ hμ 𝓕₁ h𝓕 Φ hΦ`. Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Establish `hc` using `schA_continuous F hΦ`. Use `haveI : Countable F := by`.

Establish `b` using `Module.finBasis ℚ F`. Conclude with `Countable.of_equiv _ b.equivFun.toEquiv.symm`. Use `haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (ratEquiv F κ)`. Establish `hm : ∀ c : κ → AF F, Measurable fun x : κ → AF F => ‖Φ (c + x)‖ₑ ^ 2` using `fun c => ((hc.comp (continuous_const.add continuous_id)).measurable.enorm).pow_const 2`. Rewrite using `[lintegral_tsum fun ξ => (hm _).aemeasurable, h𝓕.lintegral_eq_tsum' (fun x => ‖Φ x‖ₑ ^ 2)]`.

Rewrite using `[← ((ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]`. Both sides reduce to the same expression.
-/
theorem unfold : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      ∫⁻ x in 𝓕₁, ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ μ hμ 𝓕₁ h𝓕 Φ hΦ
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hc := schA_continuous F hΦ
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (ratEquiv F κ)
  have hm : ∀ c : κ → AF F, Measurable fun x : κ → AF F => ‖Φ (c + x)‖ₑ ^ 2 := fun c =>
    ((hc.comp (continuous_const.add continuous_id)).measurable.enorm).pow_const 2
  rw [lintegral_tsum fun ξ => (hm _).aemeasurable, h𝓕.lintegral_eq_tsum' (fun x => ‖Φ x‖ₑ ^ 2)]
  rw [← ((ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl
end GlobalTheory.ThetaUnfold
