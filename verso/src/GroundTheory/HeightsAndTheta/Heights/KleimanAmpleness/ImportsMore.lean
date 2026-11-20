import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartSecOverOfMem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM β Q hQ p b m c i`. Establish `hbun : ∀ (L : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : K → ℤ), BundleRealises y k₀ L δ → ∀ J, (L.sub J : Set Ω) = chartSecOver F y k₀ e δ J`. Introduce `L δ hL J`. Use extensionality with `t`. Rewrite using `[SetLike.mem_coe, mem_sub_iff_gam]`.

Use `exists_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[Kleiman.SubSystem.gam, hL]`. Establish `hO : ∀ (a : ℤ) J, ((Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) a).sub J : Set Ω) = chartSecOver F y k₀ e (a • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) J` using `fun a => hbun (Kleiman.twistBundle F _ a) _ (hBase F K ι Ω y k₀ N e _ rfl hM a)`. Establish `hmul : ∀ (R R' : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ δ' : K → ℤ), (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) → (∀ J, (R'.sub J : Set Ω) = chartSecOver F y k₀ e δ' J) → ∀ J, ((R.twist R').sub J : Set Ω) = chartSecOver F …`. Introduce `R R' δ δ' hR hR' J`.

Rewrite using `[twist_sub_eq_mul, Submodule.mul_eq_span_mul_set, hR' J, hR J]`. Conclude with `hMul F K ι Ω y k₀ N e hM δ' δ J`. Establish `hpow : ∀ (R : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ : K → ℤ), (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) → ∀ (n : ℕ) J, ((R.pow n).sub J : Set Ω) = chartSecOver F y k₀ e (n • δ) J`. Introduce `R δ hR n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `J`. Establish `h0` using `hO 0 J`. Rewrite `h0` using `[zero_smul]`. Rewrite using `[zero_smul]`.

Conclude with `h0`. Consider the case `succ n ih`. Introduce `J`. Rewrite using `[succ_nsmul']`. Conclude with `hmul _ _ _ _ ih hR J`.

Establish `hT` using `hmul _ _ _ _ (hpow _ _ (hmul _ _ _ _ (hpow _ _ (hbun Q β hQ) p) (hO m)) b) (hO c)`. Establish `hγ : c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + b • (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + p • β) = b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀`. Simplify using `only [IndefiniteRowSideFullHecke.Kleiman2.stepL]`. Use `module`. Rewrite `hT` using `[hγ]`.

Take `⟨e₁⟩` from `hRef F K ι Ω y k₀ N e hM _ _ hT i`. Take `⟨e₂⟩` from `hLoc F K ι Ω y _ i`. Conclude with `⟨e₁.trans e₂⟩`.
-/
theorem ModelCechTwist.proof (hMul : ChartSecMul.Statement) (hBase : BaseRealises.Statement)
    (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) : ModelCechTwist.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM β Q hQ p b m c i

  have hbun : ∀ (L : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : K → ℤ),
      BundleRealises y k₀ L δ → ∀ J, (L.sub J : Set Ω) = chartSecOver F y k₀ e δ J := by
    intro L δ hL J
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hL]
  have hO : ∀ (a : ℤ) J,
      ((Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) a).sub J : Set Ω) =
        chartSecOver F y k₀ e (a • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) J := fun a =>
    hbun (Kleiman.twistBundle F _ a) _ (hBase F K ι Ω y k₀ N e _ rfl hM a)

  have hmul : ∀ (R R' : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ δ' : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      (∀ J, (R'.sub J : Set Ω) = chartSecOver F y k₀ e δ' J) →
      ∀ J, ((R.twist R').sub J : Set Ω) = chartSecOver F y k₀ e (δ' + δ) J := by
    intro R R' δ δ' hR hR' J
    rw [twist_sub_eq_mul, Submodule.mul_eq_span_mul_set, hR' J, hR J]
    exact hMul F K ι Ω y k₀ N e hM δ' δ J
  have hpow : ∀ (R : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      ∀ (n : ℕ) J, ((R.pow n).sub J : Set Ω) = chartSecOver F y k₀ e (n • δ) J := by
    intro R δ hR n
    induction n with
    | zero =>
      intro J
      have h0 := hO 0 J
      rw [zero_smul] at h0
      rw [zero_smul]
      exact h0
    | succ n ih =>
      intro J
      rw [succ_nsmul']
      exact hmul _ _ _ _ ih hR J
  have hT := hmul _ _ _ _ (hpow _ _ (hmul _ _ _ _ (hpow _ _ (hbun Q β hQ) p) (hO m)) b) (hO c)
  have hγ : c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + b • (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + p • β) =
      b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp only [IndefiniteRowSideFullHecke.Kleiman2.stepL]
    module
  rw [hγ] at hT
  obtain ⟨e₁⟩ := hRef F K ι Ω y k₀ N e hM _ _ hT i
  obtain ⟨e₂⟩ := hLoc F K ι Ω y _ i
  exact ⟨e₁.trans e₂⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
