import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimePlaceBranchExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPointOfPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDisc
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProjectionLocallyInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Introduce `n J q hJ hdim P`. Establish `hq : q ∈ zeroSet J`. Assume the negation of the conclusion as `h`. Use `curveLocalRing_subsingleton J q h` as an intermediate fact. Rewrite `hdim` using `[ringKrullDim_eq_bot_of_subsingleton]`.

Conclude with `absurd hdim (by decide)`. Establish `hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ)`. Use `(ringKrullDim_quotient_le J).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using the standard rewrite rules.

Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by`. Establish `h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)` using `ringKrullDim_nonneg_of_nontrivial`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢`. Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot => simp at h0`.

Consider the case `coe x`. Proceed by induction on `x using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction. Simplify using `only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle`.

Consider the case `coe e => exact ⟨e, rfl⟩`. Establish `hloc : ringKrullDim (curveLocalRing J q) = (e : ℕ)` using `LocalDimDomain.proof n e J hJ he q hq`. Establish `hdim1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)`. Rewrite using `[he]`. Rewrite `hdim` using `[hloc]`.

Conclude with `hdim` after adjusting the coercions. Take `⟨M⟩` from `IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ`. Take `⟨w, hw, hwq, hord⟩` from `hA n J q M hJ P`. Take `⟨r, hr, φ, hφd, hφi, hφm, hφ0⟩` from `hB n J M w hJ hdim1 hw`. Take `⟨U, hU, hUi⟩` from `hC n J M w hJ hdim1 hw`.

Establish `hcont : ContinuousAt φ 0` using `hφd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)`. Take `⟨ε, hε, hεU⟩` from `Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hφ0 ▸ hU))`. Establish `hρ : 0 < min r ε` using `lt_min hr hε`. Establish `hsub : Metric.ball (0 : Fin 1 → ℂ) (min r ε) ⊆ Metric.ball 0 r` using `Metric.ball_subset_ball (min_le_left _ _)`. Establish `hsubU : ∀ t ∈ Metric.ball (0 : Fin 1 → ℂ) (min r ε), φ t ∈ U` using `fun t ht ↦ hεU (Metric.ball_subset_ball (min_le_right _ _) ht)`.

Set `ν : VarBranch J 1 q` to `{ radius := min r ε, radius_pos := hρ, toFun := fun t i ↦ φ t (Sum.inl i), differentiableOn := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 (hφd.mono hsub) (Sum.inl i), injOn := fun a ha b hb hab ↦ hφi (hsub ha) (hsub hb) (hUi ⟨hφm (hsub ha), hsubU a ha⟩ ⟨hφm (hsub hb), hs …`. Use function extensionality and compare the values at `i`. Rewrite using `[hφ0]`. Conclude with `congrFun hwq i,`. Use `mapsTo := fun t ht g hg ↦ by`.

Establish `hg' : rename Sum.inl g ∈ M.ideal` using `Ideal.mem_comap.1 (M.comap_eq.symm ▸ hg)`. Establish `h` using `hφm (hsub ht) _ hg'`. Rewrite `h` using `[eval_rename]`. Conclude with `h }`. Use `⟨ν, fun f ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[hord f, hO n J M w (min r ε) φ hJ hdim1 hρ (hφd.mono hsub) (hφi.mono hsub) (fun t ht ↦ hφm (hsub ht)) hφ0]`. Unfold `branchOrder`. Simplify using `only [eval_rename]`. Both sides reduce to the same expression.
-/
theorem PrimePlaceBranchExists.proof (hA : NormalModelPointOfPlace.Statement) (hB : NormalModelDisc.Statement)
    (hC : NormalModelProjectionLocallyInjective.Statement) (hO : NormalCurveBranchOrder.Statement) :
    PrimePlaceBranchExists.Statement := by
  intro n J q hJ hdim P

  have hq : q ∈ zeroSet J := by
    by_contra h
    have := curveLocalRing_subsingleton J q h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have hloc : ringKrullDim (curveLocalRing J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have hdim1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) := by
    rw [he]
    rw [hloc] at hdim
    exact_mod_cast hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨w, hw, hwq, hord⟩ := hA n J q M hJ P
  obtain ⟨r, hr, φ, hφd, hφi, hφm, hφ0⟩ := hB n J M w hJ hdim1 hw
  obtain ⟨U, hU, hUi⟩ := hC n J M w hJ hdim1 hw

  have hcont : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hφ0 ▸ hU))
  have hρ : 0 < min r ε := lt_min hr hε
  have hsub : Metric.ball (0 : Fin 1 → ℂ) (min r ε) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsubU : ∀ t ∈ Metric.ball (0 : Fin 1 → ℂ) (min r ε), φ t ∈ U := fun t ht ↦
    hεU (Metric.ball_subset_ball (min_le_right _ _) ht)
  let ν : VarBranch J 1 q :=
    { radius := min r ε, radius_pos := hρ, toFun := fun t i ↦ φ t (Sum.inl i),
      differentiableOn := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 (hφd.mono hsub) (Sum.inl i),
      injOn := fun a ha b hb hab ↦ hφi (hsub ha) (hsub hb)
        (hUi ⟨hφm (hsub ha), hsubU a ha⟩ ⟨hφm (hsub hb), hsubU b hb⟩ hab),
      map_zero := by
        funext i
        rw [hφ0]
        exact congrFun hwq i,
      mapsTo := fun t ht g hg ↦ by
        have hg' : rename Sum.inl g ∈ M.ideal := Ideal.mem_comap.1 (M.comap_eq.symm ▸ hg)
        have h := hφm (hsub ht) _ hg'
        rw [eval_rename] at h
        exact h }
  refine ⟨ν, fun f ↦ ?_⟩
  rw [hord f, hO n J M w (min r ε) φ hJ hdim1 hρ (hφd.mono hsub) (hφi.mono hsub) (fun t ht ↦ hφm (hsub ht)) hφ0]
  unfold branchOrder
  simp only [eval_rename]
  rfl

end GroundTheory.Heights₂.Heights
