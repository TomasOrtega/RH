import Formalism.LocalRingCardinality.SpanPowerMembership.TiesGen
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityUnique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open MeasureTheory

namespace Formalism.MainNotions.BesselDiscreteSeries

open Formalism.BasicNotions.Examples₂ Formalism.MainNotions.S

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.DS.dimVlam`. Apply `div_pos` to reduce the goal to its premises. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `a _`. Apply `Finset.prod_pos` to reduce the goal to its premises.

Introduce `b hb`. Establish `hab : a < b` using `(Finset.mem_filter.mp hb).2`. Conclude with `abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt (hlam hab)))`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `a _`.

Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `b hb`. Establish `hab : a < b` using `(Finset.mem_filter.mp hb).2`. Establish `: (a : ℕ) < b` using `hab`. Conclude with `sub_pos.mpr (by exact_mod_cast this)`.
-/
theorem dimVlam_pos_of_strictAnti {n : ℕ} {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    0 < ReciprocityTheory.ChartRestriction.DS.dimVlam lam := by
  unfold ReciprocityTheory.ChartRestriction.DS.dimVlam
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt (hlam hab)))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    have : (a : ℕ) < b := hab
    exact sub_pos.mpr (by exact_mod_cast this)

/- English proof (translation)
Take `⟨-, hspec⟩` from `CD.cdScaleOf_spec CD.cdHaar (epsSH R) (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R)) (CD.sign_split_equiv_inr (epsSH R))`. Use extensionality with `A hA`. Establish `h2` using `congrArg (fun μ : Measure _ => μ A) hspec`. Rewrite `h2` using `[Measure.map_apply (CD.phi_cont (epsSH R) _ _ _).measurable hA]`. Rewrite using `[ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol CD.cdHaar (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R)) (CD.sign_split_equiv_inr (epsSH R)) A hA]`.

Establish `hset : {g | ∃ a ∈ A, Formalism.MainNotions.S.umat a = Matrix.reindex (CD.e0 (epsSH R)) (CD.e0 (epsSH R)) (Formalism.BasicNotions.UpqT.mat g)} = (CD.phi (epsSH R) (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R)) (CD.sign_split_equiv_inr (epsSH R))) ⁻¹' A`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, hag⟩`.

Establish `: a = CD.phi (epsSH R) (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R)) (CD.sign_split_equiv_inr (epsSH R)) g`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hag.trans (CD.coe_phi (epsSH R) _ _ _ g).symm`. Rewrite using `[← this]` and apply the resulting hypothesis.

Introduce `hg`. Conclude with `⟨_, hg, CD.coe_phi (epsSH R) _ _ _ g⟩`. Rewrite using `[hset, h2]`. Both sides reduce to the same expression.
-/
theorem muCD_eq_cdScale (R : Formalism.BasicNotions.Ranks) :
    ReciprocityTheory.ChartRestriction.DS.muCD (epsSH R) =
      (CD.cdScaleOf CD.cdHaar _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R) := by
  obtain ⟨-, hspec⟩ := CD.cdScaleOf_spec CD.cdHaar (epsSH R) (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R))
    (CD.sign_split_equiv_inr (epsSH R))
  ext A hA
  have h2 := congrArg (fun μ : Measure _ => μ A) hspec
  rw [Measure.map_apply (CD.phi_cont (epsSH R) _ _ _).measurable hA] at h2
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol CD.cdHaar (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R))
    (CD.sign_split_equiv_inr (epsSH R)) A hA]
  have hset : {g | ∃ a ∈ A, Formalism.MainNotions.S.umat a = Matrix.reindex (CD.e0 (epsSH R)) (CD.e0 (epsSH R))
      (Formalism.BasicNotions.UpqT.mat g)} =
      (CD.phi (epsSH R) (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R)) (CD.sign_split_equiv_inr (epsSH R))) ⁻¹' A := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨a, ha, hag⟩
      have : a = CD.phi (epsSH R) (CD.e0 (epsSH R)) (CD.sign_split_equiv_inl (epsSH R)) (CD.sign_split_equiv_inr (epsSH R)) g := by
        apply Subtype.ext
        apply Units.ext
        exact hag.trans (CD.coe_phi (epsSH R) _ _ _ g).symm
      rwa [← this]
    · intro hg
      exact ⟨_, hg, CD.coe_phi (epsSH R) _ _ _ g⟩
  rw [hset, h2]
  rfl

/- English proof (translation)
Establish `hlam` using `Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH R P`. Use `⟨ReciprocityTheory.ChartRestriction.DS.dimVlam (lamSH R P), dimVlam_pos_of_strictAnti hlam.1, ?_⟩` and prove the remaining obligations. Introduce `V _ _ σ d hσ hd`. Use `haveI : CompleteSpace V := hσ.1`. Use `haveI : Nontrivial V := hσ.2.1`.

Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Rewrite `hd` using `[← muCD_eq_cdScale]`. Establish `hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R)` using `le_min hp hq`. Establish `h8 : 8 * ((2 * R.rS + R.k + 1 : ℕ) : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) < h`. Establish `h1` using `le_max_right (((2 * R.rS + R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (epsSH R) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf (epsSH R) : ℝ) + 1) (16 * ((2 * R.rS + R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) : ℝ) + 8 * Real. …`.

Establish `h2 : 0 ≤ 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) : ℝ))` using `by positivity`. Establish `h3 : 0 ≤ ((2 * R.rS + R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) : ℝ)` using `by positivity`. Unfold `ReciprocityTheory.ChartRestriction.DS.thrStar at hh`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hΨ : ∀ μ : Fin (2 * R.rS + R.k + 1) → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast (epsSH R) μ h → ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType (epsSH R) (ReciprocityTheory.ChartRestriction.DS.lowK (epsSH R) μ …`.

Introduce `μ hμ hgμ`. Take `⟨T⟩` from `ReciprocityTheory.ChartRestriction.DS.HW.kType_exists (epsSH R) μ hμ`. Take `⟨m, hm⟩` from `ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ`. Conclude with `⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩`. Establish `key` using `ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp hq hlam hgap hh hΨ hσ hv`.

Rewrite `key` using `[ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' hd hv]`. Conclude with `key`.
-/
theorem fdegUniq_of_gap (R : Formalism.BasicNotions.Ranks) (P : Formalism.BasicNotions.HCParam R) (h : ℝ)
    (hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf (epsSH R)) (hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf (epsSH R))
    (hgap : Formalism.QuantumDeterminants.GapAtLeast (epsSH R) (lamSH R P) h)
    (hh : ReciprocityTheory.ChartRestriction.DS.thrStar (epsSH R) + 1 < h) :
    FdegUniq R P := by
  have hlam := Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH R P
  refine ⟨ReciprocityTheory.ChartRestriction.DS.dimVlam (lamSH R P), dimVlam_pos_of_strictAnti hlam.1, ?_⟩
  intro V _ _ σ d hσ hd
  haveI : CompleteSpace V := hσ.1
  haveI : Nontrivial V := hσ.2.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  rw [← muCD_eq_cdScale] at hd
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) := le_min hp hq
  have h8 : 8 * ((2 * R.rS + R.k + 1 : ℕ) : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) < h := by
    have h1 := le_max_right
      (((2 * R.rS + R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (epsSH R) : ℝ) *
        (ReciprocityTheory.ChartRestriction.DS.qOf (epsSH R) : ℝ) + 1)
      (16 * ((2 * R.rS + R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) : ℝ) +
        8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) : ℝ)))
    have h2 : 0 ≤ 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) : ℝ)) := by positivity
    have h3 : 0 ≤ ((2 * R.rS + R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH R) : ℝ) := by positivity
    unfold ReciprocityTheory.ChartRestriction.DS.thrStar at hh
    linarith
  have hΨ : ∀ μ : Fin (2 * R.rS + R.k + 1) → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ →
      ReciprocityTheory.ChartRestriction.DS.GapAtLeast (epsSH R) μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType (epsSH R) (ReciprocityTheory.ChartRestriction.DS.lowK (epsSH R) μ))
        (Ψ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (T.V →L[ℂ] T.V)),
        ReciprocityTheory.ChartRestriction.DS.IsPsiFor (epsSH R) μ T Ψ := by
    intro μ hμ hgμ
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists (epsSH R) μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩
  have key := ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp hq hlam hgap hh hΨ hσ hv
  rw [ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' hd hv] at key
  exact key

end Formalism.MainNotions.BesselDiscreteSeries
