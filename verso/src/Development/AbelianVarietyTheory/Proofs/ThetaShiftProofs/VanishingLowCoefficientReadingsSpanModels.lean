import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegreeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumFunctionalKillsComplexCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormsVanishingLowCoeffSpannedByRationalStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.ConjKill

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨φ, hφ⟩` from `(GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree GlobalTheory.T.arithmeticCMKnownTheorems_proof _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n).1`. Establish `hle : ∀ F : (recB h).Cusp j ka, F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n` using `fun F => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j ka F.2)`. Establish `e : ∀ F : (recB h).Cusp j ka, cfOf d.yF d.μ d.jj F.1 = φ ⟨F.1, hle F⟩` using `fun F => (hφ ⟨F.1, hle F⟩).symm`. Use `⟨fun F G => ?_, fun a F => ?_⟩` and prove the remaining obligations. Rewrite using `[e, e, e, ← map_add]`.

Both sides reduce to the same expression. Rewrite using `[e, e, ← map_smul]`. Both sides reduce to the same expression.
-/
theorem isLinearMap_cfOf {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) :
    IsLinearMap T.Q.c.F fun F : (recB h).Cusp j ka => cfOf d.yF d.μ d.jj F.1 := by
  obtain ⟨φ, hφ⟩ := (GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree GlobalTheory.T.arithmeticCMKnownTheorems_proof _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n).1
  have hle : ∀ F : (recB h).Cusp j ka, F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun F =>
    cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j ka F.2)
  have e : ∀ F : (recB h).Cusp j ka, cfOf d.yF d.μ d.jj F.1 = φ ⟨F.1, hle F⟩ := fun F => (hφ ⟨F.1, hle F⟩).symm
  refine ⟨fun F G => ?_, fun a F => ?_⟩
  · rw [e, e, e, ← map_add]; rfl
  · rw [e, e, ← map_smul]; rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D T h j hj ka CR Tt cc hD hR`. Distinguish the cases in `hlt : j < D.R.m`. Use `GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational D T h j ka CR Tt cc (fun K₁ _ _ _ φ => ∃ d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁, FamQ T.toCore j ka CR Tt cc K₁ d ∧ φ = fun F => cfOf d.yF d.μ d.jj F.1) ?_ ?_ hR` and prove the remaining obligations. Introduce and unpack `K₁ _ _ _ φ ⟨d, hd, rfl⟩`. Conclude with `⟨isLinearMap_cfOf h.toLawsCore j ka K₁ d, GlobalTheory.T.arcDatum_functional_kills_complexCombinations D T h j hj ka CR Tt cc K₁ d hd⟩`.

Introduce `F hF`. Conclude with `hD hlt F fun K₁ _ _ _ d hd => hF K₁ _ ⟨d, hd, rfl⟩`. Establish `hρ : WeightFamilies.rho D j = 0`. Unfold `WeightFamilies.rho Ranks.sigW`. Conclude with `Nat.sub_eq_zero_of_le (not_lt.1 hlt)`.

Introduce `f hf`. Take `⟨m, a, F, -, hF⟩` from `hR f fun k => (hf k).1`. Use `⟨m, a, F, fun i => ?_, hF⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Formalism.MainNotions.Gaps.EtaleWeightGaps.MggK_eq_top_of_rho hρ]`. Discharge the goal by the elementary cases of `trivial`.
-/
theorem mggOnto_of_rdOnto : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  intro D T h j hj ka CR Tt cc hD hR
  by_cases hlt : j < D.R.m
  · refine GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational D T h j ka CR Tt cc
      (fun K₁ _ _ _ φ => ∃ d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁, FamQ T.toCore j ka CR Tt cc K₁ d ∧
        φ = fun F => cfOf d.yF d.μ d.jj F.1) ?_ ?_ hR
    · rintro K₁ _ _ _ φ ⟨d, hd, rfl⟩
      exact ⟨isLinearMap_cfOf h.toLawsCore j ka K₁ d, GlobalTheory.T.arcDatum_functional_kills_complexCombinations D T h j hj ka CR Tt cc K₁ d hd⟩
    · intro F hF
      exact hD hlt F fun K₁ _ _ _ d hd => hF K₁ _ ⟨d, hd, rfl⟩
  · have hρ : WeightFamilies.rho D j = 0 := by
      unfold WeightFamilies.rho Ranks.sigW
      exact Nat.sub_eq_zero_of_le (not_lt.1 hlt)
    intro f hf
    obtain ⟨m, a, F, -, hF⟩ := hR f fun k => (hf k).1
    refine ⟨m, a, F, fun i => ?_, hF⟩
    rw [SetLike.mem_coe, Formalism.MainNotions.Gaps.EtaleWeightGaps.MggK_eq_top_of_rho hρ]
    trivial

end GlobalTheory.ConjKill
