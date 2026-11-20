import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSphericalNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldSphericalVectorTheta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitSphericalVectorTheta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilMaxCompactFixedVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldInducedMaxCompactVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedUnramifiedHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedNormalizationLambda
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WSupport

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality.

Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem sphN_of_std (hS : Ad3.K.QuadraticBaseChangeGL3.Th.STDSPH K) (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K} {v : Pl}
    (m : LM c v) (hok : m.ok) (hU : Unr c v) (hstd : m.std) : SphN m.W := by
  cases m with
  | sp w₁ w₂ Φ =>
    obtain ⟨hne, -, -⟩ := hok
    have hΦ : Φ = _ := hstd
    subst hΦ
    exact (hS h2 c v hU _ (Or.inl ⟨w₁, w₂, inferInstance, inferInstance, hne, rfl⟩)).1
  | ns w σ η Φ =>
    obtain ⟨hu, hσ, hη, -⟩ := hok
    have hΦ : Φ = _ := hstd
    subst hΦ
    exact (hS h2 c v hU _ (Or.inr ⟨w, inferInstance, hu, σ, η, hσ, hη, rfl⟩)).1

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

A detailed English derivation is pending.
-/
theorem W_eq_zero_of_not_plus {c : HeckeCharacter K} {v : Pl} (m : LM c v) (g : GL (Fin 2) (Qv v))
    (h : ¬ m.plus g) : m.W g = 0 := by
  cases m with
  | sp w₁ w₂ Φ => exact absurd trivial h
  | ns w σ η Φ =>
    simp only [LM.W]
    unfold GL2LocalData.Wc
    exact dif_neg h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem wsup_of_stdsph (hS : Ad3.K.QuadraticBaseChangeGL3.Th.STDSPH K) : Ad3.K.QuadraticBaseChangeGL3.Th.WSUP K := by
  classical
  intro h2 c n t M hM g hg
  obtain ⟨hok, S0, hS0⟩ := hM
  unfold WM pw2
  by_cases hdet : 0 < ((GL2Classical.realPart g).val).det
  · have hv : ∃ v, ¬ (M v).plus (finAt v g) := by
      by_contra hcon
      push Not at hcon
      exact hg ⟨hcon, hdet⟩
    obtain ⟨v₀, hv₀⟩ := hv
    obtain ⟨S, hSi⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
    have hz : ∏ᶠ v, (M v).W (finAt v g) = 0 := by
      refine finprod_eq_zero _ v₀ (W_eq_zero_of_not_plus _ _ hv₀) ?_
      refine (S0 ∪ S).finite_toSet.subset ?_
      intro v hv
      by_contra hn
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
      obtain ⟨h1, h3⟩ := hn
      apply hv
      have hsph := sphN_of_std hS h2 (M v) (hok v) (hS0 v h1).1 (hS0 v h1).2
      show (M v).W (finAt v g) = 1
      have hk := hsph.1 _ (hSi v h3) 1
      rw [one_mul] at hk
      rw [hk]
      exact hsph.2
    rw [hz, mul_zero]
  · have : WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart g) = 0 := by
      unfold WcR
      exact dif_neg hdet
    rw [this, zero_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem wsup : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.WSUP K := by
  intro K _ _
  have hN := GlobalTheory.CompanionTheory.UnitNormUnr.normU
  have hF : Ad3.K.QuadraticBaseChangeGL3.Th.SPHF := GlobalTheory.CompanionTheory.SphFUnr.sphf GlobalTheory.T.weil_induced_representation_hypothesis
    (GlobalTheory.CompanionTheory.PiKFUnr.pikf GlobalTheory.CompanionTheory.RwKF.rwkf GlobalTheory.CompanionTheory.NormModulus.wMod hN) hN
  exact wsup_of_stdsph (GlobalTheory.CompanionTheory.StdSphOf.stdsph K hF GlobalTheory.CompanionTheory.SphTheta.SplitSph.sphs_direct
    (GlobalTheory.CompanionTheory.LamUnr.lamU hN) hN)

end GlobalTheory.CompanionTheory.WSupport
