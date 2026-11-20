import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalWhittakerUnipotentCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSphericalNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaSpherical
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldInducedMaxCompactVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedMaxCompactVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilMaxCompactFixedVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilMaxCompactFixedVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedUnramifiedHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitRepresentationHypothesis
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.StdValue

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem degreeOneEmbedding_zero {K : Type} [Field K] [NumberField K] (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have h := Function.leftInverse_invFun (algebraMap (Qv v) (Kv K w)).injective 0
  simpa [dg1] using h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem std_unit : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), Unr c v → m.ok → m.std →
      ∀ k ∈ integralGL (Qv v) 2, m.W k = 1 ∧ m.val k 0 = 1 := by
  intro K _ _ h2 c v m hU hok hs k hk
  have hS := GlobalTheory.CompanionTheory.GlobalWhittakerPsi.LM_W_sph h2 m hok hU hs
  refine ⟨?_, ?_⟩
  · have h := hS.1 k hk 1
    rw [one_mul] at h
    rw [h]
    exact hS.2
  · obtain ⟨hχc, hχ1, hχ0⟩ := GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v
    cases m with
    | @sp w₁ w₂ i₁ i₂ Φ =>
      obtain rfl : Φ = _ := hs
      have r₁ : IsUnramifiedChar (cAt c v w₁) :=
        GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
      have hP := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.piks
        (GlobalTheory.CompanionTheory.SphTheta.SplitRWK.rwks GlobalTheory.CompanionTheory.SplitRep.sRep) (Qv v) _ hχc hχ1 hχ0 _ r₁ k hk
      simp only [LM.val]
      rw [hP, degreeOneEmbedding_zero, degreeOneEmbedding_zero]
      exact Set.indicator_of_mem (show ((0 : Qv v), (0 : Qv v)) ∈
        {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} from ⟨zero_mem _, zero_mem _⟩) _
    | @ns w i σ η Φ =>
      haveI := i
      obtain rfl : Φ = _ := hs
      obtain ⟨hu, hσ, hη, -⟩ := hok
      rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hU w).2) with
        ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩
      · exact absurd ((hu a ha).trans (hu b hb).symm) hab
      obtain rfl : w' = w := hu w' hw'
      have hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2 :=
        GlobalTheory.CompanionTheory.NormGauss.card_E hf hord
      have hcont : Continuous (algebraMap (Qv v) (Kv K w')) := continuous_adicCompletionMap v w'
      have hP := GlobalTheory.CompanionTheory.PiKFUnr.pikf GlobalTheory.CompanionTheory.RwKF.rwkf GlobalTheory.CompanionTheory.NormModulus.wMod
        GlobalTheory.CompanionTheory.UnitNormUnr.normU (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres
        (localChar c w') (hU w').1 k hk
      simp only [LM.val]
      have hP' := congrFun hP (algebraMap K (Kv K w') 0)
      refine hP'.trans ?_
      rw [map_zero]
      have h0 : (0 : Kv K w') ∈ 𝒪[Kv K w'] := zero_mem _
      exact Set.indicator_of_mem (show (0 : Kv K w') ∈ {x : Kv K w' | x ∈ 𝒪[Kv K w']} from h0) _

end GlobalTheory.CompanionTheory.StdValue
