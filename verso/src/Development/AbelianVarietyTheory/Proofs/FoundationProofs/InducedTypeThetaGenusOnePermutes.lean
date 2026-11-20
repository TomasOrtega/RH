import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InducedType

open Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaOf_mul {R : Ranks} (H : Host R) (g g' : R.GG) :
    H.sigmaOf (g * g') = H.sigmaOf g * H.sigmaOf g' := map_mul (H.gal).symm g g'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaOf_one {R : Ranks} (H : Host R) : H.sigmaOf 1 = 1 := map_one (H.gal).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emb_apply {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) : H.emb g x = H.φ₀ (H.sigmaOf g x) := rfl

def galK {R : Ranks} (H : Host R) (g : R.Psi) : H.E ≃ₐ[H.K] H.E :=
  { (H.sigmaOf g : H.E ≃+* H.E) with
    commutes' := fun a => sigmaOf_fix_K H g g.2 a a.2 }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem galK_apply {R : Ranks} (H : Host R) (g : R.Psi) (x : H.E) : galK H g x = H.sigmaOf g x := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem galK_bijective {R : Ranks} (H : Host R) : Function.Bijective (galK H) := by
  constructor
  · intro g g' h
    apply Subtype.ext
    apply (H.gal).symm.injective
    exact AlgEquiv.ext fun x => congrArg (fun f : H.E ≃ₐ[H.K] H.E => f x) h
  · intro s
    refine ⟨⟨H.galE (s.restrictScalars ℚ), ?_⟩, ?_⟩
    · rw [H.galE_mem_Psi_iff]
      exact s.commutes ⟨_, bE_mem H⟩
    · refine AlgEquiv.ext fun x => ?_
      rw [galK_apply, sigmaOf_galE]
      rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem restrict_K (D : D7) : GL3Theta.InducedCMType D := fun τ a => by
  change D.host.φ₀ (D.host.sigmaOf _ _) = _
  rw [sigmaOf_fix_K D.host _ (D.eTau τ).2 _ a.2]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem sum_eq_trace (D : D7) : TraceMapNormalisation D := fun y => by
  have hE := D.host.hostE_isGalois
  have h := trace_eq_sum_automorphisms (K := D.host.K) (L := D.host.E) y
  change _ = D.host.φ₀ (algebraMap D.host.K D.host.E _)
  rw [h, map_sum]
  exact Fintype.sum_bijective (galK D.host ∘ D.eTau) ((galK_bijective D.host).comp D.eTau.bijective) _ _
    (fun τ => rfl)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem permutes (D : D7) : EmbeddingPermutesTypes D := fun M ρ hK hM => by
  have h0 : ∀ x, D.host.φ₀ x ∈ M := fun x => by
    have := hM (D.eTau.symm 1) x
    rwa [embT, Equiv.apply_symm_apply, emb_apply, Subgroup.coe_one, sigmaOf_one] at this
  let ψ : D.host.E →+* ℂ := (ρ : M →+* ℂ).comp (D.host.φ₀.codRestrict M h0)
  have hψ : ∀ x, cj M ρ (D.host.φ₀ x) = ψ x := fun x => by
    rw [cj, TaylorLogMetric.liftM, dif_pos (h0 x)]
    rfl
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ψ
  have hgP : g ∈ D.R.Psi := by
    rw [← galE_sigmaOf D.host g, D.host.galE_mem_Psi_iff]
    apply D.host.φ₀.injective
    rw [← emb_apply, hg, ← hψ]
    exact (hK ⟨_, bE_mem D.host⟩).2
  refine ⟨D.eTau.trans ((Equiv.mulLeft (⟨g, hgP⟩ : D.R.Psi)).trans D.eTau.symm), fun τ x => ?_⟩
  rw [embT, emb_apply, hψ, ← hg, embT, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.coe_mulLeft, Subgroup.coe_mul, emb_apply, emb_apply, sigmaOf_mul]
  rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem induced_type : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D :=
  fun D => ⟨⟨restrict_K D, sum_eq_trace D⟩, permutes D⟩

end GlobalTheory.InducedType
