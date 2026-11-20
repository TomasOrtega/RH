import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def DegreeGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
      ptsIntegral P (pot L) (fun _ => 1) =
        NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) (fun j => (L j).a)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isArithVar_projLine : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ => ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    have hc : Nat.card ((_ : Unit) × PBlk 2 ()) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    rfl

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isSmoothHerm_fsLine (n : ℕ) : IsSmoothHerm (fsLine n) := by
  have hfun : (fsLine n).h = fun z => ∏ k : Unit, Real.sqrt (∑ i : Fin n, ‖z ⟨k, i⟩‖ ^ 2) := by
    funext z
    simp only [fsLine, HermLine.ofMetrics, fsMetric, Pi.one_apply, zpow_one,
      EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ContDiffOn.sqrt ?_ fun z hz => ?_
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, PBlk n k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem DegreeGeneric.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧ ∀ j, IsSmoothHerm (![fsLine 2] j) :=
  ⟨isArithVar_projLine, fun j => by fin_cases j; exact isSmoothHerm_fsLine 2⟩

end

end GroundTheory.Heights₂.Heights.Inter
