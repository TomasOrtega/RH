import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StBaseRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWWArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem BaseRatioBasis.proof : BaseRatioBasis.Statement := by
  classical
  intro Ω _ _ ι _ x D hD

  obtain ⟨i₀, hi₀⟩ := hD.2.1.2.2 ()
  have hx : x i₀ ≠ 0 := by
    intro h0
    apply hi₀
    simp [T.baseIdeal, T.multiConeMap, h0]

  set S : Set Ω := Set.range fun j => x j / x i₀ with hS
  obtain ⟨u, -, hu⟩ := exists_maximal_algebraicIndependent (R := ℚ) (∅ : Set Ω) S (Set.empty_subset _)
    ((algebraicIndependent_empty_iff ℚ Ω).mpr (algebraMap ℚ Ω).injective)
  have huS : u ⊆ S := hu.prop.2
  have huI : AlgebraicIndepOn ℚ id u := hu.prop.1
  have hfin : u.Finite := (Set.finite_range _).subset huS
  have : Fintype u := hfin.fintype
  set d := Fintype.card u
  let e : u ≃ Fin d := Fintype.equivFin u
  let t : Fin d → Ω := fun n => (e.symm n : Ω)
  have hrange : Set.range t = u := by
    ext a
    constructor
    · rintro ⟨n, rfl⟩
      exact (e.symm n).2
    · intro ha
      exact ⟨e ⟨a, ha⟩, by simp [t]⟩
  have ht : AlgebraicIndependent ℚ t := huI.comp e.symm e.symm.injective
  have htS : ∀ n, t n ∈ IntermediateField.adjoin ℚ S := fun n =>
    IntermediateField.subset_adjoin ℚ S (huS (e.symm n).2)
  have halg : ∀ r ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r := by
    intro r hr
    rw [hrange]
    by_cases hru : r ∈ u
    · exact isAlgebraic_algebraMap
        (⟨r, IntermediateField.subset_adjoin ℚ u hru⟩ : IntermediateField.adjoin ℚ u)
    · refine IntermediateField.isAlgebraic_adjoin_iff.mpr ?_
      by_contra hT
      have hins : AlgebraicIndepOn ℚ id (insert r u) :=
        (AlgebraicIndepOn.insert_iff hru).mpr ⟨huI, by rw [Set.image_id]; exact hT⟩
      exact hru (hu.mem_of_prop_insert ⟨hins, Set.insert_subset hr huS⟩)

  have hcone : coneRatios (fun p : (Σ _ : Unit, ι) => x p.2) (fun _ => i₀) = S := by
    ext a
    constructor
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(), j⟩, rfl⟩
  have hA := CoordConeArithVar.full Unit (fun _ => ι) Ω (fun p => x p.2) (fun _ => i₀) d t ⟨()⟩
    (fun _ => hx) ht (by rw [hcone]; exact htS) (by rw [hcone]; exact halg)
  rw [mCoordIdeal_eq_ker_multiConeMap] at hA
  have hdim := hD.2.2.2.symm.trans hA.2.2.2
  simp only [Fintype.card_unit] at hdim
  have hDd : D + 1 = d + 1 + 1 := by exact_mod_cast hdim
  refine ⟨i₀, d, t, hx, by omega, ht, htS, fun j => halg _ ⟨j, rfl⟩⟩

end

end GroundTheory.Heights₂.Heights.Inter
