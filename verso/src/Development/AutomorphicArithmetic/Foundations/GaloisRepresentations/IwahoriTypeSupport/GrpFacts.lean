import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem unitRes_surj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Function.Surjective (unitRes k) := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TypesAndIwahori.grpFacts :
    UpperTheory.Gal.TypesAndIwahori.GrpFacts := by
  intro k _ _ _ _ s θ μ hθ hμ a b hab
  have key : (∀ u, θ a (unitRes k u) = θ b (unitRes k u)) → False := by
    intro h
    apply hab
    apply hθ
    refine MonoidHom.ext fun w => ?_
    obtain ⟨u, rfl⟩ := unitRes_surj k w
    exact h u
  have hres : ∀ c u, UpperTheory.TNZ.res (μ c) u = θ c (unitRes k u) := fun c u => hμ c u
  have hdiv : ∀ u, UpperTheory.TNZ.res (μ a / μ b) u = θ a (unitRes k u) / θ b (unitRes k u) := by
    intro u
    show (μ a / μ b) (unitIncl k u) = _
    rw [MonoidHom.div_apply, hμ a u, hμ b u]
  refine ⟨fun h => key fun u => ?_, ?_⟩
  · rw [← hres, ← hres, h]
  · unfold UpperTheory.TNZ.cc UpperTheory.TNZ.cond
    set S := {c : ℕ | ∀ u : (𝒪[k])ˣ, (u : 𝒪[k]) - 1 ∈ 𝓂[k] ^ c → UpperTheory.TNZ.res (μ a / μ b) u = 1} with hS
    have h1 : 1 ∈ S := by
      intro u hu
      rw [pow_one] at hu
      have hr : unitRes k u = 1 := by
        ext
        simp only [unitRes, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
        have hz : IsLocalRing.residue 𝒪[k] ((u : 𝒪[k]) - 1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hu
        rw [map_sub, map_one, sub_eq_zero] at hz
        exact hz
      rw [hdiv, hr, map_one, map_one, div_one]
    have h0 : 0 ∉ S := by
      intro h
      apply key
      intro u
      have := h u (by simp)
      rw [hdiv, div_eq_one] at this
      exact this
    apply le_antisymm (Nat.sInf_le h1)
    rw [Nat.one_le_iff_ne_zero]
    intro hz
    rcases Nat.sInf_eq_zero.1 hz with h | h
    · exact h0 h
    · rw [h] at h1
      exact h1
