import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Loc.memIK :
    ∀ {v : ℕ} [Fact v.Prime] (K : FinExt v) (g : ↥(GK K)), g ∈ IK K ↔ (g : GQ v) ∈ Iq v := by
  intro l _ K g
  refine ⟨fun hg => (Subgroup.closure_le ((MaximalUnramifiedExtension l).fixingSubgroup.comap (GK K).subtype)).2 (fun σ hσ => ?_) hg,
    fun hg => Subgroup.subset_closure (GlobalTheory.FrobGen.norm_sub_lt hg)⟩
  change (σ : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
  rintro x ⟨n, hn, hln, hx⟩
  have key : (σ : GQ l) x = x := GlobalTheory.Pst.eq_of_pow_eq_one_of_norm_sub_lt hln (by rw [← map_pow, hx, map_one]) hx
    (hσ x (GlobalTheory.Pst.norm_eq_one_of_pow_eq_one hn hx).le)
  rintro ⟨_, n, rfl⟩
  exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy _ (σ : GQ l) from key) n
