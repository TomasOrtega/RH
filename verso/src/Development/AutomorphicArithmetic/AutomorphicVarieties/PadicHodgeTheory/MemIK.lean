import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Introduce `l _ K g`. Use `⟨fun hg => (Subgroup.closure_le ((MaximalUnramifiedExtension l).fixingSubgroup.comap (GK K).subtype)).2 (fun σ hσ => ?_) hg, fun hg => Subgroup.subset_closure (GlobalTheory.FrobGen.norm_sub_lt hg)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(σ : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup`. Rewrite using `[← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]`. Introduce and unpack `x ⟨n, hn, hln, hx⟩`.

Establish `key : (σ : GQ l) x = x` using `GlobalTheory.Pst.eq_of_pow_eq_one_of_norm_sub_lt hln (by rw [← map_pow, hx, map_one]) hx (hσ x (GlobalTheory.Pst.norm_eq_one_of_pow_eq_one hn hx).le)`. Introduce and unpack `⟨_, n, rfl⟩`. Conclude with `MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy _ (σ : GQ l) from key) n`.
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
