import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensIdxE

noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing IdxHW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Substitute using the available equality. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem idxH_holds : IdxH := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  subst hd
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let u : Fin 2 → F := fun k => b.repr 1 k
  have hC1 : Cmat b σ ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := sigma_ne_id σ hCM
    apply hx
    have hb : ∀ l, σ (b l) = b l := fun l => by
      apply b.repr.injective
      ext k
      have := congrFun (congrFun h k) l
      simp only [Cmat] at this
      rw [this, b.repr_self, Matrix.one_apply, Finsupp.single_apply]
      by_cases hkl : k = l
      · subst hkl; simp
      · simp [hkl, Ne.symm hkl]
    have : σ.toLinearMap = LinearMap.id := b.ext fun l => by simp [hb l]
    exact congrArg (fun f : E →ₗ[F] E => f x) this
  have hu : u ≠ 0 := by
    intro h
    apply one_ne_zero (α := E)
    apply b.repr.injective
    ext k
    simpa [u] using congrFun h k
  have hCu : Matrix.mulVec (Cmat b σ) u = u := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Cmat, u]
    have h1 : σ 1 = 1 := map_one σ
    have h2 : (1 : E) = ∑ l, b.repr 1 l • b l := (b.sum_repr 1).symm
    have h3 : σ 1 = ∑ l, b.repr 1 l • σ (b l) := by
      rw [show σ 1 = σ (∑ l, b.repr 1 l • b l) from by rw [b.sum_repr], map_sum]
      exact Finset.sum_congr rfl fun l _ => σ.toLinearMap.map_smul _ _
    have := congrArg (fun y => b.repr y k) h3
    simp only [h1, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  obtain ⟨k0, k1, hk, hk0, ρ, hfix⟩ := fix2 (Cmat b σ) hC1 u hu hCu
  filter_upwards [eventually_all.2 fun k => eventually_all.2 fun l => eventually_int (Cmat b σ k l),
    eventually_all.2 fun k => eventually_int (u k / u k0), eventually_int ρ] with v hC hu' hρ
  unfold AddSubgroup.relIndex
  rw [comap_eq b v σ a k0 k1 hk ρ hC hρ (fun x hx => hfix (Fv F v) x hx),
    AddSubgroup.index_comap_of_surjective _ (psi_surj b v σ a k0 hσ hC hu' hk0),
    AddSubgroup.index_pi]
  simp only [index_max, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  ring

end PI.VolStabW
