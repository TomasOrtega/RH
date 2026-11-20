import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace Katz
namespace WittHaus

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (ha' : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have h1 := constantCoeff_subst_eq_zero ha ha' (f := f - C (constantCoeff f)) (by simp)
  have h2 : subst a (C (constantCoeff f) : MvPowerSeries σ R) = C (constantCoeff f) := by
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes (constantCoeff f)
  rw [← coe_substAlgHom ha, map_sub, coe_substAlgHom ha, h2, map_sub, constantCoeff_C] at h1
  exact sub_eq_zero.mp h1

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isUnit_natCast_of_not_dvd (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (u : ℕ)
    (hu : ¬ p ∣ u) : IsUnit (u : WittVector p k) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  intro h0
  have : (WittVector.constantCoeff (u : WittVector p k)) = 0 := h0
  rw [map_natCast, CharP.cast_eq_zero_iff k p] at this
  exact hu this

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem constantCoeff_int (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) {f : MvPowerSeries (Fin d) (Fr p k)}
    (hf : f ∈ quasiLog p h) :
    ∃ w : WittVector p k, coeff 0 f = algebraMap _ (Fr p k) w := by
  obtain ⟨w, hw⟩ := hf.2 0
  have hμ : HasSubst (fun i => lift p (μ i)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift p (h.const i)
  have hX : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hc : coeff 0 (cob1 (fun i => lift p (μ i)) f) = - coeff 0 f := by
    simp only [coeff_zero_eq_constantCoeff_apply]
    unfold cob1 inL inR
    rw [map_sub, map_sub, constantCoeff_subst_of_zero' hμ (fun i => constantCoeff_lift p (h.const i)),
      constantCoeff_subst_of_zero' hX (fun _ => constantCoeff_X _),
      constantCoeff_subst_of_zero' hY (fun _ => constantCoeff_X _)]
    ring
  refine ⟨-(1 * w), ?_⟩
  rw [map_neg, ← hw, hc, neg_neg]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Proceed by induction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Proceed by induction. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem haus : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ),
    IsHausdorff (Ideal.span {(p : WittVector p k)}) (Mod p h) := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun x hx => ?_⟩
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  have key : ∀ n : ℕ, ∃ g : quasiLog p h,
      (f : MvPowerSeries (Fin d) (Fr p k)) - ((p : WittVector p k) ^ n) • (g : MvPowerSeries (Fin d) (Fr p k))
        ∈ intBy p k (Fin d) 1 := by
    intro n
    have h1 := (SModEq.sub_mem.mp (hx n))
    rw [sub_zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨b, -, hb⟩ := h1
    induction b using Submodule.Quotient.induction_on with | _ g => ?_
    refine ⟨g, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero] at hb
    rw [Submodule.submoduleOf, Submodule.mem_comap] at hb
    have := neg_mem hb
    simpa [neg_sub] using this
  rw [Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  intro α
  by_cases hα : α = 0
  · subst hα
    obtain ⟨w, hw⟩ := constantCoeff_int p h f.2
    exact ⟨w, by rw [one_mul]; exact hw⟩
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra! hc
    exact hα (Finsupp.ext hc)
  obtain ⟨v, u, hu, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p (Nat.Prime.ne_one Fact.out)
  obtain ⟨g, hg⟩ := key v
  obtain ⟨w₁, hw₁⟩ := hg α
  obtain ⟨w₂, hw₂⟩ := g.2.1 α i
  obtain ⟨U, hU⟩ := isUnit_natCast_of_not_dvd p k u hu
  refine ⟨w₁ + ↑U⁻¹ * w₂, ?_⟩
  have hsm : coeff α (((p : WittVector p k) ^ v) • (g : MvPowerSeries (Fin d) (Fr p k))) =
      algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)) := by
    rw [← algebraMap_smul (Fr p k), LinearMap.map_smul, smul_eq_mul]
  have hα' : ((α i : ℕ) : Fr p k) = algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * algebraMap _ (Fr p k) (U : WittVector p k) := by
    rw [hU, ← map_mul, hm]; push_cast; rfl
  rw [map_sub, hsm] at hw₁
  have e2 : algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)) =
      algebraMap _ (Fr p k) (↑U⁻¹ * w₂) := by
    rw [map_mul, ← hw₂, hα']
    have : algebraMap _ (Fr p k) (↑U⁻¹ : WittVector p k) * algebraMap _ (Fr p k) (U : WittVector p k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap _ (Fr p k) ((p : WittVector p k) ^ v) * coeff α (g : MvPowerSeries (Fin d) (Fr p k)))) * this
  rw [one_mul, map_add, ← e2]
  rw [one_mul] at hw₁
  linear_combination hw₁

end WittHaus
end Katz
end GlobalTheory
