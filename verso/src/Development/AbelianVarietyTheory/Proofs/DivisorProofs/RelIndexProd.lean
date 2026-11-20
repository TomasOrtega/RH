import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.LevOpTmul

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem finite_supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport f) := hf
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : G => (fun y : G => x⁻¹ * y) ⁻¹' (K : Set G))
    (fun x => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun x : G => (x : G ⧸ K))).subset ?_
  intro q hq
  have hmem : q.out ∈ tsupport f := subset_tsupport f hq
  obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (ht hmem)
  refine ⟨x, hx, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  exact QuotientGroup.eq.2 hqx

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem levOp_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K₁ : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (S : Finset (G ⧸ K₁)) (hS : ∀ q : G ⧸ K₁, f q.out ≠ 0 → q ∈ S)
    (v : V) : levOp ρ K K₁ f A v = ((K₁.relIndex K : ℕ) : ℂ)⁻¹ • ∑ q ∈ S, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  · intro q hq
    rw [Function.mem_support] at hq
    apply hS
    intro h0
    apply hq
    rw [h0, zero_smul]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem term_mk {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K₁ : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K₁, ∀ x, f (x * k) = f x) (w : V) (hw : ∀ k ∈ K₁, ρ k w = w) (g : G) :
    f (g : G ⧸ K₁).out = f g ∧ ρ (g : G ⧸ K₁).out w = ρ g w := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
  rw [hk]
  exact ⟨hf k k.2 g, by rw [map_mul, Module.End.mul_apply, hw k k.2]⟩

end GlobalTheory.BCT.LevOpTmul
