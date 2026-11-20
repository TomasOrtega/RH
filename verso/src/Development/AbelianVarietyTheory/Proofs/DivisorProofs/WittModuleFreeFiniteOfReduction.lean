import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WittFrobeniusPowEqOne
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Consider separately whether the proposition holds or fails. Prove the first alternative. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem wittModule_free_finite_of_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [AddCommGroup V] [Module k V] [Module.Finite k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), IsHausdorff (Ideal.span {(p : WittVector p k)}) M → (∀ m : M, (p : WittVector p k) • m = 0 → m = 0) → Function.Surjective r → (∀ m, r m = 0 → ∃ n, m = p • n) → Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M := by
  intro p _ k _ _ _ M V _ _ _ _ _ r hH htf hr hker
  classical
  let I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hpow : ∀ (j : ℕ) (m : M), ((p : WittVector p k) ^ j) • m = 0 → m = 0 := by
    intro j
    induction j with
    | zero => intro m h; simpa using h
    | succ j ih =>
      intro m h
      rw [pow_succ, mul_smul] at h
      exact htf m (ih _ h)
  haveI : Module.IsTorsionFree (WittVector p k) M :=
    Module.IsTorsionFree.of_smul_eq_zero fun a m h => by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      obtain ⟨j, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
      rw [mul_smul] at h
      have h1 := hpow j _ h
      rw [← Units.smul_def] at h1
      exact (smul_eq_zero_iff_eq u).mp h1
  haveI : IsHausdorff I M := hH
  let b := Module.finBasis k V
  choose m hm using fun i => hr (b i)
  let F : (Fin (Module.finrank k V) → WittVector p k) →ₗ[WittVector p k] M :=
    Fintype.linearCombination (WittVector p k) m
  haveI : IsPrecomplete I (Fin (Module.finrank k V) → WittVector p k) :=
    GlobalTheory.isPrecomplete_pi I _
  have hs : Function.Surjective F := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨fun i => WittVector.teichmuller p (b.repr (r x) i), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h0 : r (F (fun i => WittVector.teichmuller p (b.repr (r x) i)) - x) = 0 := by
      rw [map_sub, Fintype.linearCombination_apply, map_sum]
      simp only [map_smulₛₗ, hm, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rw [sub_eq_zero]
      exact b.sum_repr (r x)
    obtain ⟨y, hy⟩ := hker _ h0
    rw [hy]
    have : ((p : WittVector p k)) • y ∈ (I • ⊤ : Submodule (WittVector p k) M) :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    simpa [Nat.cast_smul_eq_nsmul] using this
  haveI : Module.Finite (WittVector p k) M := Module.Finite.of_surjective F hs
  exact ⟨Module.free_of_finite_type_torsion_free', inferInstance⟩

end GlobalTheory
