import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMLatticeDiscrete

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem cmLattice_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) → DiscreteTopology Λ := by
  intro E _ _ _ I _ φ hφ n e L hL Λ hΛ
  obtain ⟨N, hNpos, hN⟩ := hL

  have hfin : {w : Fin n → ℂ | w ∈ Λ ∧ ‖w‖ ≤ 1}.Finite := by
    have hS := NumberField.Embeddings.finite_of_norm_le E ℂ ((N : ℝ) * 1)
    have hT : {x : E | x ∈ L ∧ ∀ i, ‖φ i x‖ ≤ 1}.Finite := by
      refine (hS.image (fun y : E ↦ y / (N : E))).subset ?_
      rintro x ⟨hxL, hxb⟩
      refine ⟨(N : E) * x, ⟨hN x hxL, fun σ ↦ ?_⟩, ?_⟩
      · obtain ⟨i, hi, -⟩ := hφ σ
        have hb : ‖σ x‖ ≤ 1 := by
          rcases hi with h | h
          · rw [h]; exact hxb i
          · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact hxb i
        rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)
      · have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
        simp only
        field_simp
    refine (hT.image (fun x : E ↦ fun j ↦ φ (e j) x)).subset ?_
    rintro w ⟨hwΛ, hwb⟩
    obtain ⟨x, hxL, rfl⟩ := (hΛ w).1 hwΛ
    refine ⟨x, ⟨hxL, fun i ↦ ?_⟩, rfl⟩
    have := norm_le_pi_norm (fun j ↦ φ (e j) x) (e.symm i)
    simp only [Equiv.apply_symm_apply] at this
    exact this.trans hwb
  apply discreteTopology_of_isOpen_singleton_zero
  set F : Set (Fin n → ℂ) := {w | w ∈ Λ ∧ ‖w‖ ≤ 1} \ {0}
  have hF : IsClosed F := (hfin.subset Set.diff_subset).isClosed
  have hU : IsOpen (Metric.ball (0 : Fin n → ℂ) 1 ∩ Fᶜ) := Metric.isOpen_ball.inter hF.isOpen_compl
  convert hU.preimage continuous_subtype_val using 1
  ext ⟨w, hw⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_compl_iff, F, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
  constructor
  · intro h
    have h0 : w = 0 := by simpa using congrArg Subtype.val h
    subst h0
    simp
  · rintro ⟨h1, h2⟩
    have : w = 0 := h2 ⟨hw, h1.le⟩
    exact Subtype.ext this

end GlobalTheory.CMLatticeDiscrete
