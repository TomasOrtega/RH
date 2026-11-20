import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMLatticeDiscrete

/- English proof (translation)
Introduce `E _ _ _ I _ φ hφ n e L hL Λ hΛ`. Take `⟨N, hNpos, hN⟩` from `hL`. Establish `hfin : {w : Fin n → ℂ | w ∈ Λ ∧ ‖w‖ ≤ 1}.Finite`. Establish `hS` using `NumberField.Embeddings.finite_of_norm_le E ℂ ((N : ℝ) * 1)`. Establish `hT : {x : E | x ∈ L ∧ ∀ i, ‖φ i x‖ ≤ 1}.Finite`.

Use `(hS.image (fun y : E ↦ y / (N : E))).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hxL, hxb⟩`. Use `⟨(N : E) * x, ⟨hN x hxL, fun σ ↦ ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨i, hi, -⟩` from `hφ σ`. Establish `hb : ‖σ x‖ ≤ 1`.

Break down `hi with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hxb i`. Rewrite using `[h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]`. Conclude with `hxb i`.

Rewrite using `[map_mul, map_natCast, norm_mul, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)`. Establish `hN0 : (N : E) ≠ 0` using `Nat.cast_ne_zero.mpr hNpos.ne'`. Simplify using `only`. Clear the denominators using the available nonvanishing facts.

Use `(hT.image (fun x : E ↦ fun j ↦ φ (e j) x)).subset ?_` and prove the remaining obligations. Introduce and unpack `w ⟨hwΛ, hwb⟩`. Take `⟨x, hxL, rfl⟩` from `(hΛ w).1 hwΛ`. Use `⟨x, ⟨hxL, fun i ↦ ?_⟩, rfl⟩` and prove the remaining obligations. Use `norm_le_pi_norm (fun j ↦ φ (e j) x) (e.symm i)` as an intermediate fact.

Simplify using `only [Equiv.apply_symm_apply] at this`. Conclude with `this.trans hwb`. Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Use `set F : Set (Fin n → ℂ) := {w | w ∈ Λ ∧ ‖w‖ ≤ 1} \ {0}`. Establish `hF : IsClosed F` using `(hfin.subset Set.diff_subset).isClosed`.

Establish `hU : IsOpen (Metric.ball (0 : Fin n → ℂ) 1 ∩ Fᶜ)` using `Metric.isOpen_ball.inter hF.isOpen_compl`. Use `hU.preimage continuous_subtype_val using 1` and compare the differences between its conclusion and the goal. Use extensionality with `⟨w, hw⟩`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, Set.mem_compl_iff, F, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h0 : w = 0` using `by simpa using congrArg Subtype.val h`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Introduce and unpack `⟨h1, h2⟩`.

Establish `: w = 0` using `h2 ⟨hw, h1.le⟩`. Conclude with `Subtype.ext this`.
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
