import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Establish `ht0 : Ideal.absNorm (𝔭 ^ k) ≠ 0`. Rewrite using `[ne_eq, Ideal.absNorm_eq_zero_iff]`. Conclude with `pow_ne_zero _ hne`. Establish `htm : ((Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k` using `Ideal.absNorm_mem _`.

Take `⟨N, hN⟩` from `exists_nat_gt (∑ φ : K →+* ℂ, ‖φ (algebraMap F K (a : F))‖)`. Establish `hz : ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k`. Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_left _ _ htm`. Establish `hzF : (((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) = ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : F)`.

Simplify using the standard rewrite rules. Use `⟨(((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) - (a : F), ?_, ?_⟩` and prove the remaining obligations. Introduce `φ`. Rewrite using `[hzF, map_sub, map_sub, map_natCast, map_natCast, Complex.sub_re, Complex.natCast_re]`. Establish `h1 : (φ (algebraMap F K (a : F))).re ≤ ∑ ψ : K →+* ℂ, ‖ψ (algebraMap F K (a : F))‖` using `(Complex.re_le_norm _).trans (Finset.single_le_sum (f := fun ψ : K →+* ℂ => ‖ψ (algebraMap F K (a : F))‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ))`.

Establish `h2 : (N : ℝ) ≤ ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : ℝ)`. Use `push_cast`. Conclude with `le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht0)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[add_sub_cancel]`.

Conclude with `inP_of_mem_pow hz`.
-/
theorem exists_totPos_congr {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hne : 𝔭 ≠ ⊥) (a : 𝓞 F) (k : ℕ) :
    ∃ x : F, TotPos (algebraMap F K x) ∧ InP 𝔭 k (algebraMap F K ((a : F) + x)) := by
  have := h𝔭.isPrime
  have ht0 : Ideal.absNorm (𝔭 ^ k) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact pow_ne_zero _ hne
  have htm : ((Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := Ideal.absNorm_mem _
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ φ : K →+* ℂ, ‖φ (algebraMap F K (a : F))‖)
  have hz : ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ htm
  have hzF : (((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) = ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : F) := by
    simp
  refine ⟨(((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) - (a : F), ?_, ?_⟩
  · intro φ
    rw [hzF, map_sub, map_sub, map_natCast, map_natCast, Complex.sub_re, Complex.natCast_re]
    have h1 : (φ (algebraMap F K (a : F))).re ≤ ∑ ψ : K →+* ℂ, ‖ψ (algebraMap F K (a : F))‖ :=
      (Complex.re_le_norm _).trans (Finset.single_le_sum
        (f := fun ψ : K →+* ℂ => ‖ψ (algebraMap F K (a : F))‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ φ))
    have h2 : (N : ℝ) ≤ ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_right (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht0)
    linarith
  · rw [add_sub_cancel]
    exact inP_of_mem_pow hz

end Formalism.L2.SG.Pf.GluingBases
