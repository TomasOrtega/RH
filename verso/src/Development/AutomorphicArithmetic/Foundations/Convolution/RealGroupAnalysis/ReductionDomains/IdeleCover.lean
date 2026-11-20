import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.AutomorphicForms.ReductionIdele

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ c hc`. Use `set ρ : IdeleGroup F := Reduction.posIdele (K := F) 2 two_pos with hρ`. Establish `hr : ab ρ = 2 ^ Module.finrank ℚ F` using `Reduction.ideleModule_posIdele (K := F) 2 two_pos`. Establish `h1 : 1 < ab ρ`. Rewrite using `[hr]`.

Conclude with `one_lt_pow₀ one_lt_two Module.finrank_pos.ne'`. Establish `hr0 : 0 < ab ρ` using `one_pos.trans h1`. Take `⟨S, hS, hSm⟩` from `Reduction.exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc (c * ab ρ)`. Use `⟨S, ρ, hS, h1, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hx : 1 ≤ ab a / c` using `(one_le_div hc).2 ha`.

Take `⟨n, hn1, hn2⟩` from `exists_nat_pow_near hx h1`. Establish `hp : 0 < ab ρ ^ n` using `pow_pos hr0 n`. Establish `hm : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ) = ab a / ab ρ ^ n`. Establish `: (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ) = ((IdeleGroup.ideleModule F ρ : ℝ) ^ n)⁻¹ * (IdeleGroup.ideleModule F a : ℝ)`. Simplify using `[map_mul, map_inv, map_pow]`.

Rewrite using `[this, div_eq_inv_mul]`. Both sides reduce to the same expression. Take `⟨t, ht⟩` from `hSm ((ρ ^ n)⁻¹ * a) (by`. Rewrite using `[hm, le_div_iff₀ hp]`. Use `(le_div_iff₀ hc).1 hn1` as an intermediate fact.

Use the proof step `linarith)`. Use the proof step `(by`. Rewrite using `[hm, div_le_iff₀ hp]`. Establish `h2` using `(div_lt_iff₀ hc).1 hn2`. Rewrite `h2` using `[pow_succ]`.

Use the proof step `nlinarith)`. Use `⟨t, n, _, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm, mul_inv_cancel_left]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.ideleCover :
    ∀ (F : Type) [Field F] [NumberField F] (c : ℝ), 0 < c → ∃ (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C ∧ 1 < ab ρ ∧ ∀ a : IdeleGroup F, c ≤ ab a → ∃ (t : Fˣ) (n : ℕ), ∃ x ∈ C, IdeleGroup.diagonal F t * a = ρ ^ n * x := by
  intro F _ _ c hc
  set ρ : IdeleGroup F := Reduction.posIdele (K := F) 2 two_pos with hρ
  have hr : ab ρ = 2 ^ Module.finrank ℚ F := Reduction.ideleModule_posIdele (K := F) 2 two_pos
  have h1 : 1 < ab ρ := by
    rw [hr]
    exact one_lt_pow₀ one_lt_two Module.finrank_pos.ne'
  have hr0 : 0 < ab ρ := one_pos.trans h1
  obtain ⟨S, hS, hSm⟩ := Reduction.exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc (c * ab ρ)
  refine ⟨S, ρ, hS, h1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx h1
  have hp : 0 < ab ρ ^ n := pow_pos hr0 n
  have hm : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ) = ab a / ab ρ ^ n := by
    have : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ)
        = ((IdeleGroup.ideleModule F ρ : ℝ) ^ n)⁻¹ * (IdeleGroup.ideleModule F a : ℝ) := by
      simp [map_mul, map_inv, map_pow]
    rw [this, div_eq_inv_mul]
    rfl
  obtain ⟨t, ht⟩ := hSm ((ρ ^ n)⁻¹ * a)
    (by
      rw [hm, le_div_iff₀ hp]
      have := (le_div_iff₀ hc).1 hn1
      linarith)
    (by
      rw [hm, div_le_iff₀ hp]
      have h2 := (div_lt_iff₀ hc).1 hn2
      rw [pow_succ] at h2
      nlinarith)
  refine ⟨t, n, _, ht, ?_⟩
  rw [mul_left_comm, mul_inv_cancel_left]
