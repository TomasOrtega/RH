import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize Formalism.MainNotions.WeightAlgebra

/- English proof (translation)
Introduce `eps Fm hP hCP`. Use `⟨max ((10 : ℝ) ^ 60) (Fm.CP ^ 20), ?_⟩` and prove the remaining obligations. Introduce `x hx hx₁ i`. Establish `hS : SizesAt (Fm.L x i)` using `Fm.sizes x hx i`. Establish `hLx : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx`.

Establish `hCnW : (Fm.params x hx i).CnW = 10` using `(Fm.fixed.2.2.2.2.2.2.2 x hx i).1`. Establish `hg : ∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1`. Introduce `k`. Establish `hpr` using `(Fm.D x i).host.g_prime k`. Establish `hpos : (0 : ℝ) < ((Fm.D x i).host.g k : ℝ)` using `by exact_mod_cast hpr.pos`.

Establish `hle` using `(hP.2.2.2.2.2.2.2.2 x hx i).2.2.1 k`. Use `(Real.log_le_iff_le_exp hpos).2 hle` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h60 : (10 : ℝ) ^ 60 ≤ (Fm.L x i).sc.x`. Rewrite using `[hLx]`.

Conclude with `le_trans (le_max_left _ _) hx₁`. Take `⟨hH, hF⟩` from `hostSz_of_sizes (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) hS hg h60`. Establish `hCPeq : (Fm.parT x hx i).CP = Fm.CP`. Unfold `FamP.CP`. Rewrite using `[← Fm.parT_K x hx i]`.

Both sides reduce to the same expression. Establish `hL4 : (4 : ℝ) ≤ (Fm.L x i).sc.L` using `hH.len`. Establish `hf : (1 : ℝ) ≤ (Fm.D x i).R.f`. Establish `hK` using `hS.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1`. Break down `Nat.eq_zero_or_pos (Fm.D x i).R.f with h0 | hpos` into its components or cases.

It suffices to derive a contradiction. Rewrite `hK` using `[h0, Nat.cast_zero, zero_mul]`. Establish `hxpos : 0 < (Fm.L x i).sc.x ^ szTh (Fm.L x i)` using `Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _`. Use `mul_pos hxpos (by linarith : (0 : ℝ) < (Fm.L x i).sc.L)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hpos` after adjusting the coercions. Use `⟨hS, hCnW, hg, ?_, ?_, (Fm.ex x hx i).kap_def, ⟨(Fm.ex x hx i).errX⟩, hLx, ?_⟩` and prove the remaining obligations. Rewrite using `[hCPeq]`. Conclude with `hCP`. Unfold `zBase`.

Rewrite using `[hCPeq]`. Establish `hr : x ≤ ((Fm.D x i).R.r : ℝ)`. Establish `h` using `scale_le_rank hS`. Rewrite `h` using `[hLx]`. Conclude with `h`.

Establish `hr0 : (0 : ℝ) ≤ ((Fm.D x i).R.r : ℝ)` using `Nat.cast_nonneg _`. Establish `h1 : ((Fm.D x i).R.r : ℝ) ≤ (Fm.D x i).R.f * (Fm.D x i).R.r` using `le_mul_of_one_le_left hr0 hf`. Establish `h2 : ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r ≤ (Fm.D x i).R.f * (Fm.D x i).R.r * (Fm.L x i).sc.L` using `le_mul_of_one_le_right (by positivity) (by linarith)`. Combine the linear relations using `[le_trans (le_max_right _ _) hx₁]`. Introduce `hJ`.

Conclude with `hF (hJ.2.2.2.2 _ hH)`.
-/
theorem rows_of_pageFix : ∀ (eps : ℝ) (Fm : FamP eps), DC.PageFix Fm → 1000 ≤ Fm.CP → ∃ x₁ : ℝ, ∀ x (hx : Fm.x1 < x), x₁ ≤ x → ∀ i : Fm.Ix x, SizesAt (Fm.L x i) ∧ (Fm.params x hx i).CnW = 10 ∧ (∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1) ∧ 1000 ≤ (Fm.parT x hx i).CP ∧ (Fm.parT x hx i).CP ^ 20 ≤ zBase (Fm.L x i) ∧ DV.KapDef (Fm.D x i) ∧ Nonempty (ErrX (Fm.D x i)) ∧ (Fm.L x i).sc.x = x ∧ (JointQ (Fm.D x i) → FieldSmall (Fm.D x i) (Fm.L x i)) := by
  intro eps Fm hP hCP
  refine ⟨max ((10 : ℝ) ^ 60) (Fm.CP ^ 20), ?_⟩
  intro x hx hx₁ i
  have hS : SizesAt (Fm.L x i) := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hCnW : (Fm.params x hx i).CnW = 10 := (Fm.fixed.2.2.2.2.2.2.2 x hx i).1

  have hg : ∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1 := by
    intro k
    have hpr := (Fm.D x i).host.g_prime k
    have hpos : (0 : ℝ) < ((Fm.D x i).host.g k : ℝ) := by exact_mod_cast hpr.pos
    have hle := (hP.2.2.2.2.2.2.2.2 x hx i).2.2.1 k
    have := (Real.log_le_iff_le_exp hpos).2 hle
    linarith
  have h60 : (10 : ℝ) ^ 60 ≤ (Fm.L x i).sc.x := by
    rw [hLx]; exact le_trans (le_max_left _ _) hx₁
  obtain ⟨hH, hF⟩ := hostSz_of_sizes (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) hS hg h60

  have hCPeq : (Fm.parT x hx i).CP = Fm.CP := by
    unfold FamP.CP
    rw [← Fm.parT_K x hx i]
    rfl
  have hL4 : (4 : ℝ) ≤ (Fm.L x i).sc.L := hH.len

  have hf : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have hK := hS.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    rcases Nat.eq_zero_or_pos (Fm.D x i).R.f with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, zero_mul] at hK
      have hxpos : 0 < (Fm.L x i).sc.x ^ szTh (Fm.L x i) :=
        Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _
      have := mul_pos hxpos (by linarith : (0 : ℝ) < (Fm.L x i).sc.L)
      linarith
    · exact_mod_cast hpos
  refine ⟨hS, hCnW, hg, ?_, ?_, (Fm.ex x hx i).kap_def, ⟨(Fm.ex x hx i).errX⟩, hLx, ?_⟩
  · rw [hCPeq]; exact hCP
  ·
    unfold zBase
    rw [hCPeq]
    have hr : x ≤ ((Fm.D x i).R.r : ℝ) := by
      have h := scale_le_rank hS
      rw [hLx] at h
      exact h
    have hr0 : (0 : ℝ) ≤ ((Fm.D x i).R.r : ℝ) := Nat.cast_nonneg _
    have h1 : ((Fm.D x i).R.r : ℝ) ≤ (Fm.D x i).R.f * (Fm.D x i).R.r := le_mul_of_one_le_left hr0 hf
    have h2 : ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r ≤ (Fm.D x i).R.f * (Fm.D x i).R.r * (Fm.L x i).sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith [le_trans (le_max_right _ _) hx₁]
  · intro hJ
    exact hF (hJ.2.2.2.2 _ hH)

end GlobalTheory.FinalRows

end
