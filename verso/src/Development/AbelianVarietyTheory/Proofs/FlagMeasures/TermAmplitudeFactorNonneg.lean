import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hb : 0 < large₂.sc.b` using `Real.exp_pos _`. Establish `hS : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ` using `le_trans zero_le_one (one_le_sigma_product _ j δ)`. Unfold `k2a`. Use `mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _) (Real.rpow_nonneg (minor_norm_nonneg j δ) _)) (Real.rpow_nonneg ?_ _)) (Real.rpow_nonneg hS _)` and prove the remaining obligations. Unfold `Formalism.MainNotions.S.Cnt.Hb`.

Conclude with `Real.rpow_nonneg hb.le _`.
-/
theorem termAmplitudeFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Cs C : ℝ) (hC : 0 ≤ C) (j : ℕ) (δ : ℕ → D.host.E) :
    0 ≤ k2a large₂ CH Cs C j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hS : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := le_trans zero_le_one (one_le_sigma_product _ j δ)
  unfold k2a
  refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _)
    (Real.rpow_nonneg (minor_norm_nonneg j δ) _)) (Real.rpow_nonneg ?_ _)) (Real.rpow_nonneg hS _)
  unfold Formalism.MainNotions.S.Cnt.Hb
  exact Real.rpow_nonneg hb.le _

/- English proof (translation)
Introduce `hAmp hPairs Cg cb Cw cT CT C0 hcb hcT`. Take `⟨CH, hCH, hA⟩` from `hAmp Cg cb Cw cT CT C0 hcb hcT`. Take `⟨Ch, Cp, hCh, hCp, C'₁, Cl₁, hP⟩` from `hPairs Cg cb Cw cT CT C0 CH hCH`. Use `⟨CH, Ch, Cp, hCH, hCh, hCp, fun Cs hCs => ?_⟩` and prove the remaining obligations. Take `⟨C₀, hC₀, hA2⟩` from `hA Cs (by linarith)`.

Use `⟨C₀, fun C hC => ?_⟩` and prove the remaining obligations. Take `⟨C'₂, Cl₂, hA3⟩` from `hA2 C hC`. Use `⟨max C'₁ C'₂, max Cl₁ Cl₂, fun C' Cl hC' hCl D large₂ X Y u hTies hK hConc => ?_⟩` and prove the remaining obligations. Establish `amp` using `hA3 C' Cl (le_of_max_le_right hC') (le_of_max_le_right hCl) D large₂ X Y u hTies hK hConc`. Establish `pairs` using `hP C' Cl (le_of_max_le_left hC') (le_of_max_le_left hCl) D large₂ X Y u hK hConc`.

Introduce `j' hj' j'' hj'' δ' δ'' S hS`. Establish `hC0 : 0 ≤ C` using `le_trans hC₀ hC`. Establish `hdpi : 0 ≤ dpiC X u` using `Nat.cast_nonneg _`. Establish `hsq : Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u) = dpiC X u` using `Real.mul_self_sqrt hdpi`. Establish `ha'` using `termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j' δ'`.

Establish `ha''` using `termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j'' δ''`. Establish `hK0 : 0 ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'')` using `mul_nonneg hdpi (mul_nonneg ha' ha'')`. Establish `hterm : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') * ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2))`. Introduce `p hp`. Take `⟨hmem, hj1, hj2, hl1, hl2⟩` from `hS p hp`.

Establish `h1` using `amp p.1 hmem.1`. Establish `h2` using `amp p.2 hmem.2.1`. Rewrite `h1` using `[hj1, hl1]`. Rewrite `h2` using `[hj2, hl2]`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `_ ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') * (massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')) := mul_le_mul_of_nonneg_left (pairs j' hj' j'' hj'' δ' δ'' S hS) hK0`. Use `_ = _ := by ring`.
-/
theorem typeBound_of_amplitude_pairs : AmpP → PairsP → TypeP := by
  intro hAmp hPairs Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hA⟩ := hAmp Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Ch, Cp, hCh, hCp, C'₁, Cl₁, hP⟩ := hPairs Cg cb Cw cT CT C0 CH hCH
  refine ⟨CH, Ch, Cp, hCH, hCh, hCp, fun Cs hCs => ?_⟩
  obtain ⟨C₀, hC₀, hA2⟩ := hA Cs (by linarith)
  refine ⟨C₀, fun C hC => ?_⟩
  obtain ⟨C'₂, Cl₂, hA3⟩ := hA2 C hC
  refine ⟨max C'₁ C'₂, max Cl₁ Cl₂, fun C' Cl hC' hCl D large₂ X Y u hTies hK hConc => ?_⟩
  have amp := hA3 C' Cl (le_of_max_le_right hC') (le_of_max_le_right hCl) D large₂ X Y u hTies hK hConc
  have pairs := hP C' Cl (le_of_max_le_left hC') (le_of_max_le_left hCl) D large₂ X Y u hK hConc
  intro j' hj' j'' hj'' δ' δ'' S hS
  have hC0 : 0 ≤ C := le_trans hC₀ hC
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hsq : Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u) = dpiC X u := Real.mul_self_sqrt hdpi
  have ha' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j' δ'
  have ha'' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j'' δ''
  have hK0 : 0 ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') :=
    mul_nonneg hdpi (mul_nonneg ha' ha'')
  have hterm : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
    intro p hp
    obtain ⟨hmem, hj1, hj2, hl1, hl2⟩ := hS p hp
    have h1 := amp p.1 hmem.1
    have h2 := amp p.2 hmem.2.1
    rw [hj1, hl1] at h1
    rw [hj2, hl2] at h2
    calc ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
        ≤ (Formalism.L2.SG.TermOp.wt p.1 * Real.sqrt (dpiC X u) * (omT p.1 * k2a large₂ CH Cs C j' δ')) *
          (Formalism.L2.SG.TermOp.wt p.2 * Real.sqrt (dpiC X u) * (omT p.2 * k2a large₂ CH Cs C j'' δ'')) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = (Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u)) * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
          ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by ring
      _ = _ := by rw [hsq]
  calc ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
      ≤ ∑ p ∈ S, dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := Finset.sum_le_sum hterm
    _ = dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ∑ p ∈ S, ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
      rw [Finset.mul_sum]
    _ ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        (massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')) :=
      mul_le_mul_of_nonneg_left (pairs j' hj' j'' hj'' δ' δ'' S hS) hK0
    _ = _ := by ring

end GlobalTheory.TypeAsm
