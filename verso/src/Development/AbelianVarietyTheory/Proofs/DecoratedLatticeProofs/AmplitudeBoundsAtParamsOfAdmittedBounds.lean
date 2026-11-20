import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypothesesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `Cg CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa0`. Use `set Cc : ℝ := CS + Cg + 2 with hCc`. Use `set K : ℝ := max CPT 0 + max Cc 0 + 6 with hK`. Use `set Ch : ℝ := max (max CDl 0) (max (CDl + 1) 0) with hChd`. Use `set Cm : ℝ := max (max K Ca) 2 with hCm`.

Use `set C : ℝ := max Cm (6 * Real.exp 1 * Real.pi * 1) with hCd`. Use `set C2 : ℝ := max (6 * C) (C ^ 2 + C * Ch) with hC2`. Establish `m1 : K ≤ Cm` using `le_trans (le_max_left _ _) (le_max_left _ _)`. Establish `m2 : Ca ≤ Cm` using `le_trans (le_max_right _ _) (le_max_left _ _)`. Establish `m3 : 2 ≤ Cm` using `le_max_right _ _`.

Establish `n1 : Cm ≤ C` using `le_max_left _ _`. Establish `n4 : 6 * Real.exp 1 * Real.pi * 1 ≤ C` using `le_max_right _ _`. Establish `hC0 : 0 ≤ C` using `by linarith`. Establish `hChA : max (CDl + 1) 0 ≤ Ch` using `le_max_right _ _`. Establish `hCh0 : 0 ≤ Ch` using `le_trans (le_max_right _ _) hChA`.

Establish `hChD : CDl ≤ Ch` using `le_trans (le_max_left _ _) (le_max_left _ _)`. Establish `h62 : 6 * C ≤ C2` using `le_max_left _ _`. Establish `h22 : C ^ 2 + C * Ch ≤ C2` using `le_max_right _ _`. Use `⟨C, C2, Ch, hC0, hCh0, fun Cpr δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨thr0, hthr0⟩` from `GlobalTheory.T.size_bounds_of_standingHypotheses (max (max (C + 6 * C * Ch) C) (max (1 / δ) hilbertNinetyConstant))`.

Use `⟨thr0, fun D large₂ C' Cl cb Cu cT CT C0 hC' hCl hG hA1 hA2 hA5 hA9 hDeg hAbs hA11 hA12 => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0`. Use `swap`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w w' zs zs' γs ps _ hH`.

Conclude with `absurd hH.1 hH0`. Introduce `w w' zs zs' γs ps _ hH`. Conclude with `absurd hH.1 hH0`. Introduce `τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH`. Conclude with `absurd hH.1 hH0`.

Take `⟨h1000, -, hMm, hMk, -, -, hrb, hm2k, -⟩` from `hthr0 D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1`. Establish `hM1 : C + 6 * C * Ch ≤ (D.R.m : ℝ)` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMm`. Establish `hMC : C ≤ (D.R.k : ℝ)` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMk`. Establish `hMd : 1 / δ ≤ (D.R.m : ℝ)` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMm`. Establish `hM9 : hilbertNinetyConstant ≤ (D.R.m : ℝ)` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMm`.

Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `hb : 1 ≤ large₂.sc.b` using `one_le_b large₂`. Establish `hS3 : VanishingOnXAndXPlusBranching.TowerRallisLemma D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch`. Use `heightStatement_of_bounds D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 h62 ?_` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.

Establish `hS5 : VanishingOnXAndXPlusBranching.GGFromIrreducibility D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch` using `product_clause_at_record D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 (by linarith) h22`. Establish `hCl1 : 1 / Cl ≤ 1` using `by rw [div_le_one (by linarith)]; linarith`. Establish `p1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 1 Cc` using `constant_clause_schur_weyl D large₂ C' Cl Cg cb Cu cT CT C0 1 CS Cc (by rw [hCc]; linarith) hA11 hA12`. Establish `hn : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2` using `by exact_mod_cast rank_eq_two_mul_add_two D`. Establish `hr0 : (0 : ℝ) ≤ D.R.rS` using `Nat.cast_nonneg _`. Establish `hδk : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k`. Establish `hmpos : (0 : ℝ) < D.R.m` using `by rw [hmr]; positivity`. Establish `e1 : 1 ≤ δ * (D.R.m : ℝ)`.

Rewrite `hMd` using `[div_le_iff₀ hδ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3 : (D.R.m : ℝ) ≤ δ * (D.R.m : ℝ) ^ 2`. Use `mul_le_mul_of_nonneg_right e1 hmpos.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `e4 : δ * (D.R.m : ℝ) ^ 2 ≤ δ * D.R.k` using `mul_le_mul_of_nonneg_left hm2k hδ.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `r1 : HilbertSchmidtBoundWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch` using `L2_decay_of_admissible D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CPT CDl Cc Cpr Cm Ch (le_max_right _ _) (le_max_left _ _) m1 hCh0 hChD hA1 hA2 p1`. Establish `r2 : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch` using `abs_decay_mono_constants D large₂ hCa0 m2 hChA (abs_decay_of_all_parameters D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CDl hilbertNinetyConstant Cpr Ca (max (CDl + 1) 0) (le_max_right _ _) (le_max_left _ _) hCa0 hilbertNinetyConstant_pos (le_max_right _ _) (le_max_left _ _) …`. Establish `q7 : VanishingOnXAndXPlusBranching.division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ` using `decayProp_of_l2AbsDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm C Ch δ m3 n1 hMC hδk n4 hA5 r1 r2`.

Conclude with `⟨hS3, hS5, q7⟩`.
-/
theorem ampAt_record_of_inputs :
    ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam →
      VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT →
      VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl →
      VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 →
      VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 →
      DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant →
      AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca →
      VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D →
      AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  intro Cg CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa0
  set Cc : ℝ := CS + Cg + 2 with hCc
  set K : ℝ := max CPT 0 + max Cc 0 + 6 with hK
  set Ch : ℝ := max (max CDl 0) (max (CDl + 1) 0) with hChd
  set Cm : ℝ := max (max K Ca) 2 with hCm
  set C : ℝ := max Cm (6 * Real.exp 1 * Real.pi * 1) with hCd
  set C2 : ℝ := max (6 * C) (C ^ 2 + C * Ch) with hC2
  have m1 : K ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have m2 : Ca ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have m3 : 2 ≤ Cm := le_max_right _ _
  have n1 : Cm ≤ C := le_max_left _ _
  have n4 : 6 * Real.exp 1 * Real.pi * 1 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  have hChA : max (CDl + 1) 0 ≤ Ch := le_max_right _ _
  have hCh0 : 0 ≤ Ch := le_trans (le_max_right _ _) hChA
  have hChD : CDl ≤ Ch := le_trans (le_max_left _ _) (le_max_left _ _)
  have h62 : 6 * C ≤ C2 := le_max_left _ _
  have h22 : C ^ 2 + C * Ch ≤ C2 := le_max_right _ _
  refine ⟨C, C2, Ch, hC0, hCh0, fun Cpr δ hδ => ?_⟩
  obtain ⟨thr0, hthr0⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max (C + 6 * C * Ch) C) (max (1 / δ) hilbertNinetyConstant))
  refine ⟨thr0, fun D large₂ C' Cl cb Cu cT CT C0 hC' hCl hG hA1 hA2 hA5 hA9 hDeg hAbs hA11 hA12 => ?_⟩
  by_cases hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0
  swap
  · refine ⟨?_, ?_, ?_⟩
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
      exact absurd hH.1 hH0
  obtain ⟨h1000, -, hMm, hMk, -, -, hrb, hm2k, -⟩ := hthr0 D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hM1 : C + 6 * C * Ch ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMm
  have hMC : C ≤ (D.R.k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMk
  have hMd : 1 / δ ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMm
  have hM9 : hilbertNinetyConstant ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMm
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hb : 1 ≤ large₂.sc.b := one_le_b large₂

  have hS3 : VanishingOnXAndXPlusBranching.TowerRallisLemma D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch := by
    refine heightStatement_of_bounds D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 h62 ?_
    nlinarith
  have hS5 : VanishingOnXAndXPlusBranching.GGFromIrreducibility D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch :=
    product_clause_at_record D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 (by linarith) h22

  have hCl1 : 1 / Cl ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have p1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 1 Cc :=
    constant_clause_schur_weyl D large₂ C' Cl Cg cb Cu cT CT C0 1 CS Cc (by rw [hCc]; linarith) hA11 hA12

  have hn : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := by
    calc (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (hilbertNinetyConstant * (D.R.m : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hrb (mul_nonneg hilbertNinetyConstant_pos hm0)
      _ ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by nlinarith)
  have hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast rank_eq_two_mul_add_two D
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hδk : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k := by
    have hmpos : (0 : ℝ) < D.R.m := by rw [hmr]; positivity
    have e1 : 1 ≤ δ * (D.R.m : ℝ) := by
      rw [div_le_iff₀ hδ] at hMd; linarith
    have e3 : (D.R.m : ℝ) ≤ δ * (D.R.m : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right e1 hmpos.le
      nlinarith
    have e4 : δ * (D.R.m : ℝ) ^ 2 ≤ δ * D.R.k := mul_le_mul_of_nonneg_left hm2k hδ.le
    linarith

  have r1 : HilbertSchmidtBoundWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    L2_decay_of_admissible D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CPT CDl Cc Cpr Cm Ch (le_max_right _ _) (le_max_left _ _)
      m1 hCh0 hChD hA1 hA2 p1
  have r2 : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    abs_decay_mono_constants D large₂ hCa0 m2 hChA
      (abs_decay_of_all_parameters D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CDl hilbertNinetyConstant Cpr Ca (max (CDl + 1) 0) (le_max_right _ _)
        (le_max_left _ _) hCa0 hilbertNinetyConstant_pos (le_max_right _ _) (le_max_left _ _) hn hA2 hA9 hDeg hAbs)
  have q7 : VanishingOnXAndXPlusBranching.division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ :=
    decayProp_of_l2AbsDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm C Ch δ m3 n1 hMC hδk n4 hA5 r1 r2
  exact ⟨hS3, hS5, q7⟩

end GlobalTheory

end
