import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `F L _ _ _ _ _ _ _ _ _ _ _ _ B h0 hB`. Take `⟨hanti, hbot⟩` from `GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L`. Take `⟨n, hn⟩` from `GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot`. Establish `hjs` using `GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B n hanti hn`. Establish `hphi` using `GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 n`.

Simplify using `only [top_inf_eq] at hjs hn`. Establish `hcard : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ)`. Conclude with `Nat.card_pos` after adjusting the coercions. Establish `hidx : (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) = herbrandPhi F L n`. Rewrite using `[hjs, ← hphi]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hidx, upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]`. Consider the cases of `n with`. Consider the case `zero`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ⟩ : ∃ σ, σ ∉ B := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hB (eq_top_iff.mpr fun σ _ => h σ)`. Use `⟨σ, ?_, hσ⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_zero, h0]`.

Conclude with `Subgroup.mem_top σ`. Consider the case `succ k`. Establish `hk : ¬ wild F L k ≤ B` using `(hn k).mp (Nat.lt_succ_self k)`. Take `⟨σ, hσ, hσB⟩` from `SetLike.not_le_iff_exists.mp hk`. Use `⟨σ, ?_, hσB⟩` and prove the remaining obligations.

Establish `: ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1` using `by push_cast; rfl`. Rewrite using `[this]`. Conclude with `hσ`.
-/
theorem exists_mem_upperRamificationGroup_jumpSum_not_mem :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)),
      lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ →
        ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B h0 hB
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  have hjs := GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B n hanti hn
  have hphi := GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 n
  simp only [top_inf_eq] at hjs hn
  have hcard : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hidx : (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) = herbrandPhi F L n := by
    rw [hjs, ← hphi]
    field_simp
  rw [hidx, upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]
  cases n with
  | zero =>
    obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ B := by
      by_contra h
      push_neg at h
      exact hB (eq_top_iff.mpr fun σ _ => h σ)
    refine ⟨σ, ?_, hσ⟩
    rw [Nat.cast_zero, h0]
    exact Subgroup.mem_top σ
  | succ k =>
    have hk : ¬ wild F L k ≤ B := (hn k).mp (Nat.lt_succ_self k)
    obtain ⟨σ, hσ, hσB⟩ := SetLike.not_le_iff_exists.mp hk
    refine ⟨σ, ?_, hσB⟩
    have : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [this]
    exact hσ

end GlobalTheory.PMon.Ram
