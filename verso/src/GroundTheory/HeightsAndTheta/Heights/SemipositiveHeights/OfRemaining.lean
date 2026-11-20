import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefShiftPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.HilbertSamuel

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D α I hI hV hB hNef hPos`. Establish `hagree : ∀ (V : Ideal (MRingOver ℚ ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n → I V n L = NumbersDVR.intNum ℚ V L`. Take `⟨I₀, -, h₀⟩` from `Targets.ExistsUnique.full ℚ ι`. Introduce `V n L hVn`. Rewrite using `[h₀ I hI V n L hVn, h₀ _ (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) V n L hVn]`.

Establish `hG : IsProjVarF (KH.genIdeal y) D` using `isProjVarF_map_of_isArithVar hV`. Establish `hdeg : 0 < genDeg (mCoordIdeal y) D α`. Establish `h` using `hagree _ D (fun _ => α) hG`. Rewrite `hPos` using `[h]`. Conclude with `hPos`.

Choose the witnesses or unpack the hypotheses as in `⟨k, e, hk, he, hmem⟩ : ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • α - 1) 1 := by`. Break down `Nat.eq_zero_or_pos D with rfl | hD` into its components or cases. Establish `hr` using `hZ K ι Ω y ((1 : ℕ) • α - 1) 1 hV`. Establish `hg : genDeg (mCoordIdeal y) 0 ((1 : ℕ) • α - 1) = genDeg (mCoordIdeal y) 0 α`. Unfold `genDeg`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `j.elim0`. Rewrite `hr` using `[hg]`. Establish `hpos : 0 < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1)`.

Establish `: (0 : ℤ) < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1)` using `by rw [hr]; exact hdeg`. Conclude with `this` after adjusting the coercions. Use `Module.nontrivial_of_finrank_pos hpos` as an intermediate fact. Take `⟨⟨e, he⟩, hne⟩` from `exists_ne (0 : chartLatQ y ((1 : ℕ) • α - 1) 1)`. Use `⟨1, e, le_rfl, fun h => hne ?_, by simpa using he⟩` and prove the remaining obligations.

Conclude with `Subtype.ext h`. Establish `hnef : NefOnGenericDeg (mCoordIdeal y) α`. Introduce `W hW hPW`. Establish `hWq : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1` using `isProjVarF_map_of_isArithVar (D := 1) hW`. Establish `h` using `hNef _ hWq (Ideal.map_mono hPW)`.

Rewrite `h` using `[hagree _ 1 _ hWq]`. Unfold `genDeg`. Use `h using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Use `fin_cases j`.

Both sides reduce to the same expression. Conclude with `hK K ι Ω y D α hD hV hB hnef hdeg`. Take `⟨n, hn, hns⟩` from `ChartDenominator.proof K ι Ω y ((k : ℤ) • α - 1) 1 e hmem`. Establish `hn0 : (n : Ω) ≠ 0` using `by exact_mod_cast (show n ≠ 0 by omega)`. Use `⟨k, hk, (n : Ω) * e, ?_, mul_ne_zero hn0 he⟩` and prove the remaining obligations.

Establish `hfun : (fun κ => (k : ℤ) * α κ - 1) = (k : ℤ) • α - 1`. Use function extensionality and compare the values at `κ`. Simplify using the standard rewrite rules. Rewrite using `[hfun]`. Conclude with `hns`.
-/
theorem SiuZB.proof (hK : KodairaGeneric.Statement) (hZ : SectionsDimZero.Statement) : KH.SiuZStatement := by
  intro K _ ι _ Ω _ _ y D α I hI hV hB hNef hPos
  classical

  have hagree : ∀ (V : Ideal (MRingOver ℚ ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum ℚ V L := by
    obtain ⟨I₀, -, h₀⟩ := Targets.ExistsUnique.full ℚ ι
    intro V n L hVn
    rw [h₀ I hI V n L hVn, h₀ _ (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) V n L hVn]
  have hG : IsProjVarF (KH.genIdeal y) D := isProjVarF_map_of_isArithVar hV
  have hdeg : 0 < genDeg (mCoordIdeal y) D α := by
    have h := hagree _ D (fun _ => α) hG
    rw [h] at hPos
    exact hPos

  obtain ⟨k, e, hk, he, hmem⟩ :
      ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • α - 1) 1 := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have hr := hZ K ι Ω y ((1 : ℕ) • α - 1) 1 hV
      have hg : genDeg (mCoordIdeal y) 0 ((1 : ℕ) • α - 1) = genDeg (mCoordIdeal y) 0 α := by
        unfold genDeg
        congr 1
        funext j
        exact j.elim0
      rw [hg] at hr
      have hpos : 0 < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by
        have : (0 : ℤ) < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by rw [hr]; exact hdeg
        exact_mod_cast this
      have := Module.nontrivial_of_finrank_pos hpos
      obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (0 : chartLatQ y ((1 : ℕ) • α - 1) 1)
      refine ⟨1, e, le_rfl, fun h => hne ?_, by simpa using he⟩
      exact Subtype.ext h
    · have hnef : NefOnGenericDeg (mCoordIdeal y) α := by
        intro W hW hPW
        have hWq : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
          isProjVarF_map_of_isArithVar (D := 1) hW
        have h := hNef _ hWq (Ideal.map_mono hPW)
        rw [hagree _ 1 _ hWq] at h
        unfold genDeg
        convert h using 2
        funext j
        fin_cases j
        rfl
      exact hK K ι Ω y D α hD hV hB hnef hdeg

  obtain ⟨n, hn, hns⟩ := ChartDenominator.proof K ι Ω y ((k : ℤ) • α - 1) 1 e hmem
  have hn0 : (n : Ω) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨k, hk, (n : Ω) * e, ?_, mul_ne_zero hn0 he⟩
  have hfun : (fun κ => (k : ℤ) * α κ - 1) = (k : ℤ) • α - 1 := by
    funext κ
    simp
  rw [hfun]
  exact hns

/- English proof (translation)
The claim follows from `SiuZB.proof hK SectionsDimZero.proof`.
-/
theorem SiuZB.of_kodaira (hK : KodairaGeneric.Statement) : KH.SiuZStatement :=
  SiuZB.proof hK SectionsDimZero.proof

end GroundTheory.Heights₂.Heights.ForSecondHalf
