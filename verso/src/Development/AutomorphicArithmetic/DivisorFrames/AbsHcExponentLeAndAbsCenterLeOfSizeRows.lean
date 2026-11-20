import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

/- English proof (translation)
Introduce `D large₂ hS hH`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hb, he, -⟩` from `hS`. Establish `hbpos : 0 < large₂.sc.b`. Use `large₂.Sc_pos` as an intermediate fact. Establish `: (0 : ℝ) ≤ (↑D.R.m + 1) * ↑(gap D 1)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun τ l => ?_, fun τ i hi him => ?_⟩` and prove the remaining obligations. Take `⟨hb0, he0⟩` from `he τ l`. Establish `hg` using `((hH.gap τ l).1)`. Establish `ht : (0 : ℚ) ≤ ((D.R.t : ℚ) + 3) / 2` using `by positivity`.

Establish `hepos : (0 : ℚ) ≤ (D.hc τ).e l` using `by linarith`. Establish `hepos' : (0 : ℝ) ≤ (((D.hc τ).e l : ℚ) : ℝ)` using `by exact_mod_cast hepos`. Rewrite using `[abs_of_nonneg hepos']`. Conclude with `he0`. Use `set G := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG`.

Establish `hcen : cen D 1 τ i = ⌊G.mid i⌋` using `rfl`. Establish `hmid : G.mid i = G.a i + (G.ga : ℚ) / 2` using `G.mid_eq hi`. Establish `ha : G.a i = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1 - i) * G.ga` using `rfl`. Establish `hm : G.m = D.R.m` using `rfl`. Establish `hga : G.ga = gap D 1` using `rfl`.

Establish `hv : 0 ≤ G.v 2 ∧ ((G.v 2 : ℚ) : ℝ) ≤ large₂.Sc`. Distinguish the cases in `hk : 0 < D.R.k - 1`. Establish `hv2 : G.v 2 = ⌊(D.hc τ).v ⟨0, hk⟩⌋`. Simplify using `[hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]`. Take `⟨h0, h1⟩` from `large₂.cloud_v τ ⟨0, hk⟩`.

Establish `h0' : (0 : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩` using `by exact_mod_cast h0`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv2]`. Conclude with `Int.floor_nonneg.mpr h0'`. Rewrite using `[hv2]`.

Establish `hfl : ((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩` using `Int.floor_le _`. Establish `hfl' : ((((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ)) : ℝ) ≤ (((D.hc τ).v ⟨0, hk⟩ : ℚ) : ℝ)`. Conclude with `hfl` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv2 : G.v 2 = 0`.

Simplify using `[hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]`. Rewrite using `[hv2]`. Use `⟨le_rfl, ?_⟩` and prove the remaining obligations. Simplify using `using large₂.Sc_pos.le`. Take `⟨hv0, hv1⟩` from `hv`.

Establish `hi' : (1 : ℚ) ≤ i` using `by exact_mod_cast hi`. Establish `him' : (i : ℚ) ≤ D.R.m` using `by exact_mod_cast him`. Establish `hga0 : (0 : ℚ) ≤ G.ga` using `by positivity`. Establish `hv0' : (0 : ℚ) ≤ G.v 2` using `by exact_mod_cast hv0`. Establish `hmid0 : 0 ≤ G.mid i`.

Rewrite using `[hmid, ha, hm]`. Establish `: (0 : ℚ) ≤ ((D.R.m : ℚ) + 1 - i) * G.ga` using `mul_nonneg (by linarith) hga0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmid1 : ((G.mid i : ℚ) : ℝ) ≤ large₂.sc.b`. Establish `e1 : ((G.mid i : ℚ) : ℝ) = ((G.v 2 : ℚ) : ℝ) + 1 / 2 + (((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ)) + (gap D 1 : ℝ) / 2`.

Rewrite using `[hmid, ha, hm, hga]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hgr : (0 : ℝ) ≤ (gap D 1 : ℝ)` using `by positivity`. Establish `hir : (1 : ℝ) ≤ i` using `by exact_mod_cast hi`.

Establish `: ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ)`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf0 : 0 ≤ cen D 1 τ i`. Rewrite using `[hcen]`.

Conclude with `Int.floor_nonneg.mpr hmid0`. Establish `hf1 : ((cen D 1 τ i : ℤ) : ℝ) ≤ large₂.sc.b`. Rewrite using `[hcen]`. Establish `hfl : ((⌊G.mid i⌋ : ℤ) : ℚ) ≤ G.mid i` using `Int.floor_le _`. Establish `hfl' : ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) ≤ ((G.mid i : ℚ) : ℝ)` using `by exact_mod_cast hfl`.

Establish `: (((⌊G.mid i⌋ : ℤ)) : ℝ) = ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ)` using `by push_cast; rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf0' : (0 : ℝ) ≤ ((cen D 1 τ i : ℤ) : ℝ)` using `by exact_mod_cast hf0`. Rewrite using `[abs_of_nonneg hf0']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows :
    ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → (∀ τ l, |(((D.hc τ).e l : ℚ) : ℝ)| ≤ 4 * large₂.sc.b) ∧ ∀ τ i, 1 ≤ i → i ≤ D.R.m → |((cen D 1 τ i : ℤ) : ℝ)| ≤ 2 * large₂.sc.b := by
  intro D large₂ hS hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, he, -⟩ := hS
  have hbpos : 0 < large₂.sc.b := by
    have := large₂.Sc_pos
    have : (0 : ℝ) ≤ (↑D.R.m + 1) * ↑(gap D 1) := by positivity
    linarith
  refine ⟨fun τ l => ?_, fun τ i hi him => ?_⟩
  · obtain ⟨hb0, he0⟩ := he τ l
    have hg := ((hH.gap τ l).1)
    have ht : (0 : ℚ) ≤ ((D.R.t : ℚ) + 3) / 2 := by positivity
    have hepos : (0 : ℚ) ≤ (D.hc τ).e l := by linarith
    have hepos' : (0 : ℝ) ≤ (((D.hc τ).e l : ℚ) : ℝ) := by exact_mod_cast hepos
    rw [abs_of_nonneg hepos']
    exact he0
  · set G := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG
    have hcen : cen D 1 τ i = ⌊G.mid i⌋ := rfl
    have hmid : G.mid i = G.a i + (G.ga : ℚ) / 2 := G.mid_eq hi
    have ha : G.a i = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1 - i) * G.ga := rfl
    have hm : G.m = D.R.m := rfl
    have hga : G.ga = gap D 1 := rfl
    have hv : 0 ≤ G.v 2 ∧ ((G.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by
      by_cases hk : 0 < D.R.k - 1
      · have hv2 : G.v 2 = ⌊(D.hc τ).v ⟨0, hk⟩⌋ := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        obtain ⟨h0, h1⟩ := large₂.cloud_v τ ⟨0, hk⟩
        have h0' : (0 : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := by exact_mod_cast h0
        refine ⟨?_, ?_⟩
        · rw [hv2]
          exact Int.floor_nonneg.mpr h0'
        · rw [hv2]
          have hfl : ((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := Int.floor_le _
          have hfl' : ((((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ)) : ℝ) ≤ (((D.hc τ).v ⟨0, hk⟩ : ℚ) : ℝ) := by
            exact_mod_cast hfl
          linarith
      · have hv2 : G.v 2 = 0 := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        rw [hv2]
        refine ⟨le_rfl, ?_⟩
        simpa using large₂.Sc_pos.le
    obtain ⟨hv0, hv1⟩ := hv
    have hi' : (1 : ℚ) ≤ i := by exact_mod_cast hi
    have him' : (i : ℚ) ≤ D.R.m := by exact_mod_cast him
    have hga0 : (0 : ℚ) ≤ G.ga := by positivity
    have hv0' : (0 : ℚ) ≤ G.v 2 := by exact_mod_cast hv0
    have hmid0 : 0 ≤ G.mid i := by
      rw [hmid, ha, hm]
      have : (0 : ℚ) ≤ ((D.R.m : ℚ) + 1 - i) * G.ga := mul_nonneg (by linarith) hga0
      linarith
    have hmid1 : ((G.mid i : ℚ) : ℝ) ≤ large₂.sc.b := by
      have e1 : ((G.mid i : ℚ) : ℝ) = ((G.v 2 : ℚ) : ℝ) + 1 / 2 + (((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ)) + (gap D 1 : ℝ) / 2 := by
        rw [hmid, ha, hm, hga]
        push_cast
        ring
      have hgr : (0 : ℝ) ≤ (gap D 1 : ℝ) := by positivity
      have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by
        nlinarith
      linarith
    have hf0 : 0 ≤ cen D 1 τ i := by
      rw [hcen]
      exact Int.floor_nonneg.mpr hmid0
    have hf1 : ((cen D 1 τ i : ℤ) : ℝ) ≤ large₂.sc.b := by
      rw [hcen]
      have hfl : ((⌊G.mid i⌋ : ℤ) : ℚ) ≤ G.mid i := Int.floor_le _
      have hfl' : ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) ≤ ((G.mid i : ℚ) : ℝ) := by exact_mod_cast hfl
      have : (((⌊G.mid i⌋ : ℤ)) : ℝ) = ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) := by push_cast; rfl
      linarith
    have hf0' : (0 : ℝ) ≤ ((cen D 1 τ i : ℤ) : ℝ) := by exact_mod_cast hf0
    rw [abs_of_nonneg hf0']
    linarith
