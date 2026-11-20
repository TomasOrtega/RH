import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

/- English proof (translation)
Take `⟨c, hc⟩` from `D.R.t_odd`. Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hs : ∃ d : ℕ, sLen D = 2 * d + 1` using `⟨a + b + 2, by unfold sLen Formalism.BasicNotions.Ranks.r; omega⟩`.

Take `⟨d, hd⟩` from `hs`. Break down `GridData.mem_parD.1 hx with ⟨h1, -⟩ | ⟨l, -, -, rfl⟩ | ⟨l, -, -, h3, -⟩ | ⟨l, -, -, h4, -⟩` into its components or cases. Take `⟨i', -, -, h⟩` from `GridData.mem_cloud.1 h1`. Conclude with `⟨_, h⟩`. Conclude with `⟨-(grid D τ).b l, by push_cast; rfl⟩`.

Simplify using `only [GridData.blockM, TPar.block, Finset.mem_image, Finset.mem_range] at h3`. Take `⟨a', -, h⟩` from `h3`. Use `⟨-((grid D τ).e l) + c - a', ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`. Establish `ht : ((grid D τ).t : ℚ) = 2 * c + 1` using `by exact_mod_cast hc`.

Rewrite using `[ht]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [GridData.blockC, TPar.block, Finset.mem_image, Finset.mem_range] at h4`. Take `⟨a', -, h⟩` from `h4`.

Use `⟨(grid D τ).cen l + d - a', ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`. Establish `ht : ((grid D τ).s : ℚ) = 2 * d + 1` using `by exact_mod_cast hd`. Rewrite using `[ht]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem parD_entry_int (D : D7) (τ : D.what₂.Tau) (i j : ℕ) {x : ℚ × Bool} (hx : x ∈ (grid D τ).parD i j) :
    ∃ z : ℤ, x.1 = z := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  have hs : ∃ d : ℕ, sLen D = 2 * d + 1 := ⟨a + b + 2, by unfold sLen Formalism.BasicNotions.Ranks.r; omega⟩
  obtain ⟨d, hd⟩ := hs
  rcases GridData.mem_parD.1 hx with ⟨h1, -⟩ | ⟨l, -, -, rfl⟩ | ⟨l, -, -, h3, -⟩ | ⟨l, -, -, h4, -⟩
  · obtain ⟨i', -, -, h⟩ := GridData.mem_cloud.1 h1
    exact ⟨_, h⟩
  · exact ⟨-(grid D τ).b l, by push_cast; rfl⟩
  · simp only [GridData.blockM, TPar.block, Finset.mem_image, Finset.mem_range] at h3
    obtain ⟨a', -, h⟩ := h3
    refine ⟨-((grid D τ).e l) + c - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
    rw [ht]; push_cast; ring
  · simp only [GridData.blockC, TPar.block, Finset.mem_image, Finset.mem_range] at h4
    obtain ⟨a', -, h⟩ := h4
    refine ⟨(grid D τ).cen l + d - a', ?_⟩
    rw [← h]
    have ht : ((grid D τ).s : ℚ) = 2 * d + 1 := by exact_mod_cast hd
    rw [ht]; push_cast; ring

/- English proof (translation)
Take `⟨c, hc⟩` from `D.R.t_odd`. Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Establish `hk` using `D.R.m_add_three_le_k`. Take `⟨u, hu⟩ : ∃ u, a + b = u + 1` from `⟨a + b - 1, by omega⟩`.

Establish `hr : D.R.r = 2 * u + 1` using `by unfold Formalism.BasicNotions.Ranks.r; omega`. Establish `e : rkV D i j = 2 * (u + j * c + i * (u + 3)) + (1 + j + i)`. Unfold `rkV sLen`. Rewrite using `[hr, hc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Nat.even_add, Nat.odd_add]`. Simplify using `only [even_two, Even.mul_right, true_iff, Nat.even_add, Nat.odd_add]`. Simplify using `only [Nat.odd_iff, Nat.even_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem even_rkV_iff (D : D7) (i j : ℕ) : Even (rkV D i j) ↔ Odd (i + j) := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hk := D.R.m_add_three_le_k
  obtain ⟨u, hu⟩ : ∃ u, a + b = u + 1 := ⟨a + b - 1, by omega⟩
  have hr : D.R.r = 2 * u + 1 := by unfold Formalism.BasicNotions.Ranks.r; omega
  have e : rkV D i j = 2 * (u + j * c + i * (u + 3)) + (1 + j + i) := by
    unfold rkV sLen; rw [hr, hc]; ring
  rw [e, Nat.even_add, Nat.odd_add]
  simp only [even_two, Even.mul_right, true_iff, Nat.even_add, Nat.odd_add]
  simp only [Nat.odd_iff, Nat.even_iff]; omega

/- English proof (translation)
Introduce `D _ i j _ _ _ τ n lam ε hn hE`. Use `⟨hE.1, fun a' => ?_⟩` and prove the remaining obligations. Take `⟨-, q, hq, hS⟩` from `hE`. Establish `hmem : (q a', ε a') ∈ parV D i j τ` using `by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)`. Simplify using `only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem`.

Take `⟨y, ⟨x, hx, rfl⟩, hy1, -⟩` from `hmem`. Take `⟨z, hz⟩` from `parD_entry_int D τ i j hx`. Establish `hpar` using `even_rkV_iff D i j`. Rewrite using `[hq a', ← hy1]`. Distinguish the cases in `ho : Odd (i + j)`.

Take `⟨N, hN⟩` from `hpar.2 ho`. Rewrite `*` using `[if_pos ho]`. Use `⟨-z + 1 - N, ?_⟩` and prove the remaining obligations. Establish `: (n : ℝ) = N + N` using `by rw [hn, hN]; push_cast; ring`. Simplify using `only [hz, this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : ¬ Even (rkV D i j)` using `fun h => ho (hpar.1 h)`. Take `⟨N, hN⟩` from `Nat.not_even_iff_odd.1 hne`. Rewrite `*` using `[if_neg ho]`.

Use `⟨-z - N, ?_⟩` and prove the remaining obligations. Establish `: (n : ℝ) = 2 * N + 1` using `by rw [hn, hN]; push_cast; ring`. Simplify using `only [hz, this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isHCParam_parV : ∀ (D : D7), HostHyp D → ∀ (i j : ℕ), 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkV D i j → IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i j _ _ _ τ n lam ε hn hE
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ parV D i j τ := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  obtain ⟨z, hz⟩ := parD_entry_int D τ i j hx
  have hpar := even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho] at *
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rkV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho] at *
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.Grid
