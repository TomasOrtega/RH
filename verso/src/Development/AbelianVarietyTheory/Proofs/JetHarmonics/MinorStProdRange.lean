import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

@[to_additive]
/- English proof (translation)
Rewrite using `[Finset.prod_range_succ', hg 0 (by omega), _root_.mul_one, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) r]`. Use `symm`. Apply `Finset.prod_subset (Finset.range_subset_range.mpr hr)` to reduce the goal to its premises. Introduce `s _ hs`. Apply `hg` to reduce the goal to its premises.

Rewrite `hs` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem minorSt_prod_range {M : Type} [CommMonoid M] {N r : ℕ} (hr : r ≤ N) (g : ℕ → M)
    (hg : ∀ s, ¬ (1 ≤ s ∧ s ≤ r) → g s = 1) :
    ∏ s ∈ Finset.range (N + 1), g s = ∏ s : Fin r, g (s.val + 1) := by
  rw [Finset.prod_range_succ', hg 0 (by omega), _root_.mul_one, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) r]
  symm
  apply Finset.prod_subset (Finset.range_subset_range.mpr hr)
  intro s _ hs
  apply hg
  rw [Finset.mem_range] at hs
  omega

/- English proof (translation)
Introduce `E _ _ _ H Dw K _ typ m n₁ n₂ hm`. Set `rk : (E →+* ℂ) → ℕ` to `fun τ => min (Dw.mult τ) (if typ τ then n₁ else n₂)`. Establish `hrk : ∀ τ, rk τ ≤ Dw.mult τ` using `fun τ => min_le_left _ _`. Establish `hrk1 : ∀ τ, typ τ → rk τ ≤ n₁` using `fun τ h => (min_le_right _ _).trans (by simp [h])`. Establish `hrk2 : ∀ τ, ¬ typ τ → rk τ ≤ n₂` using `fun τ h => (min_le_right _ _).trans (by simp [h])`.

Establish `hm0 : ∀ τ s, ¬ (1 ≤ s ∧ s ≤ rk τ) → m τ s = 0`. Introduce `τ s hs`. Assume the negation of the conclusion as `h`. Take `⟨h1, h2, h3⟩` from `hm τ s h`. Conclude with `hs ⟨h1, le_min h2 h3⟩`.

Set `col : ∀ τ, Fin (rk τ) → Fin (n₁ + n₂)` to `fun τ i => if h : typ τ then Fin.castAdd n₂ (Fin.castLE (hrk1 τ h) i) else Fin.natAdd n₁ (Fin.castLE (hrk2 τ h) i)`. Use `⟨rk, hrk, col, fun τ s => m τ (s.val + 1), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ i j hij`. Distinguish the cases in `h : typ τ`. Simplify using `only [col, dif_pos h] at hij`.

Use `congrArg Fin.val hij` as an intermediate fact. Conclude with `Fin.ext (by simpa using this)`. Simplify using `only [col, dif_neg h] at hij`. Use `congrArg Fin.val hij` as an intermediate fact. Conclude with `Fin.ext (by simpa using this)`.

Introduce `τ i`. Distinguish the cases in `h : typ τ`. Use `hrk1 τ h` as an intermediate fact. Use `i.isLt` as an intermediate fact. Simplify using `only [col, dif_pos h, h, iff_true, Fin.val_castAdd, Fin.val_castLE]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[col, h]`. Unfold `degOf`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[minorSt_sum_range (hrk τ) (fun s => s * m τ s) (fun s hs => by simp [hm0 τ s hs])]`.

Conclude with `Finset.sum_congr rfl fun s _ => mul_comm _ _`. Unfold `minorProd FamGerm.minorsP`. Rewrite using `[← Finset.prod_mul_distrib, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`.

Distinguish the cases in `h : typ τ`. Rewrite using `[if_pos h, if_neg (not_not.mpr h), _root_.mul_one, minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₁` using `⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk1 τ h)⟩`. Rewrite using `[dif_pos hs, map_pow, AlgHom.map_det]`.

Unfold `leadMinor`. Use `congr 2`. Use extensionality with `a i : 2`. Simplify using `only [col, dif_pos h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]`. Both sides reduce to the same expression.

Rewrite using `[if_neg h, if_pos h, _root_.one_mul, minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₂` using `⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk2 τ h)⟩`. Rewrite using `[dif_pos hs, map_pow, AlgHom.map_det]`. Unfold `leadMinor`.

Use `congr 2`. Use extensionality with `a i : 2`. Simplify using `only [col, dif_neg h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]`. Both sides reduce to the same expression.
-/
theorem minorSt : MinorSt := by
  classical
  intro E _ _ _ H Dw K _ typ m n₁ n₂ hm
  let rk : (E →+* ℂ) → ℕ := fun τ => min (Dw.mult τ) (if typ τ then n₁ else n₂)
  have hrk : ∀ τ, rk τ ≤ Dw.mult τ := fun τ => min_le_left _ _
  have hrk1 : ∀ τ, typ τ → rk τ ≤ n₁ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hrk2 : ∀ τ, ¬ typ τ → rk τ ≤ n₂ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hm0 : ∀ τ s, ¬ (1 ≤ s ∧ s ≤ rk τ) → m τ s = 0 := by
    intro τ s hs
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hm τ s h
    exact hs ⟨h1, le_min h2 h3⟩
  let col : ∀ τ, Fin (rk τ) → Fin (n₁ + n₂) := fun τ i =>
    if h : typ τ then Fin.castAdd n₂ (Fin.castLE (hrk1 τ h) i) else Fin.natAdd n₁ (Fin.castLE (hrk2 τ h) i)
  refine ⟨rk, hrk, col, fun τ s => m τ (s.val + 1), ?_, ?_, ?_, ?_⟩
  · intro τ i j hij
    by_cases h : typ τ
    · simp only [col, dif_pos h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
    · simp only [col, dif_neg h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
  · intro τ i
    by_cases h : typ τ
    · have := hrk1 τ h
      have := i.isLt
      simp only [col, dif_pos h, h, iff_true, Fin.val_castAdd, Fin.val_castLE]
      omega
    · simp [col, h]
  · unfold degOf
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [minorSt_sum_range (hrk τ) (fun s => s * m τ s) (fun s hs => by simp [hm0 τ s hs])]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  · unfold minorProd FamGerm.minorsP
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod]
    by_cases h : typ τ
    · rw [if_pos h, if_neg (not_not.mpr h), _root_.mul_one,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₁ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk1 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_pos h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl
    · rw [if_neg h, if_pos h, _root_.one_mul,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₂ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk2 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_neg h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl

end GlobalTheory.PowGerm
