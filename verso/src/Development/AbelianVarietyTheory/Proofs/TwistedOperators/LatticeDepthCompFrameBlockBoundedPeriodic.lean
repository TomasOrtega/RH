import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host
open Matrix

namespace GlobalTheory.DepthBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Set `γ : ValueGroupWithZero k` to `∏ i, max 1 (valuation k (f i))`. Establish `h1 : 1 ≤ γ` using `Finset.one_le_prod' (fun i _ => le_max_left _ _)`. Take `⟨x, hx⟩` from `ValuativeRel.valuation_surjective γ`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hx` using `[map_zero]`. Conclude with `absurd (hx ▸ h1) (not_le.2 zero_lt_one)`. Use `⟨Units.mk0 x hx0, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, hx]`. Conclude with `(le_max_right _ _).trans (Finset.single_le_prod' (f := fun j => max 1 (valuation k (f j))) (fun j _ => le_max_left _ _) (Finset.mem_univ i))`.
-/
theorem exists_unit_bound {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ R : kˣ, ∀ i, valuation k (f i) ≤ valuation k (R : k) := by
  classical
  let γ : ValueGroupWithZero k := ∏ i, max 1 (valuation k (f i))
  have h1 : 1 ≤ γ := Finset.one_le_prod' (fun i _ => le_max_left _ _)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective γ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact absurd (hx ▸ h1) (not_le.2 zero_lt_one)
  refine ⟨Units.mk0 x hx0, fun i => ?_⟩
  rw [Units.val_mk0, hx]
  exact (le_max_right _ _).trans
    (Finset.single_le_prod' (f := fun j => max 1 (valuation k (f j))) (fun j _ => le_max_left _ _) (Finset.mem_univ i))

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[frameMatrixSecondColumnBlock_mul_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Y0]`.

Simplify using `[Y0, Matrix.one_apply, hij, Ne.symm hij]`.
-/
theorem frameMatrixSecondColumnBlock_mul_transpose {A A' D : Type} [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (σ : A ⊕ A' ≃ D) : Y0 k σ * (Y0 k σ)ᵀ = 1 := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  by_cases hij : i = j
  · subst hij; simp [Y0]
  · simp [Y0, Matrix.one_apply, hij, Ne.symm hij]

/- English proof (translation)
Introduce `k _ _ _ _ A A' D _ _ _ _ _ _ σ ϖ e hϖ c Ψ hΨ h`. Use `set Y : Matrix A' D k := Y0 k σ * h.val with hYdef`. Use `set W : Matrix D A' k := (h⁻¹).val * (Y0 k σ)ᵀ with hWdef`. Establish `hYW : Y * W = 1`. Rewrite using `[hYdef, hWdef, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, frameMatrixSecondColumnBlock_mul_transpose]`.

Take `⟨R, hR⟩` from `exists_unit_bound (fun p : D × A' => (c p.1 : k) * W p.1 p.2)`. Take `⟨R', hR'⟩` from `exists_unit_bound (fun p : A' × D => Y p.1 p.2 / (((ϖ ^ e) * c p.2 : kˣ) : k))`. Establish `hlt : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Establish `hR'0 : valuation k (R' : k) ≠ 0` using `by simp`. Take `⟨N, hN⟩` from `exists_pow_lt₀ hlt (Units.mk0 (valuation k (R' : k))⁻¹ (inv_ne_zero hR'0))`.

Establish `hN' : valuation k (ϖ : k) ^ N * valuation k (R' : k) ≤ 1`. Establish `: valuation k (ϖ : k) ^ N ≤ (valuation k (R' : k))⁻¹` using `by simpa using hN.le`. Combine the equalities or inequalities in the displayed calculation. Use `⟨R, N, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg i j`.

Establish `hmem : g * Y ∈ matLat A' (diagLat c)`. Assume the negation of the conclusion as `hc`. Conclude with `hg (hΨ.1 _ hc)`. Establish `hg' : g = (g * Y) * W` using `by rw [Matrix.mul_assoc, hYW, Matrix.mul_one]`. Rewrite using `[hg', Matrix.mul_apply]`.

Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `g Z hZ`. Rewrite using `[Matrix.add_mul]`.

Use `hΨ.2 _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[smul_diagLat, mem_diagLat]`. Introduce `m`. Use `show valuation k ((Z * Y) i m) ≤ _`. Rewrite using `[Matrix.mul_apply]`.

Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Establish `hpos : 0 < valuation k ((((ϖ ^ e) * c m : kˣ)) : k)` using `zero_lt_iff.2 (by simp)`. Establish `h1` using `hR' (l, m)`. Simplify using `only at h1`.

Rewrite `h1` using `[map_div₀, div_le_iff₀ hpos]`. Establish `hz : valuation k (Z i l) ≤ valuation k (ϖ : k) ^ N`. Simplify `hZ i l` using `[Units.val_pow_eq_pow_val, map_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem latticeDepth_comp_frameBlock_bounded_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ ϖ e hϖ c Ψ hΨ h
  set Y : Matrix A' D k := Y0 k σ * h.val with hYdef
  set W : Matrix D A' k := (h⁻¹).val * (Y0 k σ)ᵀ with hWdef
  have hYW : Y * W = 1 := by
    rw [hYdef, hWdef, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, frameMatrixSecondColumnBlock_mul_transpose]
  obtain ⟨R, hR⟩ := exists_unit_bound (fun p : D × A' => (c p.1 : k) * W p.1 p.2)
  obtain ⟨R', hR'⟩ := exists_unit_bound (fun p : A' × D => Y p.1 p.2 / (((ϖ ^ e) * c p.2 : kˣ) : k))
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hR'0 : valuation k (R' : k) ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 (valuation k (R' : k))⁻¹ (inv_ne_zero hR'0))
  have hN' : valuation k (ϖ : k) ^ N * valuation k (R' : k) ≤ 1 := by
    have : valuation k (ϖ : k) ^ N ≤ (valuation k (R' : k))⁻¹ := by simpa using hN.le
    calc valuation k (ϖ : k) ^ N * valuation k (R' : k)
        ≤ (valuation k (R' : k))⁻¹ * valuation k (R' : k) := mul_le_mul' this le_rfl
      _ = 1 := inv_mul_cancel₀ hR'0
  refine ⟨R, N, ?_, ?_⟩
  · intro g hg i j
    have hmem : g * Y ∈ matLat A' (diagLat c) := by
      by_contra hc; exact hg (hΨ.1 _ hc)
    have hg' : g = (g * Y) * W := by rw [Matrix.mul_assoc, hYW, Matrix.mul_one]
    rw [hg', Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc valuation k ((g * Y) i l) * valuation k (W l j)
        ≤ valuation k (c l : k) * valuation k (W l j) := mul_le_mul' (mem_diagLat.1 (hmem i) l) le_rfl
      _ = valuation k ((c l : k) * W l j) := (map_mul _ _ _).symm
      _ ≤ valuation k (R : k) := hR (l, j)
  · intro g Z hZ
    rw [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat, mem_diagLat]
    intro m
    show valuation k ((Z * Y) i m) ≤ _
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    have hpos : 0 < valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := zero_lt_iff.2 (by simp)
    have h1 := hR' (l, m)
    simp only at h1
    rw [map_div₀, div_le_iff₀ hpos] at h1
    have hz : valuation k (Z i l) ≤ valuation k (ϖ : k) ^ N := by
      simpa [Units.val_pow_eq_pow_val, map_pow] using hZ i l
    calc valuation k (Z i l) * valuation k (Y l m)
        ≤ valuation k (ϖ : k) ^ N * (valuation k (R' : k) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k)) :=
          mul_le_mul' hz h1
      _ = (valuation k (ϖ : k) ^ N * valuation k (R' : k)) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) :=
          (mul_assoc _ _ _).symm
      _ ≤ 1 * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := mul_le_mul' hN' le_rfl
      _ = _ := one_mul _

end GlobalTheory.DepthBound
