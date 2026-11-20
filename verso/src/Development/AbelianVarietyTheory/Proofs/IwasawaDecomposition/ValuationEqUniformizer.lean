import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaStep
open GlobalTheory.IwaCell GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

/- English proof (translation)
Take `⟨y, hy⟩` from `valuation_surjective (uniformizer k)`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[map_zero]`. Conclude with `uniformizer_pos.ne' hy.symm`.

Set `π₀ : kˣ` to `Units.mk0 y hy0`. Establish `h1 : ord k π₀ = 1` using `ord_eq_one (by simpa [π₀] using hy)`. Establish `h2 : ord k (ϖ * π₀⁻¹) = 0`. Rewrite using `[ord_mul, show π₀⁻¹ = π₀ ^ (-1 : ℤ) by simp, ord_zpow, h1, hϖ]; ring`. Establish `h3` using `ord_eq_zero_iff.1 h2`.

Rewrite `h3` using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]`. Establish `hne : valuation k (π₀ : k) ≠ 0` using `by simp`. Rewrite `h3` using `[mul_inv_eq_one₀ hne]`. Rewrite using `[h3]`. Simplify `hy` using `[π₀]`.
-/
theorem valuation_eq_uniformizer {ϖ : kˣ} (hϖ : ord k ϖ = 1) : valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact uniformizer_pos.ne' hy.symm
  let π₀ : kˣ := Units.mk0 y hy0
  have h1 : ord k π₀ = 1 := ord_eq_one (by simpa [π₀] using hy)
  have h2 : ord k (ϖ * π₀⁻¹) = 0 := by
    rw [ord_mul, show π₀⁻¹ = π₀ ^ (-1 : ℤ) by simp, ord_zpow, h1, hϖ]; ring
  have h3 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at h3
  have hne : valuation k (π₀ : k) ≠ 0 := by simp
  rw [mul_inv_eq_one₀ hne] at h3
  rw [h3]
  simpa [π₀] using hy

/- English proof (translation)
Rewrite using `[← tD_neg]`. Both sides reduce to the same expression.
-/
theorem diagT_neg (ϖ : kˣ) (d : Fin m → ℤ) : diagT k (Fin m) (fun i => ϖ ^ (-d i)) = (tD ϖ d)⁻¹ := by
  rw [← tD_neg]
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.IwahoriTraceProof.dominantContracts ϖ (valuation_eq_uniformizer hϖ) (fun i => -d i) fun _ _ h => neg_le_neg (hd h)`.
-/
theorem contracts_neg {ϖ : kˣ} (hϖ : ord k ϖ = 1) {d : Fin m → ℤ} (hd : Monotone d) :
    Contracts (fun i => ϖ ^ (-d i)) :=
  GlobalTheory.IwahoriTraceProof.dominantContracts ϖ (valuation_eq_uniformizer hϖ) (fun i => -d i)
    fun _ _ h => neg_le_neg (hd h)

/- English proof (translation)
Use `(contracts_neg hϖ hd).2 u hu` as an intermediate fact. Rewrite `this` using `[diagT_neg, inv_inv]`. Then use the resulting hypothesis.
-/
theorem conj_mem_unipLowerOne {ϖ : kˣ} (hϖ : ord k ϖ = 1) {d : Fin m → ℤ} (hd : Monotone d) {u : GL (Fin m) k}
    (hu : u ∈ unipLowerOne k (Fin m)) : tD ϖ d * u * (tD ϖ d)⁻¹ ∈ unipLowerOne k (Fin m) := by
  have := (contracts_neg hϖ hd).2 u hu
  rwa [diagT_neg, inv_inv] at this

end GlobalTheory.IwaStep
