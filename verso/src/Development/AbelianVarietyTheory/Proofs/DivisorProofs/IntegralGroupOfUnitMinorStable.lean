import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Set `X' : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨X i j, hX i j⟩`. Establish `e : X = (algebraMap 𝒪[k] k).mapMatrix X'` using `by ext i j; rfl`. Introduce `i j`. Rewrite using `[e, ← RingHom.map_adjugate]`. Conclude with `(X'.adjugate i j).2`.
-/
theorem adjugate_integral {n : ℕ} (X : Matrix (Fin n) (Fin n) k) (hX : ∀ i j, X i j ∈ 𝒪[k]) :
    ∀ i j, X.adjugate i j ∈ 𝒪[k] := by
  let X' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X = (algebraMap 𝒪[k] k).mapMatrix X' := by ext i j; rfl
  intro i j
  rw [e, ← RingHom.map_adjugate]
  exact (X'.adjugate i j).2

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hW l j)`.
-/
theorem mul_integral {a b c : ℕ} (X : Matrix (Fin a) (Fin b) k) (W : Matrix (Fin b) (Fin c) k)
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hW : ∀ i j, W i j ∈ 𝒪[k]) : ∀ i j, (X * W) i j ∈ 𝒪[k] := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hW l j)

/- English proof (translation)
Take `⟨hZi, f, hf⟩` from `hZ`. Use `set Zf := Z.submatrix id f with hZf`. Establish `hsub : (M * Z).submatrix id f = M * Zf`. Use extensionality with `i j`. Simplify using `[Zf, Matrix.mul_apply]`.

Establish `hdet : Zf.det ≠ 0`. Introduce `h0`. Rewrite `hf` using `[h0, map_zero]`. Conclude with `zero_ne_one hf`. Establish `hM : M = (M * Z).submatrix id f * Zf⁻¹`.

Rewrite using `[hsub, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]`. Establish `hZfi : ∀ i j, Zf i j ∈ 𝒪[k]` using `fun i j => hZi _ _`. Establish `hinv : ∀ i j, Zf⁻¹ i j ∈ 𝒪[k]`. Introduce `i j`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']`.

Use `Subring.mul_mem _ ?_ (adjugate_integral Zf hZfi i j)` and prove the remaining obligations. Rewrite using `[Valuation.mem_integer_iff, map_inv₀, hf, inv_one]`. Rewrite using `[hM]`. Conclude with `mul_integral _ _ (fun i j => hMZ _ _) hinv`.
-/
theorem integral_of_mul {n d : ℕ} (M : Matrix (Fin n) (Fin n) k) (Z : Matrix (Fin n) (Fin d) k)
    (hZ : Z ∈ unitMinorSet k n d) (hMZ : ∀ i j, (M * Z) i j ∈ 𝒪[k]) : ∀ i j, M i j ∈ 𝒪[k] := by
  obtain ⟨hZi, f, hf⟩ := hZ
  set Zf := Z.submatrix id f with hZf
  have hsub : (M * Z).submatrix id f = M * Zf := by
    ext i j; simp [Zf, Matrix.mul_apply]
  have hdet : Zf.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hf; exact zero_ne_one hf
  have hM : M = (M * Z).submatrix id f * Zf⁻¹ := by
    rw [hsub, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]
  have hZfi : ∀ i j, Zf i j ∈ 𝒪[k] := fun i j => hZi _ _
  have hinv : ∀ i j, Zf⁻¹ i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine Subring.mul_mem _ ?_ (adjugate_integral Zf hZfi i j)
    rw [Valuation.mem_integer_iff, map_inv₀, hf, inv_one]
  rw [hM]
  exact mul_integral _ _ (fun i j => hMZ _ _) hinv

/- English proof (translation)
Use `(mem_KO_iff E).2 ⟨integral_of_mul _ Y hY hEY.1, integral_of_mul _ (E.val * Y) hEY ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Conclude with `hY.1`.
-/
theorem mem_KO_of_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (hY : Y ∈ unitMinorSet k n d)
    (hEY : E.val * Y ∈ unitMinorSet k n d) : E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  refine (mem_KO_iff E).2 ⟨integral_of_mul _ Y hY hEY.1, integral_of_mul _ (E.val * Y) hEY ?_⟩
  rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  exact hY.1

end GlobalTheory.FullRankCoinv.UnitMinor
