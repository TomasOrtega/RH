import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

/- English proof (translation)
Rewrite using `[Matrix.mulVec, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)`.
-/
theorem norm_mulVec_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (i : Fin n) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  rw [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)

/- English proof (translation)
Rewrite using `[Matrix.vecMul, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hv k) (norm_nonneg _) (hA k j)`.
-/
theorem norm_vecMul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (v : Fin n → F) (A : Matrix (Fin n) (Fin n) F) (hv : ∀ i, ‖v i‖ ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (j : Fin n) : ‖(v ᵥ* A) j‖ ≤ 1 := by
  rw [Matrix.vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hv k) (norm_nonneg _) (hA k j)

def IsIntegral {F : Type} [NormedField F] {n : ℕ} (Y : Gl n F) : Prop :=
  (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hY`. Use `⟨fun i j => ?_, fun i => ?_, fun i => ?_, h4⟩` and prove the remaining obligations. Conclude with `norm_mul_apply_le_one _ _ (fun i j => norm_mul_apply_le_one _ _ (fun i j => (hk i j).1) h1 i j) (fun i j => (hk i j).2) i j`. Conclude with `norm_mulVec_apply_le_one _ _ (fun i j => (hk i j).1) h2 i`. Conclude with `norm_vecMul_apply_le_one _ _ h3 (fun i j => (hk i j).2) i`.
-/
theorem isIntegral_act {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ glO n F) {Y : Gl n F} (hY : IsIntegral Y) : IsIntegral (act k Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hY
  refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, h4⟩
  · exact norm_mul_apply_le_one _ _
      (fun i j => norm_mul_apply_le_one _ _ (fun i j => (hk i j).1) h1 i j) (fun i j => (hk i j).2) i j
  · exact norm_mulVec_apply_le_one _ _ (fun i j => (hk i j).1) h2 i
  · exact norm_vecMul_apply_le_one _ _ h3 (fun i j => (hk i j).2) i

/- English proof (translation)
Take `⟨A, b, c, l⟩` from `Y`. Simplify using `only [act, inv_inv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]`. Use `Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))` and prove the remaining obligations. Use `show ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((k : Matrix (Fin n) (Fin n) F) * A * ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (k : Matrix (Fin n) (Fin n) F) = A`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Use `show (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) *ᵥ b = b`. Rewrite using `[Units.inv_mul, Matrix.one_mulVec]`. Use `show c ᵥ* (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) = c`. Rewrite using `[Units.inv_mul, Matrix.vecMul_one]`.
-/
theorem act_inv_act {F : Type} [Field F] {n : ℕ} (k : GL (Fin n) F) (Y : Gl n F) :
    act k⁻¹ (act k Y) = Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, inv_inv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((k : Matrix (Fin n) (Fin n) F) * A *
        ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (k : Matrix (Fin n) (Fin n) F) = A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  · show (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) *ᵥ b = b
    rw [Units.inv_mul, Matrix.one_mulVec]
  · show c ᵥ* (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) = c
    rw [Units.inv_mul, Matrix.vecMul_one]

/- English proof (translation)
Introduce `F _ _ n k hk Y`. Establish `hk' : k⁻¹ ∈ glO n F` using `(glOSub n F).inv_mem hk`. Establish `key : IsIntegral (act k Y) ↔ IsIntegral Y` using `⟨fun h => act_inv_act k Y ▸ isIntegral_act hk' h, isIntegral_act hk⟩`. Establish `e : ∀ Z : Gl n F, unitG n F Z = Set.indicator {Z | IsIntegral Z} 1 Z` using `fun _ => rfl`. Rewrite using `[e, e]`.

Distinguish the cases in `h : IsIntegral Y`. Rewrite using `[Set.indicator_of_mem (show act k Y ∈ {Z | IsIntegral Z} from key.2 h), Set.indicator_of_mem (show Y ∈ {Z | IsIntegral Z} from h)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show act k Y ∉ {Z | IsIntegral Z} from fun h' => h (key.1 h')), Set.indicator_of_notMem (show Y ∉ {Z | IsIntegral Z} from h)]`.
-/
theorem unitG_act : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F),
    k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  intro F _ _ n k hk Y
  have hk' : k⁻¹ ∈ glO n F := (glOSub n F).inv_mem hk
  have key : IsIntegral (act k Y) ↔ IsIntegral Y :=
    ⟨fun h => act_inv_act k Y ▸ isIntegral_act hk' h, isIntegral_act hk⟩
  have e : ∀ Z : Gl n F, unitG n F Z = Set.indicator {Z | IsIntegral Z} 1 Z := fun _ => rfl
  rw [e, e]
  by_cases h : IsIntegral Y
  · rw [Set.indicator_of_mem (show act k Y ∈ {Z | IsIntegral Z} from key.2 h),
      Set.indicator_of_mem (show Y ∈ {Z | IsIntegral Z} from h)]
    rfl
  · rw [Set.indicator_of_notMem (show act k Y ∉ {Z | IsIntegral Z} from fun h' => h (key.1 h')),
      Set.indicator_of_notMem (show Y ∉ {Z | IsIntegral Z} from h)]

end GlobalTheory.JR.GLift
