import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBoundedStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ a t ht i j hij`. Take `⟨C0, hC0, hb⟩` from `GlobalTheory.T.cone_coordinate_ratio_bounded a t ht`. Use `⟨C0 * C0 + C0, by positivity, ?_⟩` and prove the remaining obligations. Introduce `r d hr hcone hd`. Establish `hij' : i ≤ j` using `by rw [Fin.le_def]; omega`.

Establish `hji : r j / r i ≤ C0` using `hb r hr hcone i j hij'`. Establish `hji0 : 0 ≤ r j / r i` using `(div_pos (hr j) (hr i)).le`. Use `⟨by nlinarith, fun z => ?_⟩` and prove the remaining obligations. Use `⟨fun p => (r p.1.2 / r p.1.1) • z p, ?_, ?_⟩` and prove the remaining obligations. Establish `hX : 0 ≤ (C0 * C0 + C0) * (r j / r i)` using `by positivity`.

Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_` and prove the remaining obligations. Establish `hk : p.1.1 ≤ i` using `by rw [Fin.le_def]; have := p.2.1; omega`. Establish `hl : j ≤ p.1.2` using `by rw [Fin.le_def]; exact p.2.2`. Establish `h1 : r p.1.2 / r j ≤ C0` using `hb r hr hcone j p.1.2 hl`. Establish `h3 : r i / r p.1.1 ≤ C0` using `hb r hr hcone p.1.1 i hk`.

Establish `hpos : 0 < r p.1.2 / r p.1.1` using `div_pos (hr _) (hr _)`. Establish `heq : r p.1.2 / r p.1.1 = (r p.1.2 / r j) * (r j / r i) * (r i / r p.1.1)`. Use `hr j` as an intermediate fact. Use `hr i` as an intermediate fact. Use `hr p.1.1` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `hbd : r p.1.2 / r p.1.1 ≤ (C0 * C0 + C0) * (r j / r i)`. Rewrite using `[heq]`. Establish `e1 : 0 ≤ r p.1.2 / r j` using `(div_pos (hr _) (hr _)).le`. Establish `e3 : 0 ≤ r i / r p.1.1` using `(div_pos (hr _) (hr _)).le`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul_of_nonneg_right h1 hji0) h3 e3 (by positivity)` to reduce the goal to its premises. Use `_ ≤ (C0 * C0 + C0) * (r j / r i) := by nlinarith`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos hpos]`. Conclude with `mul_le_mul hbd (norm_le_pi_norm z p) (norm_nonneg _) hX`.

Introduce `τ`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, hd]`. Express the relevant statement in the definitionally equal form `(1 + nilM (τ • z)) * _ = _ * (1 + nilM (τ • fun p => (r p.1.2 / r p.1.1) • z p))`. Use extensionality with `k l w`.

Rewrite using `[add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Use `congr 1`. Simplify using `only [nilM, Matrix.of_apply]`. Use `split_ifs with h`. Simplify using `only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, add_right_inj]`.

Use `hr k` as an intermediate fact. Establish `hk0 : (r k : ℂ) ≠ 0` using `by exact_mod_cast this.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.
-/
theorem unip_mul_diag_cone : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → r j / r i ≤ C ∧ ∀ z : BlockIx a j → Cinf E, ∃ z' : BlockIx a j → Cinf E, ‖z'‖ ≤ C * (r j / r i) * ‖z‖ ∧ ∀ τ : ℝ, unip (τ • z) * d = d * unip (τ • z') := by
  intro E _ _ _ a t ht i j hij
  obtain ⟨C0, hC0, hb⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  refine ⟨C0 * C0 + C0, by positivity, ?_⟩
  intro r d hr hcone hd
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hji : r j / r i ≤ C0 := hb r hr hcone i j hij'
  have hji0 : 0 ≤ r j / r i := (div_pos (hr j) (hr i)).le
  refine ⟨by nlinarith, fun z => ?_⟩
  refine ⟨fun p => (r p.1.2 / r p.1.1) • z p, ?_, ?_⟩
  · have hX : 0 ≤ (C0 * C0 + C0) * (r j / r i) := by positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    have hk : p.1.1 ≤ i := by rw [Fin.le_def]; have := p.2.1; omega
    have hl : j ≤ p.1.2 := by rw [Fin.le_def]; exact p.2.2
    have h1 : r p.1.2 / r j ≤ C0 := hb r hr hcone j p.1.2 hl
    have h3 : r i / r p.1.1 ≤ C0 := hb r hr hcone p.1.1 i hk
    have hpos : 0 < r p.1.2 / r p.1.1 := div_pos (hr _) (hr _)
    have heq : r p.1.2 / r p.1.1 = (r p.1.2 / r j) * (r j / r i) * (r i / r p.1.1) := by
      have := hr j; have := hr i; have := hr p.1.1
      field_simp
    have hbd : r p.1.2 / r p.1.1 ≤ (C0 * C0 + C0) * (r j / r i) := by
      rw [heq]
      have e1 : 0 ≤ r p.1.2 / r j := (div_pos (hr _) (hr _)).le
      have e3 : 0 ≤ r i / r p.1.1 := (div_pos (hr _) (hr _)).le
      calc r p.1.2 / r j * (r j / r i) * (r i / r p.1.1) ≤ C0 * (r j / r i) * C0 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hji0) h3 e3 (by positivity)
        _ ≤ (C0 * C0 + C0) * (r j / r i) := by nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    exact mul_le_mul hbd (norm_le_pi_norm z p) (norm_nonneg _) hX
  · intro τ
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hd]
    change (1 + nilM (τ • z)) * _ = _ * (1 + nilM (τ • fun p => (r p.1.2 / r p.1.1) • z p))
    ext k l w
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    congr 1
    simp only [nilM, Matrix.of_apply]
    split_ifs with h
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, add_right_inj]
      have := hr k
      have hk0 : (r k : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast
      field_simp
    · simp

end GlobalTheory
