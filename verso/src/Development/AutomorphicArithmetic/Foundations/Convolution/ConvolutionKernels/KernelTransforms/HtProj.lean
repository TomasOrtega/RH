import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormDetLeHeightPow

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Use `set e : ℝ := ((n * Module.finrank ℚ K : ℝ))⁻¹ with he`. Establish `he0 : 0 ≤ e` using `by positivity`. Establish `he1 : e ≤ 1`. Rewrite using `[he, ← Nat.cast_mul]`. Conclude with `Nat.cast_inv_le_one _`.

Establish `key : ∀ x : ℝ, 0 ≤ x → x ≤ L → x ^ e ≤ L` using `fun x hx hxL =>`. Combine the equalities or inequalities in the displayed calculation. Use `height_diagUnits_posIdele_le (K := K) (n := n) (ρ := fun _ => (s : ℝ) ^ e) (fun _ => Real.rpow_pos_of_pos s.2 e) hL fun _ => ⟨key _ s.2.le h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Real.inv_rpow s.2.le]`. Conclude with `key _ (inv_pos.2 s.2).le h2`.
-/
private theorem UpperTheory.ConvolutionTheory.Tf.height_centralSection_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (s : {r : ℝ // 0 < r}) {L : ℝ} (hL : 1 ≤ L) (h1 : (s : ℝ) ≤ L) (h2 : (s : ℝ)⁻¹ ≤ L) :
    AutomorphicForm.height (centralSection K n s) ≤ L ^ (2 * Fintype.card (InfinitePlace K)) := by
  set e : ℝ := ((n * Module.finrank ℚ K : ℝ))⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, ← Nat.cast_mul]
    exact Nat.cast_inv_le_one _
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ L → x ^ e ≤ L := fun x hx hxL =>
    calc x ^ e ≤ L ^ e := Real.rpow_le_rpow hx hxL he0
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL he1
      _ = L := Real.rpow_one L
  refine height_diagUnits_posIdele_le (K := K) (n := n) (ρ := fun _ => (s : ℝ) ^ e)
    (fun _ => Real.rpow_pos_of_pos s.2 e) hL fun _ => ⟨key _ s.2.le h1, ?_⟩
  rw [← Real.inv_rpow s.2.le]
  exact key _ (inv_pos.2 s.2).le h2

/- English proof (translation)
Introduce `K _ _ n`. Take `⟨D, N, -, hD⟩` from `UpperTheory.adelicNorm_det_le_height_pow K n`. Use `set m := 2 * Fintype.card (InfinitePlace K) with hm`. Establish `hC : 1 ≤ heightConst K n` using `one_le_heightConst`. Establish `hD1 : (1 : ℝ) ≤ max 1 D` using `le_max_left _ _`.

Use `⟨heightConst K n * max 1 D ^ m, N * m + 1, one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD1), fun g => ?_⟩` and prove the remaining obligations. Establish `hg` using `one_le_height g`. Establish `hb : ∀ x : AdelicGLn.AdelicGL K n, AutomorphicForm.height x = AutomorphicForm.height g → (detModule K n x : ℝ) ≤ max 1 D * AutomorphicForm.height g ^ N` using `fun x hx => by`. Use `(hD x).trans ?_` and prove the remaining obligations. Rewrite using `[hx]`.

Conclude with `mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)`. Establish `h2 : (detModule K n g : ℝ)⁻¹ ≤ max 1 D * AutomorphicForm.height g ^ N`. Use `hb g⁻¹ (height_inv g)` as an intermediate fact. Rewrite `this` using `[map_inv, Positive.coe_inv]`. Then use the resulting hypothesis. Establish `hz` using `UpperTheory.ConvolutionTheory.Tf.height_centralSection_le K n (detModule K n g) (one_le_mul_of_one_le_of_one_le hD1 (one_le_pow₀ hg)) (hb g rfl) h2`.

Rewrite using `[coe_retractOne]`. Use `(height_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[height_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.ConvolutionTheory.Tf.htProj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (c : ℕ), 1 ≤ C ∧ ∀ g : AdelicGLn.AdelicGL K n,
      AutomorphicForm.height (retractOne g : AdelicGLn.AdelicGL K n) ≤ C * AutomorphicForm.height g ^ c := by
  intro K _ _ n
  obtain ⟨D, N, -, hD⟩ := UpperTheory.adelicNorm_det_le_height_pow K n
  set m := 2 * Fintype.card (InfinitePlace K) with hm
  have hC : 1 ≤ heightConst K n := one_le_heightConst
  have hD1 : (1 : ℝ) ≤ max 1 D := le_max_left _ _
  refine ⟨heightConst K n * max 1 D ^ m, N * m + 1,
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD1), fun g => ?_⟩
  have hg := one_le_height g
  have hb : ∀ x : AdelicGLn.AdelicGL K n, AutomorphicForm.height x = AutomorphicForm.height g →
      (detModule K n x : ℝ) ≤ max 1 D * AutomorphicForm.height g ^ N := fun x hx => by
    refine (hD x).trans ?_
    rw [hx]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have h2 : (detModule K n g : ℝ)⁻¹ ≤ max 1 D * AutomorphicForm.height g ^ N := by
    have := hb g⁻¹ (height_inv g)
    rwa [map_inv, Positive.coe_inv] at this
  have hz := UpperTheory.ConvolutionTheory.Tf.height_centralSection_le K n (detModule K n g)
    (one_le_mul_of_one_le_of_one_le hD1 (one_le_pow₀ hg)) (hb g rfl) h2
  rw [coe_retractOne]
  refine (height_mul_le _ _).trans ?_
  rw [height_inv]
  calc heightConst K n * AutomorphicForm.height g *
        AutomorphicForm.height (centralSection K n (detModule K n g))
      ≤ heightConst K n * AutomorphicForm.height g * (max 1 D * AutomorphicForm.height g ^ N) ^ m :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring
