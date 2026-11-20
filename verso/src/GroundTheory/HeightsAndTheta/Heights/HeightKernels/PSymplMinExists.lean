import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplMinExists

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Simplify using `only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qf_smul (G : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) : qf G (c • x) = c ^ 2 * qf G x := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/- English proof (translation)
The claim follows from `continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)`.
-/
theorem continuous_qf (G : Matrix ι ι ℝ) : Continuous (qf G) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/- English proof (translation)
Take `⟨i₀⟩` from `‹Nonempty ι›`. Establish `hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < qf G x` using `fun x hx => by`. Simplify `hG.dotProduct_mulVec_pos hx` using `[qf]`. Establish `hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1)` using `isCompact_sphere 0 1`. Establish `hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty` using `⟨Pi.single i₀ 1, by simp [Pi.norm_single]⟩`.

Take `⟨u, hu, hmin⟩` from `hK.exists_isMinOn hne (continuous_qf G).continuousOn`. Use `⟨qf G u, hpos u ?_, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hu`. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Simplify using `[qf]`. Establish `hn : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Establish `hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`.

Establish `h1 : qf G u ≤ qf G (‖x‖⁻¹ • x)` using `isMinOn_iff.mp hmin _ hy`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[qf_smul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_lower [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : ι → ℝ, μ * ‖x‖ ^ 2 ≤ qf G x := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < qf G x := fun x hx => by
    simpa [qf] using hG.dotProduct_mulVec_pos hx
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨Pi.single i₀ 1, by simp [Pi.norm_single]⟩
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne (continuous_qf G).continuousOn
  refine ⟨qf G u, hpos u ?_, fun x => ?_⟩
  · rintro rfl
    simp at hu
  · by_cases hx : x = 0
    · subst hx
      simp [qf]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : qf G u ≤ qf G (‖x‖⁻¹ • x) := isMinOn_iff.mp hmin _ hy
      calc qf G u * ‖x‖ ^ 2 ≤ qf G (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := by gcongr
        _ = qf G x := by
          rw [qf_smul]
          field_simp

end PSymplMinExists

/- English proof (translation)
Introduce `ι _ _ _ G hG`. Take `⟨μ, hμ, hlow⟩` from `PSymplMinExists.exists_lower G hG`. Take `⟨i₀⟩` from `‹Nonempty ι›`. Use `set v₀ : ι → ℤ := Pi.single i₀ 1 with hv₀def`. Use `set M₀ : ℝ := qf G (intVec v₀) with hM₀`.

Use `set R : ℤ := ⌈M₀ / μ⌉ with hR`. Use `set S : Set (ι → ℤ) := {v | v ≠ 0 ∧ qf G (intVec v) ≤ M₀} with hS`. Establish `hbox : S ⊆ Set.Icc (fun _ => -R) (fun _ => R)`. Introduce and unpack `v ⟨-, hq⟩`. Establish `hb : ∀ i, |(v i : ℝ)| ≤ M₀ / μ`.

Introduce `i`. Establish `hi : |(v i : ℝ)| ≤ ‖intVec v‖`. Use `norm_le_pi_norm (intVec v) i` as an intermediate fact. Simplify `this` using `[intVec, Real.norm_eq_abs]`. Establish `hsq : |(v i : ℝ)| ≤ |(v i : ℝ)| ^ 2`.

Break down `eq_or_ne (v i) 0 with h | h` into its components or cases. Simplify using `[h]`. Establish `h' : (1 : ℝ) ≤ |(v i : ℝ)|`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs h` after adjusting the coercions.

Use the polynomial consequences of the given equalities and inequalities. Establish `hsq2 : |(v i : ℝ)| ^ 2 ≤ ‖intVec v‖ ^ 2` using `pow_le_pow_left₀ (abs_nonneg _) hi 2`. Rewrite using `[le_div_iff₀ hμ]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : ∀ i, |v i| ≤ R`.

Introduce `i`. Establish `: ((|v i| : ℤ) : ℝ) ≤ (R : ℝ)`. Rewrite using `[Int.cast_abs]`. Conclude with `(hb i).trans (Int.le_ceil _)`. Conclude with `this` after adjusting the coercions.

Use `⟨fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Conclude with `(abs_le.mp (hc i)).1`. Conclude with `(abs_le.mp (hc i)).2`. Establish `hfin : S.Finite` using `(Set.finite_Icc _ _).subset hbox`. Establish `hv₀ : v₀ ∈ S`.

Use `⟨fun h => ?_, le_rfl⟩` and prove the remaining obligations. Use `congrFun h i₀` as an intermediate fact. Simplify using `[v₀] at this`. Take `⟨w, hwS, hwmin⟩` from `Set.exists_min_image S (fun v => qf G (intVec v)) hfin ⟨v₀, hv₀⟩`. Use `⟨qf G (intVec w), ⟨w, hwS.1, rfl⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `t ⟨v, hv, rfl⟩`. Distinguish the cases in `hvS : qf G (intVec v) ≤ M₀`. Conclude with `hwmin v ⟨hv, hvS⟩`. Conclude with `hwS.2.trans (le_of_lt (not_le.mp hvS))`.
-/
theorem SymplMinExists.proof (h1 : SymplQuadDiag.Statement) : SymplMinExists.Statement := by
  intro ι _ _ _ G hG
  obtain ⟨μ, hμ, hlow⟩ := PSymplMinExists.exists_lower G hG
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set v₀ : ι → ℤ := Pi.single i₀ 1 with hv₀def
  set M₀ : ℝ := qf G (intVec v₀) with hM₀
  set R : ℤ := ⌈M₀ / μ⌉ with hR
  set S : Set (ι → ℤ) := {v | v ≠ 0 ∧ qf G (intVec v) ≤ M₀} with hS
  have hbox : S ⊆ Set.Icc (fun _ => -R) (fun _ => R) := by
    rintro v ⟨-, hq⟩
    have hb : ∀ i, |(v i : ℝ)| ≤ M₀ / μ := by
      intro i
      have hi : |(v i : ℝ)| ≤ ‖intVec v‖ := by
        have := norm_le_pi_norm (intVec v) i
        simpa [intVec, Real.norm_eq_abs] using this
      have hsq : |(v i : ℝ)| ≤ |(v i : ℝ)| ^ 2 := by
        rcases eq_or_ne (v i) 0 with h | h
        · simp [h]
        · have h' : (1 : ℝ) ≤ |(v i : ℝ)| := by
            rw [← Int.cast_abs]
            exact_mod_cast Int.one_le_abs h
          nlinarith
      have hsq2 : |(v i : ℝ)| ^ 2 ≤ ‖intVec v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
      rw [le_div_iff₀ hμ]
      calc |(v i : ℝ)| * μ ≤ μ * ‖intVec v‖ ^ 2 := by nlinarith
        _ ≤ qf G (intVec v) := hlow _
        _ ≤ M₀ := hq
    have hc : ∀ i, |v i| ≤ R := by
      intro i
      have : ((|v i| : ℤ) : ℝ) ≤ (R : ℝ) := by
        rw [Int.cast_abs]
        exact (hb i).trans (Int.le_ceil _)
      exact_mod_cast this
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (abs_le.mp (hc i)).1
    · exact (abs_le.mp (hc i)).2
  have hfin : S.Finite := (Set.finite_Icc _ _).subset hbox
  have hv₀ : v₀ ∈ S := by
    refine ⟨fun h => ?_, le_rfl⟩
    have := congrFun h i₀
    simp [v₀] at this
  obtain ⟨w, hwS, hwmin⟩ := Set.exists_min_image S (fun v => qf G (intVec v)) hfin ⟨v₀, hv₀⟩
  refine ⟨qf G (intVec w), ⟨w, hwS.1, rfl⟩, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  by_cases hvS : qf G (intVec v) ≤ M₀
  · exact hwmin v ⟨hv, hvS⟩
  · exact hwS.2.trans (le_of_lt (not_le.mp hvS))

end GroundTheory.Heights₂.Heights
