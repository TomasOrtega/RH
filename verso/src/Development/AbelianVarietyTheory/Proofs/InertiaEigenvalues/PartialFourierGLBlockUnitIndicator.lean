import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourGUnit

variable {F : Type} [NontriviallyNormedField F]

/- English proof (translation)
Use `set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef`. Establish `hS : S = Set.univ.pi fun _ => Metric.closedBall (0 : F) 1`. Use extensionality with `x`. Simplify using `[S, Metric.mem_closedBall]`. Establish `hSm : MeasurableSet S` using `hS ▸ MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)`.

Distinguish the cases in `hv : v ∈ S`. Rewrite using `[Set.indicator_of_mem hv, integral_indicator hSm, setIntegral_congr_fun hSm (g := fun _ => (1 : ℂ)) (fun x hx => ?_), setIntegral_const]`. Rewrite using `[Measure.real, hS, Measure.pi_pi]`. Simplify using `[hvol]`. Apply `hψ.1` to reduce the goal to its premises.

Rewrite using `[dotProduct]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hx i) (norm_nonneg _) (hv i)`.

Rewrite using `[Set.indicator_of_notMem hv]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, 1 < ‖v i‖ := by`. Simplify using `only [S, Set.mem_setOf_eq, not_forall, not_le] at hv`. Conclude with `hv`. Take `⟨x₀, hx₀, hx₀'⟩` from `hψ.2`.

Establish `hvi : v i ≠ 0`. Introduce `h`. Rewrite `hi` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set z₀ : Fin r → F := Pi.single i (x₀ * (v i)⁻¹) with hz₀def`.

Establish `hz₀ : z₀ ∈ S`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[hz₀def, Pi.single_eq_same]`.

Apply `hx₀'` to reduce the goal to its premises. Rewrite using `[norm_inv]`. Conclude with `inv_lt_one_of_one_lt₀ hi`. Rewrite using `[hz₀def, Pi.single_eq_of_ne hj, norm_zero]`. Conclude with `zero_le_one`.

Establish `hχ : ψ (z₀ ⬝ᵥ v) ≠ 1`. Rewrite using `[hz₀def, single_dotProduct, mul_assoc, inv_mul_cancel₀ hvi, mul_one]`. Conclude with `hx₀`. Establish `hadd : ∀ a b : Fin r → F, a ∈ S → b ∈ S → a + b ∈ S` using `fun a b ha hb i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))`. Establish `key : ∀ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) (z + z₀) = S.indicator (fun x => ψ (x ⬝ᵥ v)) z * ψ (z₀ ⬝ᵥ v)`.

Introduce `z`. Distinguish the cases in `hz : z ∈ S`. Rewrite using `[Set.indicator_of_mem (hadd _ _ hz hz₀), Set.indicator_of_mem hz, add_dotProduct, AddChar.map_add_eq_mul]`. Establish `hneg : -z₀ ∈ S` using `fun j => by rw [Pi.neg_apply, norm_neg]; exact hz₀ j`. Establish `: z + z₀ ∉ S` using `fun h => hz (by simpa using hadd _ _ h hneg)`.

Rewrite using `[Set.indicator_of_notMem this, Set.indicator_of_notMem hz, zero_mul]`. Establish `h` using `integral_add_right_eq_self (μ := Measure.pi fun _ : Fin r => μ) (fun z => S.indicator (fun x => ψ (x ⬝ᵥ v)) z) z₀`. Simplify using `only [key, integral_mul_const] at h`. Establish `h2 : (∫ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) z ∂(Measure.pi fun _ => μ)) * (ψ (z₀ ⬝ᵥ v) - 1) = 0`. Rewrite using `[mul_sub, mul_one, h, sub_self]`.

Break down `mul_eq_zero.mp h2 with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd (sub_eq_zero.mp h1) hχ`.
-/
theorem integral_ball_char {r : ℕ} [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F] [ProperSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) (v : Fin r → F) :
    ∫ x, {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => μ) =
      {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator 1 v := by
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  have hS : S = Set.univ.pi fun _ => Metric.closedBall (0 : F) 1 := by
    ext x; simp [S, Metric.mem_closedBall]
  have hSm : MeasurableSet S := hS ▸ MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv, integral_indicator hSm,
      setIntegral_congr_fun hSm (g := fun _ => (1 : ℂ)) (fun x hx => ?_), setIntegral_const]
    · rw [Measure.real, hS, Measure.pi_pi]
      simp [hvol]
    · apply hψ.1
      rw [dotProduct]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro i _
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hv i)
  · rw [Set.indicator_of_notMem hv]
    obtain ⟨i, hi⟩ : ∃ i, 1 < ‖v i‖ := by
      simp only [S, Set.mem_setOf_eq, not_forall, not_le] at hv; exact hv
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    have hvi : v i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; linarith
    set z₀ : Fin r → F := Pi.single i (x₀ * (v i)⁻¹) with hz₀def
    have hz₀ : z₀ ∈ S := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hz₀def, Pi.single_eq_same]
        apply hx₀'
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hi
      · rw [hz₀def, Pi.single_eq_of_ne hj, norm_zero]; exact zero_le_one
    have hχ : ψ (z₀ ⬝ᵥ v) ≠ 1 := by
      rw [hz₀def, single_dotProduct, mul_assoc, inv_mul_cancel₀ hvi, mul_one]
      exact hx₀
    have hadd : ∀ a b : Fin r → F, a ∈ S → b ∈ S → a + b ∈ S := fun a b ha hb i =>
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    have key : ∀ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) (z + z₀) =
        S.indicator (fun x => ψ (x ⬝ᵥ v)) z * ψ (z₀ ⬝ᵥ v) := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem (hadd _ _ hz hz₀), Set.indicator_of_mem hz, add_dotProduct,
          AddChar.map_add_eq_mul]
      · have hneg : -z₀ ∈ S := fun j => by rw [Pi.neg_apply, norm_neg]; exact hz₀ j
        have : z + z₀ ∉ S := fun h => hz (by simpa using hadd _ _ h hneg)
        rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hz, zero_mul]
    have h := integral_add_right_eq_self (μ := Measure.pi fun _ : Fin r => μ)
      (fun z => S.indicator (fun x => ψ (x ⬝ᵥ v)) z) z₀
    simp only [key, integral_mul_const] at h
    have h2 : (∫ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) z ∂(Measure.pi fun _ => μ)) * (ψ (z₀ ⬝ᵥ v) - 1) = 0 := by
      rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.mp h1) hχ

end GlobalTheory.JR.FourGUnit

namespace GlobalTheory.JR

open FourGUnit in

/- English proof (translation)
Introduce `F E _ _ _ _ U r M ψ hψ`. Use `letI := M.mF`. Use `haveI := M.bF`. Use `haveI := U.ultraF`. Use `haveI := U.lcF`.

Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI := M.haarF`. Use function extensionality and compare the values at `Y`. Take `⟨A, b, c, l⟩` from `Y`. Unfold `fourG`.

Use `set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef`. Use `set T : Set (Gl r F) := {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} with hTdef`. Establish `hT : unitG r F = T.indicator 1` using `rfl`. Distinguish the cases in `hP : (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖l‖ ≤ 1`. Establish `hint : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = S.indicator (fun x => ψ (x ⬝ᵥ c)) b' * S.indicator (fun x => ψ (x ⬝ᵥ b)) c'`.

Introduce `b' c'`. Distinguish the cases in `hb' : b' ∈ S`. Distinguish the cases in `hc' : c' ∈ S`. Rewrite using `[hT, Set.indicator_of_mem (show (A, b', c', l) ∈ T from ⟨hP.1, hb', hc', hP.2⟩), Set.indicator_of_mem hb', Set.indicator_of_mem hc', Pi.one_apply, one_mul, AddChar.map_add_eq_mul, dotProduct_comm c b', mul_comm]`. Rewrite using `[hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hc' h.2.2.1), Set.indicator_of_notMem hc', zero_mul, mul_zero]`.

Rewrite using `[hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hb' h.2.1), Set.indicator_of_notMem hb', zero_mul, zero_mul]`. Establish `hball : ∀ v : Fin r → F, ∫ x, S.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => M.μF) = S.indicator 1 v` using `integral_ball_char M.μF M.volF ψ hψ`. Repeatedly rewrite using `[hint, integral_const_mul, hball, integral_mul_const, hball]`. Distinguish the cases in `hb : b ∈ S`. Distinguish the cases in `hc : c ∈ S`.

Rewrite using `[hT, Set.indicator_of_mem (show (A, b, c, l) ∈ T from ⟨hP.1, hb, hc, hP.2⟩), Set.indicator_of_mem hb, Set.indicator_of_mem hc]`. Simplify using the standard rewrite rules. Rewrite using `[hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hc h.2.2.1), Set.indicator_of_notMem hc, zero_mul]`. Rewrite using `[hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hb h.2.1), Set.indicator_of_notMem hb, mul_zero]`. Establish `h0 : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = 0`.

Introduce `b' c'`. Rewrite using `[hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩), zero_mul]`. Repeatedly rewrite using `[h0, integral_zero]`. Rewrite using `[hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩)]`.
-/
theorem fourG_unitG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    fourG M ψ (unitG r F) = unitG r F := by
  intro F E _ _ _ _ U r M ψ hψ
  letI := M.mF
  haveI := M.bF
  haveI := U.ultraF
  haveI := U.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI := M.haarF
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  unfold fourG
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  set T : Set (Gl r F) := {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧
    ‖Y.2.2.2‖ ≤ 1} with hTdef
  have hT : unitG r F = T.indicator 1 := rfl
  by_cases hP : (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖l‖ ≤ 1
  · have hint : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') =
        S.indicator (fun x => ψ (x ⬝ᵥ c)) b' * S.indicator (fun x => ψ (x ⬝ᵥ b)) c' := by
      intro b' c'
      by_cases hb' : b' ∈ S
      · by_cases hc' : c' ∈ S
        · rw [hT, Set.indicator_of_mem (show (A, b', c', l) ∈ T from ⟨hP.1, hb', hc', hP.2⟩),
            Set.indicator_of_mem hb', Set.indicator_of_mem hc', Pi.one_apply, one_mul,
            AddChar.map_add_eq_mul, dotProduct_comm c b', mul_comm]
        · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hc' h.2.2.1),
            Set.indicator_of_notMem hc', zero_mul, mul_zero]
      · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hb' h.2.1),
          Set.indicator_of_notMem hb', zero_mul, zero_mul]
    have hball : ∀ v : Fin r → F, ∫ x, S.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => M.μF) =
        S.indicator 1 v := integral_ball_char M.μF M.volF ψ hψ
    simp_rw [hint, integral_const_mul, hball, integral_mul_const, hball]
    by_cases hb : b ∈ S
    · by_cases hc : c ∈ S
      · rw [hT, Set.indicator_of_mem (show (A, b, c, l) ∈ T from ⟨hP.1, hb, hc, hP.2⟩),
          Set.indicator_of_mem hb, Set.indicator_of_mem hc]
        simp
      · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hc h.2.2.1),
          Set.indicator_of_notMem hc, zero_mul]
    · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hb h.2.1),
        Set.indicator_of_notMem hb, mul_zero]
  · have h0 : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = 0 := by
      intro b' c'
      rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩),
        zero_mul]
    simp_rw [h0, integral_zero]
    rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩)]

end GlobalTheory.JR
