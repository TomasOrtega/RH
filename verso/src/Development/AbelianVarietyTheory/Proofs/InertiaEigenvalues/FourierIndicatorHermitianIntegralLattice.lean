import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Introduce `F E _ _ _ _ hU A ψ hψ r j B hB hO _hC μ hμ y`. Use `haveI := hU.ultraE`. Use `set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ`. Establish `key : ∀ z : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * z)) = 1) ↔ ‖z‖ ≤ 1` using `((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2`. Establish `hmem_add : ∀ a x, a ∈ Λ → (a + x ∈ Λ ↔ x ∈ Λ)`.

Introduce `a x ha`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Establish `e1 : j x i = j (a + x) i + -(j a i)` using `by simp`. Rewrite using `[e1]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i) (by rw [norm_neg]; exact ha i))`. Introduce `h i`. Rewrite using `[map_add, Pi.add_apply]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (h i))`. Establish `hBadd : ∀ a x, B (a + x) y = B a y * B x y`.

Introduce `a x`. Rewrite using `[hB, hB, hB, map_add, star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul]`. Use `haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L`. Unfold `fourB`. Distinguish the cases in `hy : y ∈ Λ`.

Establish `h1 : ∀ x, Set.indicator Λ 1 x * B x y = Set.indicator Λ (fun _ => (1:ℂ)) x`. Introduce `x`. Distinguish the cases in `hx : x ∈ Λ`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, hB]`. Simplify using `only [dotProduct, Pi.star_apply, map_sum]`.

Use `Finset.sum_induction _ (fun t => ψ t = 1) (fun u v hu hv => by` and prove the remaining obligations. Rewrite using `[AddChar.map_add_eq_mul, hu, hv, one_mul]) (AddChar.map_zero_eq_one ψ) fun i _ => ?_`. Conclude with `(key (j y i)).2 (hy i) _ (by rw [hU.norm_star]; exact hx i)`. Simplify using `[hx]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[integral_indicator_const _ hO.measurableSet, Set.indicator_of_mem hy, Pi.one_apply, mul_one]`. Simplify using `[Measure.real]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ¬ ‖j y i‖ ≤ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hy h`. Choose the witnesses or unpack the hypotheses as in `⟨e, he, hne⟩ : ∃ e : E, ‖e‖ ≤ 1 ∧ ψ (Algebra.trace F E (e * j y i)) ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hi ((key _).1 h)`.

Use `set a := j.symm (Pi.single i (star e)) with ha_def`. Establish `hja : j a = Pi.single i (star e)` using `by simp [ha_def]`. Establish `ha : a ∈ Λ`. Introduce `k`. Rewrite using `[hja]`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[hU.norm_star, he]`. Simplify using `[Pi.single_eq_of_ne hk]`. Establish `hst : star (Pi.single i (star e) : Fin r → E) = Pi.single i e`.

Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hk]`.

Establish `hBa : B a y = ψ (Algebra.trace F E (e * j y i))`. Rewrite using `[hB, hja, hst, single_dotProduct]`. Establish `hint : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = B a y * ∫ x, Set.indicator Λ 1 x * B x y ∂μ`. Rewrite using `[← integral_const_mul]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use extensionality with `x`. Rewrite using `[hBadd]`. Distinguish the cases in `hx : x ∈ Λ`. Rewrite using `[Set.indicator_of_mem ((hmem_add a x ha).2 hx), Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hx' : a + x ∉ Λ` using `fun h => hx ((hmem_add a x ha).1 h)`. Simplify using `[hx, hx']`. Establish `h0 : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0`. Establish `: (1 - B a y) * ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0`.

Rewrite using `[sub_mul, one_mul, ← hint, sub_self]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd (by rw [hBa] at h; exact (sub_eq_zero.1 h).symm) hne`. Conclude with `h`. Rewrite using `[h0]`.

Simplify using `[hy]`.
-/
theorem fourB_indicator_intLattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  intro F E _ _ _ _ hU A ψ hψ r j B hB hO _hC μ hμ y
  haveI := hU.ultraE
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  have key : ∀ z : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * z)) = 1) ↔ ‖z‖ ≤ 1 :=
    ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hmem_add : ∀ a x, a ∈ Λ → (a + x ∈ Λ ↔ x ∈ Λ) := by
    intro a x ha
    constructor
    · intro h i
      have e1 : j x i = j (a + x) i + -(j a i) := by simp
      rw [e1]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i) (by rw [norm_neg]; exact ha i))
    · intro h i
      rw [map_add, Pi.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (h i))
  have hBadd : ∀ a x, B (a + x) y = B a y * B x y := by
    intro a x
    rw [hB, hB, hB, map_add, star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul]
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  unfold fourB
  by_cases hy : y ∈ Λ
  · have h1 : ∀ x, Set.indicator Λ 1 x * B x y = Set.indicator Λ (fun _ => (1:ℂ)) x := by
      intro x
      by_cases hx : x ∈ Λ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, hB]
        simp only [dotProduct, Pi.star_apply, map_sum]
        refine Finset.sum_induction _ (fun t => ψ t = 1) (fun u v hu hv => by
          rw [AddChar.map_add_eq_mul, hu, hv, one_mul]) (AddChar.map_zero_eq_one ψ) fun i _ => ?_
        exact (key (j y i)).2 (hy i) _ (by rw [hU.norm_star]; exact hx i)
      · simp [hx]
    simp_rw [h1]
    rw [integral_indicator_const _ hO.measurableSet, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    simp [Measure.real]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ ‖j y i‖ ≤ 1 := by
      by_contra h
      push_neg at h
      exact hy h
    obtain ⟨e, he, hne⟩ : ∃ e : E, ‖e‖ ≤ 1 ∧ ψ (Algebra.trace F E (e * j y i)) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hi ((key _).1 h)
    set a := j.symm (Pi.single i (star e)) with ha_def
    have hja : j a = Pi.single i (star e) := by simp [ha_def]
    have ha : a ∈ Λ := by
      intro k
      rw [hja]
      by_cases hk : k = i
      · subst hk; simp [hU.norm_star, he]
      · simp [Pi.single_eq_of_ne hk]
    have hst : star (Pi.single i (star e) : Fin r → E) = Pi.single i e := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have hBa : B a y = ψ (Algebra.trace F E (e * j y i)) := by
      rw [hB, hja, hst, single_dotProduct]
    have hint : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = B a y * ∫ x, Set.indicator Λ 1 x * B x y ∂μ := by
      rw [← integral_const_mul]
      calc ∫ x, Set.indicator Λ 1 x * B x y ∂μ
          = ∫ x, Set.indicator Λ 1 (a + x) * B (a + x) y ∂μ :=
            (integral_add_left_eq_self (fun x => Set.indicator Λ 1 x * B x y) a).symm
        _ = ∫ x, B a y * (Set.indicator Λ 1 x * B x y) ∂μ := by
            congr 1; ext x
            rw [hBadd]
            by_cases hx : x ∈ Λ
            · rw [Set.indicator_of_mem ((hmem_add a x ha).2 hx), Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply]; ring
            · have hx' : a + x ∉ Λ := fun h => hx ((hmem_add a x ha).1 h)
              simp [hx, hx']
    have h0 : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
      have : (1 - B a y) * ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← hint, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by rw [hBa] at h; exact (sub_eq_zero.1 h).symm) hne
      · exact h
    rw [h0]
    simp [hy]

end GlobalTheory.JR
