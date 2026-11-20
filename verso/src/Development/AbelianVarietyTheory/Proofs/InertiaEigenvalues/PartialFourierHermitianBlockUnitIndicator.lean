import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.FourUnit

/- English proof (translation)
Establish `key : ∀ z, S.indicator φ (t + z) = φ t * S.indicator φ z`. Introduce `z`. Distinguish the cases in `hz : z ∈ S`. Rewrite using `[Set.indicator_of_mem ((hS z).2 hz), Set.indicator_of_mem hz, hφ]`. Rewrite using `[Set.indicator_of_notMem (fun h => hz ((hS z).1 h)), Set.indicator_of_notMem hz, mul_zero]`.

Establish `h` using `integral_add_left_eq_self (μ := μ) (S.indicator φ) t`. Rewrite `h` using `[key, integral_const_mul]`. Establish `h2 : (φ t - 1) * ∫ z, S.indicator φ z ∂μ = 0` using `by rw [sub_mul, h, one_mul, sub_self]`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h3) ht`.

Conclude with `h3`.
-/
theorem integral_indicator_char_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (S : Set G) (φ : G → ℂ)
    (hφ : ∀ a b, φ (a + b) = φ a * φ b) (t : G) (hS : ∀ z, t + z ∈ S ↔ z ∈ S) (ht : φ t ≠ 1) :
    ∫ z, S.indicator φ z ∂μ = 0 := by
  have key : ∀ z, S.indicator φ (t + z) = φ t * S.indicator φ z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem ((hS z).2 hz), Set.indicator_of_mem hz, hφ]
    · rw [Set.indicator_of_notMem (fun h => hz ((hS z).1 h)), Set.indicator_of_notMem hz, mul_zero]
  have h := integral_add_left_eq_self (μ := μ) (S.indicator φ) t
  simp_rw [key, integral_const_mul] at h
  have h2 : (φ t - 1) * ∫ z, S.indicator φ z ∂μ = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) ht
  · exact h3

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.
-/
theorem addChar_sum {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Use `haveI := hU.ultraE`. Rewrite using `[← norm_algebraMap' E, htr]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hU.norm_star]; simp)`.
-/
theorem norm_trace_le (hU : Unram F E) (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) (w : E) :
    ‖Algebra.trace F E w‖ ≤ ‖w‖ := by
  haveI := hU.ultraE
  rw [← norm_algebraMap' E, htr]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hU.norm_star]; simp)

/- English proof (translation)
Use `haveI := hU.ultraE`. Use `haveI := hU.ultraF`. Use `split_ifs with hy`. Rewrite using `[Set.indicator_congr (g := fun _ => (1 : ℂ)) (fun z hz => ?_)]`. Rewrite using `[integral_indicator measurableSet_closedBall, setIntegral_const]`.

Simplify using `[Measure.real, hvol]`. Apply `hψ.1` to reduce the goal to its premises. Use `(norm_trace_le hU htr _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hU.norm_star]`. Conclude with `mul_le_one₀ (mem_closedBall_zero_iff.1 hz) (norm_nonneg _) hy`.

Use `push_neg at hy`. Take `⟨x₀, hx₀, hx₀'⟩` from `hψ.2`. Take `⟨yF, hyF⟩` from `hU.unram y`. Take `⟨u, hu1, hu2⟩` from `hu`. Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy; linarith`.

Establish `hyF0 : yF ≠ 0` using `by rintro rfl; rw [hyF] at hy; simp at hy; linarith`. Establish `hx₀y : ‖x₀‖ ≤ ‖y‖`. Establish `h1 : ‖yF⁻¹‖ < 1` using `by rw [norm_inv, ← hyF]; exact inv_lt_one_of_one_lt₀ hy`. Establish `h2` using `hx₀' _ h1`. Rewrite `h2` using `[norm_mul, norm_inv, ← hyF]`.

Establish `hpos : 0 < ‖y‖` using `by linarith`. Rewrite `h2` using `[mul_inv_le_iff₀ hpos, one_mul]`. Then use the resulting hypothesis. Establish `htu : Algebra.trace F E u ≠ 0` using `by intro h; rw [h, norm_zero] at hu2; exact zero_ne_one hu2`. Use `set w : E := (x₀ / Algebra.trace F E u) • u with hw`. Establish `hTw : Algebra.trace F E w = x₀`.

Rewrite using `[hw, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ htu]`. Establish `hnw : ‖w‖ ≤ ‖y‖`. Rewrite using `[hw, norm_smul, norm_div, hu2, div_one]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) hu1).trans hx₀y`. Establish `hpos : 0 < ‖y‖` using `by linarith`.

Use `integral_indicator_char_eq_zero μ _ _ (fun a b => ?_) (star (w * y⁻¹)) (fun z => ?_) ?_` and prove the remaining obligations. Rewrite using `[star_add, add_mul, map_add, AddChar.map_add_eq_mul]`. Establish `ht : ‖star (w * y⁻¹)‖ ≤ 1`. Rewrite using `[hU.norm_star, norm_mul, norm_inv, mul_inv_le_iff₀ hpos, one_mul]`. Conclude with `hnw`.

Simplify using `only [mem_closedBall_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `IsUltrametricDist.norm_add_le_max (star (w * y⁻¹) + z) (-(star (w * y⁻¹)))` as an intermediate fact. Rewrite `this` using `[norm_neg, show star (w * y⁻¹) + z + -star (w * y⁻¹) = z by abel]`.

Conclude with `this.trans (max_le h ht)`. Introduce `h`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ht h)`. Simplify using `only [star_star]`. Rewrite using `[mul_assoc, inv_mul_cancel₀ hy0, mul_one, hTw]`.

Conclude with `hx₀`.
-/
theorem integral_ball_char (hU : Unram F E) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (hu : ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) (y : E) :
    ∫ z, (Metric.closedBall (0 : E) 1).indicator (fun z => ψ (Algebra.trace F E (star z * y))) z ∂μ =
      if ‖y‖ ≤ 1 then 1 else 0 := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  split_ifs with hy
  · rw [Set.indicator_congr (g := fun _ => (1 : ℂ)) (fun z hz => ?_)]
    · rw [integral_indicator measurableSet_closedBall, setIntegral_const]
      simp [Measure.real, hvol]
    · apply hψ.1
      refine (norm_trace_le hU htr _).trans ?_
      rw [norm_mul, hU.norm_star]
      exact mul_le_one₀ (mem_closedBall_zero_iff.1 hz) (norm_nonneg _) hy
  · push_neg at hy
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    obtain ⟨yF, hyF⟩ := hU.unram y
    obtain ⟨u, hu1, hu2⟩ := hu
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hyF0 : yF ≠ 0 := by rintro rfl; rw [hyF] at hy; simp at hy; linarith
    have hx₀y : ‖x₀‖ ≤ ‖y‖ := by
      have h1 : ‖yF⁻¹‖ < 1 := by rw [norm_inv, ← hyF]; exact inv_lt_one_of_one_lt₀ hy
      have h2 := hx₀' _ h1
      rw [norm_mul, norm_inv, ← hyF] at h2
      have hpos : 0 < ‖y‖ := by linarith
      rwa [mul_inv_le_iff₀ hpos, one_mul] at h2
    have htu : Algebra.trace F E u ≠ 0 := by intro h; rw [h, norm_zero] at hu2; exact zero_ne_one hu2
    set w : E := (x₀ / Algebra.trace F E u) • u with hw
    have hTw : Algebra.trace F E w = x₀ := by
      rw [hw, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ htu]
    have hnw : ‖w‖ ≤ ‖y‖ := by
      rw [hw, norm_smul, norm_div, hu2, div_one]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans hx₀y
    have hpos : 0 < ‖y‖ := by linarith
    refine integral_indicator_char_eq_zero μ _ _ (fun a b => ?_) (star (w * y⁻¹)) (fun z => ?_) ?_
    · rw [star_add, add_mul, map_add, AddChar.map_add_eq_mul]
    · have ht : ‖star (w * y⁻¹)‖ ≤ 1 := by
        rw [hU.norm_star, norm_mul, norm_inv, mul_inv_le_iff₀ hpos, one_mul]; exact hnw
      simp only [mem_closedBall_zero_iff]
      constructor
      · intro h
        have := IsUltrametricDist.norm_add_le_max (star (w * y⁻¹) + z) (-(star (w * y⁻¹)))
        rw [norm_neg, show star (w * y⁻¹) + z + -star (w * y⁻¹) = z by abel] at this
        exact this.trans (max_le h ht)
      · intro h
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ht h)
    · simp only [star_star]
      rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one, hTw]
      exact hx₀

/- English proof (translation)
Introduce `F E _ _ _ _ hU r M ψ hψ htr hu`. Use `letI := M.mE`. Use `haveI := M.bE`. Use `haveI := M.haarE`. Use `haveI := hU.lcE`.

Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Use function extensionality and compare the values at `X`. Simplify using `only [fourU]`. Distinguish the cases in `h0 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1`. Establish `hint : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) = ∏ i, (Metric.closedBall (0 : E) 1).indicator (fun z => ψ (Algebra.trace F E (star z * X.2.1 i))) (c i)`.

Introduce `c`. Distinguish the cases in `hc : ∀ i, ‖c i‖ ≤ 1`. Establish `e1 : unitU r F E (X.1, c, X.2.2) = 1`. Simplify using `only [unitU]; rw [Set.indicator_of_mem (by exact ⟨h0.1, hc, h0.2⟩)]; rfl`. Rewrite using `[e1, one_mul]`.

Simplify using `only [dotProduct, Pi.star_apply, map_sum, addChar_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hc i))]`. Use `push_neg at hc`. Take `⟨i, hi⟩` from `hc`.

Establish `e1 : unitU r F E (X.1, c, X.2.2) = 0`. Simplify using `only [unitU]`. Conclude with `Set.indicator_of_notMem (fun h => (not_le.2 hi) (h.2.1 i)) _`. Rewrite using `[e1, zero_mul]`. Use `(Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm` and prove the remaining obligations.

Conclude with `Set.indicator_of_notMem (fun h => (not_le.2 hi) (mem_closedBall_zero_iff.1 h)) _`. Repeatedly rewrite using `[hint]`. Rewrite using `[integral_fintype_prod_eq_prod]`. Repeatedly rewrite using `[integral_ball_char hU M.μE M.volE ψ hψ htr hu]`. Rewrite using `[Finset.prod_boole]`.

Simplify using `only [unitU, Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_univ, true_implies, Pi.one_apply]`. Simplify using `[h0.1, h0.2]`. Establish `e : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) = 0` using `fun c => by`. Simplify using `only [unitU]`. Conclude with `Set.indicator_of_notMem (fun h => h0 ⟨h.1, h.2.2⟩) _`.

Repeatedly rewrite using `[e, zero_mul, integral_zero]`.
-/
theorem fourU_unitU : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
    (∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) → fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ htr hu
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  funext X
  simp only [fourU]
  by_cases h0 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1
  · have hint : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) =
        ∏ i, (Metric.closedBall (0 : E) 1).indicator
          (fun z => ψ (Algebra.trace F E (star z * X.2.1 i))) (c i) := by
      intro c
      by_cases hc : ∀ i, ‖c i‖ ≤ 1
      · have e1 : unitU r F E (X.1, c, X.2.2) = 1 := by
          simp only [unitU]; rw [Set.indicator_of_mem (by exact ⟨h0.1, hc, h0.2⟩)]; rfl
        rw [e1, one_mul]
        simp only [dotProduct, Pi.star_apply, map_sum, addChar_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 (hc i))]
      · push_neg at hc
        obtain ⟨i, hi⟩ := hc
        have e1 : unitU r F E (X.1, c, X.2.2) = 0 := by
          simp only [unitU]
          exact Set.indicator_of_notMem (fun h => (not_le.2 hi) (h.2.1 i)) _
        rw [e1, zero_mul]
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        exact Set.indicator_of_notMem (fun h => (not_le.2 hi) (mem_closedBall_zero_iff.1 h)) _
    simp_rw [hint]
    rw [integral_fintype_prod_eq_prod]
    simp_rw [integral_ball_char hU M.μE M.volE ψ hψ htr hu]
    rw [Finset.prod_boole]
    simp only [unitU, Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_univ, true_implies, Pi.one_apply]
    simp [h0.1, h0.2]
  · have e : ∀ c : Fin r → E, unitU r F E (X.1, c, X.2.2) = 0 := fun c => by
      simp only [unitU]
      exact Set.indicator_of_notMem (fun h => h0 ⟨h.1, h.2.2⟩) _
    simp_rw [e, zero_mul, integral_zero]

end GlobalTheory.JR.FourUnit
