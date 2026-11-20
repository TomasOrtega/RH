import Mathlib

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace GlobalTheory.IntegerUnitBound

open scoped Classical in

/- English proof (translation)
Set `B` to `(basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)`. Use `⟨∑ i, ‖B i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun v => ?_⟩` and prove the remaining obligations. Establish `hmem : -((ZSpan.floor B v : logSpace E)) ∈ unitLattice E`. Rewrite using `[← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice E) (basisUnitLattice E)]`. Conclude with `neg_mem (ZSpan.floor B v).2`.

Take `⟨x, -, hx⟩` from `Submodule.mem_map.1 hmem`. Use `⟨Additive.toMul x, fun w => ?_⟩` and prove the remaining obligations. Establish `hsum : v + logEmbedding E (Additive.ofMul (Additive.toMul x)) = ZSpan.fract B v`. Establish `hx' : logEmbedding E x = -((ZSpan.floor B v : logSpace E))` using `hx`. Rewrite using `[ofMul_toMul, hx', ZSpan.fract_apply, sub_eq_add_neg]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.norm_eq_abs, Pi.add_apply]`. Use `_ ≤ ‖v + logEmbedding E (Additive.ofMul (Additive.toMul x))‖ := norm_le_pi_norm _ w`. Use `_ = ‖ZSpan.fract B v‖ := by rw [hsum]`. Use `_ ≤ ∑ i, ‖B i‖ := ZSpan.norm_fract_le B v`.
-/
theorem exists_unit_norm_add_le (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : logSpace E, ∃ u : (𝓞 E)ˣ,
      ∀ w, |v w + logEmbedding E (Additive.ofMul u) w| ≤ C := by
  let B := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun v => ?_⟩

  have hmem : -((ZSpan.floor B v : logSpace E)) ∈ unitLattice E := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice E) (basisUnitLattice E)]
    exact neg_mem (ZSpan.floor B v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨Additive.toMul x, fun w => ?_⟩
  have hsum : v + logEmbedding E (Additive.ofMul (Additive.toMul x)) = ZSpan.fract B v := by
    have hx' : logEmbedding E x = -((ZSpan.floor B v : logSpace E)) := hx
    rw [ofMul_toMul, hx', ZSpan.fract_apply, sub_eq_add_neg]
  calc |v w + logEmbedding E (Additive.ofMul (Additive.toMul x)) w|
      = ‖(v + logEmbedding E (Additive.ofMul (Additive.toMul x))) w‖ := by
        rw [Real.norm_eq_abs, Pi.add_apply]
    _ ≤ ‖v + logEmbedding E (Additive.ofMul (Additive.toMul x))‖ := norm_le_pi_norm _ w
    _ = ‖ZSpan.fract B v‖ := by rw [hsum]
    _ ≤ ∑ i, ‖B i‖ := ZSpan.norm_fract_le B v

open scoped Classical in

/- English proof (translation)
Take `⟨C₁, hC₁, hC⟩` from `exists_unit_norm_add_le E`. Use `⟨Fintype.card (InfinitePlace E) * C₁, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hC (fun w => (mult w.1 : ℝ) * t w.1)`. Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `hoff : ∀ w : {w : InfinitePlace E // w ≠ w₀}, |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| ≤ C₁`.

Introduce `w`. Establish `h` using `hu w`. Rewrite `h` using `[logEmbedding_component]`. Rewrite using `[mul_add]` and apply the resulting hypothesis. Establish `hone : ∀ w : InfinitePlace E, |t w + Real.log (w (u : E))| ≤ |(mult w : ℝ) * (t w + Real.log (w (u : E)))|`.

Introduce `w`. Rewrite using `[abs_mul, abs_of_pos (Nat.cast_pos.2 mult_pos : (0 : ℝ) < mult w)]`. Conclude with `le_mul_of_one_le_left (abs_nonneg _) one_le_mult`. Establish `hcard : C₁ ≤ Fintype.card (InfinitePlace E) * C₁`. Establish `h : (1 : ℝ) ≤ Fintype.card (InfinitePlace E)` using `by exact_mod_cast Fintype.card_pos`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `w`. Distinguish the cases in `hw : w = w₀`. Substitute `hw` using the available equality. Establish `htot : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w + Real.log (w (u : E))) = 0`.

Simplify using `only [mul_add, Finset.sum_add_distrib, ht, sum_mult_mul_log, add_zero]`. Rewrite `htot` using `[Fintype.sum_eq_add_sum_subtype_ne _ w₀]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[eq_neg_of_add_eq_zero_left htot, abs_neg]`. Use `_ ≤ ∑ w : {w : InfinitePlace E // w ≠ w₀}, |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| := Finset.abs_sum_le_sum_abs _ _`.

Use `_ ≤ ∑ _w : {w : InfinitePlace E // w ≠ w₀}, C₁ := Finset.sum_le_sum fun w _ => hoff w`. Use `_ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * C₁ := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `_ ≤ Fintype.card (InfinitePlace E) * C₁ := by gcongr`. Conclude with `Fintype.card_subtype_le _` after adjusting the coercions.

Conclude with `(hone w).trans ((hoff ⟨w, hw⟩).trans hcard)`.
-/
theorem exists_unit_of_sum_eq_zero (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ t : InfinitePlace E → ℝ, ∑ w, (mult w : ℝ) * t w = 0 → ∃ u : (𝓞 E)ˣ,
      ∀ w : InfinitePlace E, |t w + Real.log (w (u : E))| ≤ C := by
  obtain ⟨C₁, hC₁, hC⟩ := exists_unit_norm_add_le E
  refine ⟨Fintype.card (InfinitePlace E) * C₁, fun t ht => ?_⟩
  obtain ⟨u, hu⟩ := hC (fun w => (mult w.1 : ℝ) * t w.1)
  refine ⟨u, ?_⟩

  have hoff : ∀ w : {w : InfinitePlace E // w ≠ w₀},
      |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| ≤ C₁ := by
    intro w
    have h := hu w
    rw [logEmbedding_component] at h
    rwa [mul_add]

  have hone : ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E))| ≤ |(mult w : ℝ) * (t w + Real.log (w (u : E)))| := by
    intro w
    rw [abs_mul, abs_of_pos (Nat.cast_pos.2 mult_pos : (0 : ℝ) < mult w)]
    exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult
  have hcard : C₁ ≤ Fintype.card (InfinitePlace E) * C₁ := by
    have h : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    nlinarith
  intro w
  by_cases hw : w = w₀
  ·
    subst hw
    have htot : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w + Real.log (w (u : E))) = 0 := by
      simp only [mul_add, Finset.sum_add_distrib, ht, sum_mult_mul_log, add_zero]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at htot
    calc |t w₀ + Real.log (w₀ (u : E))|
        ≤ |(mult w₀ : ℝ) * (t w₀ + Real.log (w₀ (u : E)))| := hone w₀
      _ = |∑ w : {w : InfinitePlace E // w ≠ w₀}, (mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| := by
        rw [eq_neg_of_add_eq_zero_left htot, abs_neg]
      _ ≤ ∑ w : {w : InfinitePlace E // w ≠ w₀}, |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : {w : InfinitePlace E // w ≠ w₀}, C₁ := Finset.sum_le_sum fun w _ => hoff w
      _ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * C₁ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card (InfinitePlace E) * C₁ := by
        gcongr
        exact_mod_cast Fintype.card_subtype_le _
  · exact (hone w).trans ((hoff ⟨w, hw⟩).trans hcard)

/- English proof (translation)
The claim follows from `|t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + (n : ℝ)| ≤ R := by classical obtain ⟨C, hC⟩ := exists_unit_of_sum_eq_zero E refine ⟨C + 1, fun t => ?_⟩ have hmpos : 0 < ∑ w : InfinitePlace E, (mult w : ℝ) := Finset.sum_pos (fun w _ => Nat.cast_pos.2 mult_pos) Finset.univ_non …`.
-/
theorem exists_unit_int_abs_le (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + (n : ℝ)| ≤ R := by
  classical
  obtain ⟨C, hC⟩ := exists_unit_of_sum_eq_zero E
  refine ⟨C + 1, fun t => ?_⟩

  have hmpos : 0 < ∑ w : InfinitePlace E, (mult w : ℝ) :=
    Finset.sum_pos (fun w _ => Nat.cast_pos.2 mult_pos) Finset.univ_nonempty
  set s : ℝ := (∑ w : InfinitePlace E, (mult w : ℝ) * t w) / ∑ w : InfinitePlace E, (mult w : ℝ) with hs
  have hms : (∑ w : InfinitePlace E, (mult w : ℝ)) * s = ∑ w : InfinitePlace E, (mult w : ℝ) * t w := by
    rw [hs]
    field_simp
  have hsum : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w - s) = 0 := by
    rw [Finset.sum_congr rfl fun w _ => mul_sub (mult w : ℝ) (t w) s, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hms, sub_self]
  obtain ⟨u, hu⟩ := hC (fun w => t w - s) hsum

  refine ⟨u, -⌊s⌋, fun w => ?_⟩
  have h1 := abs_le.1 (hu w)
  have h2 := Int.fract_nonneg s
  have h3 := Int.fract_lt_one s
  have hcoe : algebraMap (𝓞 E) E (u : 𝓞 E) = (u : E) := rfl
  have heq : t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + ((-⌊s⌋ : ℤ) : ℝ) =
      (t w - s + Real.log (w (u : E))) + Int.fract s := by
    rw [hcoe, Int.fract]
    push_cast
    ring
  rw [heq, abs_le]
  constructor <;> linarith [h1.1, h1.2]

end GlobalTheory.IntegerUnitBound
