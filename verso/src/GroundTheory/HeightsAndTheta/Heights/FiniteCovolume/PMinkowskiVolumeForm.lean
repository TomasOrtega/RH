import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Submodule

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

/- English proof (translation)
Introduce `o b lam hlam hmin`. Set `_ : MeasurableSpace V` to `borel V`. Establish `_ : BorelSpace V` using `⟨rfl⟩`. Establish `hd : finrank ℝ V = d` using `Fact.out`. Establish `hcomb : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖`.

Introduce `x hx hx0`. Take `⟨z, rfl⟩` from `(mem_span_range_iff_exists_fun ℤ).1 hx`. Establish `hz : z ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx0`.

Simplify `hmin z hz` using `[← Int.cast_smul_eq_zsmul ℝ]`. Establish `hdisc : DiscreteTopology (span ℤ (Set.range b))` using `DiscreteTopology.of_forall_le_norm hlam fun x hx => hcomb x x.2 (by simpa using hx)`. Establish `hZ : LinearIndependent ℤ b`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `z hz`.

Assume the negation of the conclusion as `hne`. Establish `hz' : z ≠ 0` using `fun h => hne (fun i => by simp [h])`. Establish `h1` using `hmin z hz'`. Establish `h2 : ∑ i, (z i : ℝ) • b i = 0` using `by simpa [Int.cast_smul_eq_zsmul] using hz`. Rewrite `h1` using `[h2, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR : LinearIndependent ℝ b`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc, Set.finrank, finrank_span_eq_card hZ]`. Establish `hcard : Fintype.card (Fin d) = finrank ℝ V` using `by simp [hd]`. Set `B : Basis (Fin d) ℝ V` to `Basis.mk hR (hR.span_eq_top_of_card_eq_finrank' hcard).ge`.

Establish `hB : ⇑B = b` using `Basis.coe_mk _ _`. Establish `hF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b|`. Rewrite using `[measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B volume), ← o.measure_eq_volume, AlternatingMap.measure_parallelepiped, hB]`. Set `e : OrthonormalBasis (Fin d) ℝ V` to `(stdOrthonormalBasis ℝ V).reindex (finCongr hd)`. Use `set σ : ℝ := lam / Real.sqrt d with hσ`.

Establish `hσ0 : 0 ≤ σ` using `div_nonneg hlam.le (Real.sqrt_nonneg _)`. Set `φ : V →ₗ[ℝ] (Fin d → ℝ)` to `(WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ∘ₗ e.repr.toLinearEquiv.toLinearMap`. Set `P : Set (Fin d → ℝ)` to `Set.univ.pi fun _ => Set.Ioo (-σ) σ`. Set `s : Set V` to `φ ⁻¹' P`. Establish `hs_mem : ∀ v, v ∈ s ↔ ∀ i, |e.repr v i| < σ`.

Introduce `v`. Simplify using `only [s, P, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]`. Both sides reduce to the same expression. Establish `hsymm : ∀ x ∈ s, -x ∈ s`. Introduce `x hx`.

Rewrite `hx`, the goal using `[hs_mem]`. Introduce `i`. Simplify using `using hx i`. Establish `hconv : Convex ℝ s` using `(convex_pi fun _ _ => convex_Ioo _ _).linear_preimage φ`. Establish `hvol : volume s = ENNReal.ofReal (2 * σ) ^ d`.

Establish `hmp : MeasurePreserving (fun v : V => WithLp.ofLp (e.repr v)) volume volume` using `(PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr`. Rewrite using `[show s = (fun v : V => WithLp.ofLp (e.repr v)) ⁻¹' P from rfl, hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Establish `hlt' : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ V < volume s`. Rewrite using `[hd]`. Establish `h : ENNReal.ofReal (|o.volumeForm b| * 2 ^ d) < ENNReal.ofReal ((2 * σ) ^ d)`. Rewrite using `[ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mul_pow, mul_comm]`.

Conclude with `mul_lt_mul_of_pos_left hlt (by positivity)`. Rewrite `h` using `[ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (mul_nonneg zero_le_two hσ0), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← hF, ← hvol]`. Then use the resulting hypothesis. Establish `hcount : Countable (span ℤ (Set.range B)).toAddSubgroup`. Express the relevant statement in the definitionally equal form `Countable (span ℤ (Set.range B))`. Use `infer_instance`.

Take `⟨⟨x, hxL⟩, hx0, hxs⟩` from `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (ZSpan.isAddFundamentalDomain' B volume) hsymm hconv hlt'`. Establish `hx0' : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx0 rfl`. Establish `h1 : lam ≤ ‖x‖` using `hcomb x (by rw [← hB]; exact hxL) hx0'`.

Establish `h2 : ‖x‖ < lam`. Rewrite `hxs` using `[hs_mem]`. Break down `Nat.eq_zero_or_pos d with hd0 | hdpos` into its components or cases. Conclude with `absurd (@Subsingleton.elim _ (finrank_zero_iff.1 (hd.trans hd0)) x 0) hx0'`. Establish `hσpos : 0 < σ` using `div_pos hlam (Real.sqrt_pos.2 (by exact_mod_cast hdpos))`.

Establish `hsq : (d : ℝ) * σ ^ 2 = lam ^ 2`. Rewrite using `[hσ, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← e.repr.norm_map, EuclideanSpace.norm_eq]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.sqrt_lt_sqrt (by positivity)` to reduce the goal to its premises. Apply `Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩)` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Real.norm_eq_abs, sq_lt_sq, abs_of_pos hσpos, abs_abs]`. Conclude with `hxs i`.

Use `_ = lam := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq, Real.sqrt_sq hlam.le]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem MinkowskiVolumeForm.proof : MinkowskiVolumeForm.Statement V d := by
  classical
  intro o b lam hlam hmin
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hd : finrank ℝ V = d := Fact.out

  have hcomb : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨z, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hz : z ≠ 0 := by
      rintro rfl
      simp at hx0
    simpa [← Int.cast_smul_eq_zsmul ℝ] using hmin z hz
  have hdisc : DiscreteTopology (span ℤ (Set.range b)) :=
    DiscreteTopology.of_forall_le_norm hlam fun x hx => hcomb x x.2 (by simpa using hx)
  have hZ : LinearIndependent ℤ b := by
    rw [Fintype.linearIndependent_iff]
    intro z hz
    by_contra hne
    have hz' : z ≠ 0 := fun h => hne (fun i => by simp [h])
    have h1 := hmin z hz'
    have h2 : ∑ i, (z i : ℝ) • b i = 0 := by simpa [Int.cast_smul_eq_zsmul] using hz
    rw [h2, norm_zero] at h1
    linarith
  have hR : LinearIndependent ℝ b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc,
      Set.finrank, finrank_span_eq_card hZ]
  have hcard : Fintype.card (Fin d) = finrank ℝ V := by simp [hd]
  let B : Basis (Fin d) ℝ V := Basis.mk hR (hR.span_eq_top_of_card_eq_finrank' hcard).ge
  have hB : ⇑B = b := Basis.coe_mk _ _

  have hF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |o.volumeForm b| := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped B volume), ← o.measure_eq_volume,
      AlternatingMap.measure_parallelepiped, hB]

  let e : OrthonormalBasis (Fin d) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
  set σ : ℝ := lam / Real.sqrt d with hσ
  have hσ0 : 0 ≤ σ := div_nonneg hlam.le (Real.sqrt_nonneg _)
  let φ : V →ₗ[ℝ] (Fin d → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap ∘ₗ e.repr.toLinearEquiv.toLinearMap
  let P : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ioo (-σ) σ
  let s : Set V := φ ⁻¹' P
  have hs_mem : ∀ v, v ∈ s ↔ ∀ i, |e.repr v i| < σ := by
    intro v
    simp only [s, P, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]
    rfl
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs_mem] at hx ⊢
    intro i
    simpa using hx i
  have hconv : Convex ℝ s := (convex_pi fun _ _ => convex_Ioo _ _).linear_preimage φ
  have hvol : volume s = ENNReal.ofReal (2 * σ) ^ d := by
    have hmp : MeasurePreserving (fun v : V => WithLp.ofLp (e.repr v)) volume volume :=
      (PiLp.volume_preserving_ofLp (Fin d)).comp e.measurePreserving_repr
    rw [show s = (fun v : V => WithLp.ofLp (e.repr v)) ⁻¹' P from rfl,
      hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  by_contra hlt
  push Not at hlt
  have hlt' : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ V < volume s := by
    rw [hd]
    have h : ENNReal.ofReal (|o.volumeForm b| * 2 ^ d) < ENNReal.ofReal ((2 * σ) ^ d) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), mul_pow, mul_comm]
      exact mul_lt_mul_of_pos_left hlt (by positivity)
    rwa [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (mul_nonneg zero_le_two hσ0),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← hF, ← hvol] at h
  have hcount : Countable (span ℤ (Set.range B)).toAddSubgroup := by
    change Countable (span ℤ (Set.range B))
    infer_instance
  obtain ⟨⟨x, hxL⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' B volume) hsymm hconv hlt'
  have hx0' : x ≠ 0 := by
    rintro rfl
    exact hx0 rfl
  have h1 : lam ≤ ‖x‖ := hcomb x (by rw [← hB]; exact hxL) hx0'
  have h2 : ‖x‖ < lam := by
    rw [hs_mem] at hxs
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exact absurd (@Subsingleton.elim _ (finrank_zero_iff.1 (hd.trans hd0)) x 0) hx0'
    · have hσpos : 0 < σ := div_pos hlam (Real.sqrt_pos.2 (by exact_mod_cast hdpos))
      have hsq : (d : ℝ) * σ ^ 2 = lam ^ 2 := by
        rw [hσ, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        field_simp
      rw [← e.repr.norm_map, EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ i, ‖e.repr x i‖ ^ 2) < Real.sqrt (∑ _i : Fin d, σ ^ 2) := by
            apply Real.sqrt_lt_sqrt (by positivity)
            apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hdpos⟩⟩)
            intro i _
            rw [Real.norm_eq_abs, sq_lt_sq, abs_of_pos hσpos, abs_abs]
            exact hxs i
        _ = lam := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
              Real.sqrt_sq hlam.le]
  linarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
