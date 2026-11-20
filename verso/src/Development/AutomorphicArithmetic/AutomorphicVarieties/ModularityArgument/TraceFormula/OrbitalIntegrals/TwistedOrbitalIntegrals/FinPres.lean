import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

noncomputable section

open MeasureTheory Topology

namespace UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ hμ θ hθ l hl hθl`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hl`. Establish `hpow : ∀ j : ℕ, Continuous (θ ^ j : Monoid.End G)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => exact continuous_id`. Consider the case `succ j ih`. Rewrite using `[pow_succ]`. Conclude with `ih.comp hθ`. Establish `h1 : ∀ x, (θ ^ m : Monoid.End G) (θ x) = x` using `fun x => by`.

Establish `: (θ ^ (m + 1) : Monoid.End G) x = x` using `by rw [hθl]; rfl`. Rewrite `this` using `[pow_succ]`. Conclude with `this`. Establish `h2 : ∀ x, θ ((θ ^ m : Monoid.End G) x) = x` using `fun x => by`. Establish `: (θ ^ (m + 1) : Monoid.End G) x = x` using `by rw [hθl]; rfl`.

Rewrite `this` using `[pow_succ']`. Conclude with `this`. Set `e : G ≃* G` to `{ toFun := θ, invFun := (θ ^ m : Monoid.End G), left_inv := h1, right_inv := h2, map_mul' := map_mul θ }`. Establish `hν : (Measure.map θ μ).IsHaarMeasure` using `MulEquiv.isHaarMeasure_map μ e hθ (hpow m)`. Take `⟨c, hc⟩ : ∃ c : NNReal, Measure.map θ μ = c • μ` from `⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.map θ μ) μ⟩`.

Establish `hj : ∀ j : ℕ, Measure.map (θ ^ j : Monoid.End G) μ = c ^ j • μ`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[pow_zero, pow_zero, one_smul]`.

Conclude with `Measure.map_id`. Consider the case `succ j ih`. Establish `hcomp : ((θ ^ (j + 1) : Monoid.End G) : G → G) = (θ ^ j : Monoid.End G) ∘ θ`. Rewrite using `[pow_succ]`. Both sides reduce to the same expression.

Rewrite using `[hcomp, ← Measure.map_map (hpow j).measurable hθ.measurable, hc, Measure.map_smul, ih, smul_smul, pow_succ']`. Establish `hfin : c ^ (m + 1) • μ = μ`. Rewrite using `[← hj, hθl]`. Conclude with `Measure.map_id`. Take `⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G)` from `inferInstance`.

Establish `hK0 : μ K ≠ 0` using `(Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'`. Establish `hKt : μ K ≠ ⊤` using `K.isCompact.measure_lt_top.ne`. Establish `hc1 : c ^ (m + 1) = 1`. Establish `h` using `congrArg (fun ν : Measure G => ν K) hfin`. Simplify using `only [Measure.coe_nnreal_smul_apply] at h`.

Establish `h' : ((c ^ (m + 1) : NNReal) : ENNReal) * μ K = 1 * μ K` using `by rw [one_mul]; exact h`. Conclude with `(ENNReal.mul_left_inj hK0 hKt).mp h'` after adjusting the coercions. Establish `hc2 : c = 1` using `(pow_eq_one_iff_of_nonneg (by positivity) (Nat.succ_ne_zero m)).mp hc1`. Use `⟨hθ.measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, hc2, one_smul]`.
-/
theorem finPres : FinPres := by
  intro G _ _ _ _ _ _ _ _ μ hμ θ hθ l hl hθl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  have hpow : ∀ j : ℕ, Continuous (θ ^ j : Monoid.End G) := by
    intro j
    induction j with
    | zero => exact continuous_id
    | succ j ih =>
      rw [pow_succ]
      exact ih.comp hθ
  have h1 : ∀ x, (θ ^ m : Monoid.End G) (θ x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ] at this
    exact this
  have h2 : ∀ x, θ ((θ ^ m : Monoid.End G) x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ'] at this
    exact this
  let e : G ≃* G :=
    { toFun := θ, invFun := (θ ^ m : Monoid.End G), left_inv := h1, right_inv := h2,
      map_mul' := map_mul θ }
  have hν : (Measure.map θ μ).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e hθ (hpow m)
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map θ μ = c • μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.map θ μ) μ⟩
  have hj : ∀ j : ℕ, Measure.map (θ ^ j : Monoid.End G) μ = c ^ j • μ := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact Measure.map_id
    | succ j ih =>
      have hcomp : ((θ ^ (j + 1) : Monoid.End G) : G → G) = (θ ^ j : Monoid.End G) ∘ θ := by
        rw [pow_succ]; rfl
      rw [hcomp, ← Measure.map_map (hpow j).measurable hθ.measurable, hc, Measure.map_smul, ih,
        smul_smul, pow_succ']
  have hfin : c ^ (m + 1) • μ = μ := by
    rw [← hj, hθl]
    exact Measure.map_id
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hKt : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hc1 : c ^ (m + 1) = 1 := by
    have h := congrArg (fun ν : Measure G => ν K) hfin
    simp only [Measure.coe_nnreal_smul_apply] at h
    have h' : ((c ^ (m + 1) : NNReal) : ENNReal) * μ K = 1 * μ K := by rw [one_mul]; exact h
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).mp h'
  have hc2 : c = 1 := (pow_eq_one_iff_of_nonneg (by positivity) (Nat.succ_ne_zero m)).mp hc1
  refine ⟨hθ.measurable, ?_⟩
  rw [hc, hc2, one_smul]

end UpperTheory.V.Z.Tf.Orb
