import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

open Polynomial

namespace GlobalTheory.CompanionTheory.LinRec

noncomputable def shift : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun u := fun i => u (i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma shift_apply (u : ℕ → ℂ) (i : ℕ) : shift u i = u (i + 1) := rfl

/- English proof (translation)
Proceed by induction on `j generalizing u with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, shift_apply]`. Both sides reduce to the same expression.
-/
lemma shift_pow (j : ℕ) (u : ℕ → ℂ) (i : ℕ) : (shift ^ j) u i = u (i + j) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, shift_apply]
    rfl

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Pi.smul_apply, shift_pow, smul_eq_mul]`.
-/
lemma aeval_shift (p : ℂ[X]) (u : ℕ → ℂ) (i : ℕ) :
    aeval shift p u i = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shift_pow, smul_eq_mul]

/- English proof (translation)
Establish `h : aeval shift (X - C z : ℂ[X]) u = fun i => u (i + 1) - z * u i`. Use function extensionality and compare the values at `i`. Simplify using `[aeval_X, aeval_C, shift_apply, Module.algebraMap_end_apply]`. Rewrite using `[← h, ← Module.End.mul_apply, ← map_mul, mul_comm]`. Conclude with `hu`.
-/
lemma aeval_diff (q : ℂ[X]) (z : ℂ) (u : ℕ → ℂ) (hu : aeval shift ((X - C z) * q) u = 0) :
    aeval shift q (fun i => u (i + 1) - z * u i) = 0 := by
  have h : aeval shift (X - C z : ℂ[X]) u = fun i => u (i + 1) - z * u i := by
    funext i
    simp [aeval_X, aeval_C, shift_apply, Module.algebraMap_end_apply]
  rw [← h, ← Module.End.mul_apply, ← map_mul, mul_comm]
  exact hu

/- English proof (translation)
Establish `hpos : 0 < Real.exp κ - ‖z‖` using `sub_pos.2 hz`. Use `set D : ℝ := 1 + c / (Real.exp κ - ‖z‖) with hDdef`. Establish `hD1 : 1 ≤ D`. Establish `: 0 ≤ c / (Real.exp κ - ‖z‖)` using `div_nonneg hc hpos.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hD : ‖z‖ * D + c ≤ D * Real.exp κ`. Establish `: D * (Real.exp κ - ‖z‖) = (Real.exp κ - ‖z‖) + c`. Rewrite using `[hDdef]`. Clear the denominators using the available nonvanishing facts. Use the polynomial consequences of the given equalities and inequalities.

Proceed by induction on `i with`. Consider the case `zero`. Simplify using `only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]`. Use the polynomial consequences of the given equalities and inequalities. Consider the case `succ i ih`.

Establish `hE : 0 < Real.exp (κ * i)` using `Real.exp_pos _`. Establish `h1 : ‖u (i + 1)‖ ≤ ‖z‖ * ‖u i‖ + ‖u (i + 1) - z * u i‖`. Establish `: u (i + 1) = z * u i + (u (i + 1) - z * u i)` using `by ring`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp : Real.exp (κ * ((i + 1 : ℕ) : ℝ)) = Real.exp (κ * i) * Real.exp κ`.

Rewrite using `[← Real.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp]`.

Establish `hEM : 0 ≤ Real.exp (κ * i) * M` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma geom_step (z : ℂ) (κ c M : ℝ) (hz : ‖z‖ < Real.exp κ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (u : ℕ → ℂ) (h0 : ‖u 0‖ ≤ M)
    (hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤ c * Real.exp (κ * i) * M) (i : ℕ) :
    ‖u i‖ ≤ (1 + c / (Real.exp κ - ‖z‖)) * Real.exp (κ * i) * M := by
  have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hz
  set D : ℝ := 1 + c / (Real.exp κ - ‖z‖) with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ c / (Real.exp κ - ‖z‖) := div_nonneg hc hpos.le
    linarith
  have hD : ‖z‖ * D + c ≤ D * Real.exp κ := by
    have : D * (Real.exp κ - ‖z‖) = (Real.exp κ - ‖z‖) + c := by
      rw [hDdef]; field_simp
    nlinarith
  induction i with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    nlinarith
  | succ i ih =>
    have hE : 0 < Real.exp (κ * i) := Real.exp_pos _
    have h1 : ‖u (i + 1)‖ ≤ ‖z‖ * ‖u i‖ + ‖u (i + 1) - z * u i‖ := by
      have : u (i + 1) = z * u i + (u (i + 1) - z * u i) := by ring
      calc ‖u (i + 1)‖ = ‖z * u i + (u (i + 1) - z * u i)‖ := by rw [← this]
        _ ≤ ‖z * u i‖ + ‖u (i + 1) - z * u i‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    have hexp : Real.exp (κ * ((i + 1 : ℕ) : ℝ)) = Real.exp (κ * i) * Real.exp κ := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc ‖u (i + 1)‖ ≤ ‖z‖ * (D * Real.exp (κ * i) * M) + c * Real.exp (κ * i) * M :=
          h1.trans (add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg _)) (hv i))
      _ = (‖z‖ * D + c) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (D * Real.exp κ) * (Real.exp (κ * i) * M) := mul_le_mul_of_nonneg_right hD hEM
      _ = _ := by ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `p κ hp hd _`. Use `⟨0, le_rfl, fun u M hu _ _ i => ?_⟩` and prove the remaining obligations. Establish `hp1 : p = 1`.

Establish `h1 : p.coeff 0 = 1`. Establish `h2` using `hp.coeff_natDegree`. Rewrite `h2` using `[hd]`. Then use the resulting hypothesis. Rewrite using `[eq_C_of_natDegree_eq_zero hd, h1, C_1]`. Substitute `hp1` using the available equality.

Establish `hu0 : u = 0` using `by simpa using hu`. Simplify using `[hu0]`. Consider the case `succ n ih`. Introduce `p κ hp hd hr`. Take `⟨z, hz⟩ : ∃ z, p.IsRoot z` from `IsAlgClosed.exists_root p (by`.

Introduce `h0`. Establish `: p.natDegree = 0` using `natDegree_eq_zero_iff_degree_le_zero.2 h0.le`. Use the proof step `omega)`. Establish `hzlt` using `hr z hz`. Take `⟨q, rfl⟩` from `dvd_iff_isRoot.2 hz`.

Establish `hq : q.Monic` using `(monic_X_sub_C z).of_mul_monic_left hp`. Establish `hqd : q.natDegree = n`. Rewrite `hd` using `[(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Take `⟨C', hC', hB⟩` from `ih q κ hq hqd fun w hw => hr w (by`.

Establish `hw' : eval w q = 0` using `hw`. Simplify using `[IsRoot, hw'])`. Establish `hpos : 0 < Real.exp κ - ‖z‖` using `sub_pos.2 hzlt`. Establish `hc : 0 ≤ C' * (1 + ‖z‖)` using `by positivity`. Use `⟨1 + C' * (1 + ‖z‖) / (Real.exp κ - ‖z‖), by positivity, fun u M hu hM hM0 i => ?_⟩` and prove the remaining obligations.

Use `geom_step z κ _ M hzlt hc hM0 u (hM 0 (Nat.succ_pos n)) (fun i => ?_) i` and prove the remaining obligations. Establish `hb` using `hB (fun i => u (i + 1) - z * u i) ((1 + ‖z‖) * M) (aeval_diff q z u hu) (fun j hj => ?_) (by positivity) i`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_of_natDegree (n : ℕ) : ∀ (p : ℂ[X]) (κ : ℝ), p.Monic → p.natDegree = n →
    (∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < n, ‖u j‖ ≤ M) → 0 ≤ M → ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  induction n with
  | zero =>
    intro p κ hp hd _
    refine ⟨0, le_rfl, fun u M hu _ _ i => ?_⟩
    have hp1 : p = 1 := by
      have h1 : p.coeff 0 = 1 := by
        have h2 := hp.coeff_natDegree
        rwa [hd] at h2
      rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
    subst hp1
    have hu0 : u = 0 := by simpa using hu
    simp [hu0]
  | succ n ih =>
    intro p κ hp hd hr
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      have : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
      omega)
    have hzlt := hr z hz
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : q.natDegree = n := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C] at hd
      omega
    obtain ⟨C', hC', hB⟩ := ih q κ hq hqd fun w hw => hr w (by
      have hw' : eval w q = 0 := hw
      simp [IsRoot, hw'])
    have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hzlt
    have hc : 0 ≤ C' * (1 + ‖z‖) := by positivity
    refine ⟨1 + C' * (1 + ‖z‖) / (Real.exp κ - ‖z‖), by positivity, fun u M hu hM hM0 i => ?_⟩
    refine geom_step z κ _ M hzlt hc hM0 u (hM 0 (Nat.succ_pos n)) (fun i => ?_) i
    have hb := hB (fun i => u (i + 1) - z * u i) ((1 + ‖z‖) * M) (aeval_diff q z u hu)
      (fun j hj => ?_) (by positivity) i
    · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + ‖z‖) * M) := hb
        _ = _ := by ring
    · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
        _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
        _ ≤ M + ‖z‖ * M := add_le_add (hM _ (by omega))
            (mul_le_mul_of_nonneg_left (hM _ (by omega)) (norm_nonneg _))
        _ = _ := by ring

/- English proof (translation)
Introduce `p κ hp hr`. Take `⟨C, hC, h⟩` from `bound_of_natDegree _ p κ hp rfl hr`. Use `⟨C, hC, fun u M hu hM hM0 i => h u M ?_ hM hM0 i⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[aeval_shift]`.

Conclude with `hu i`.
-/
theorem recBound : PositivityTheory.Rg.Rs.An.RecBound := by
  intro p κ hp hr
  obtain ⟨C, hC, h⟩ := bound_of_natDegree _ p κ hp rfl hr
  refine ⟨C, hC, fun u M hu hM hM0 i => h u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
