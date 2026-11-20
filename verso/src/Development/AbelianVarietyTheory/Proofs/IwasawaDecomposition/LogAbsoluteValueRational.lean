import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ExtValueGroup

/- English proof (translation)
Establish `key : ∀ x y : K, w x ≤ w y → w (x + y) ≤ w y`. Introduce `x y h`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using `using h`.

Establish `hp : 0 < w y` using `w.pos hy`. Establish `h1 : x / y ∈ O` using `by rw [hO, map_div₀, div_le_one hp]; exact h`. Establish `h2 : x / y + 1 ∈ O` using `O.add_mem _ _ h1 O.one_mem`. Rewrite `h2` using `[hO, div_add_one hy, map_div₀, div_le_one hp]`. Conclude with `h2`.

Break down `le_total (w x) (w y) with h | h` into its components or cases. Conclude with `(key x y h).trans (le_max_right _ _)`. Rewrite using `[add_comm]`. Conclude with `(key y x h).trans (le_max_left _ _)`.
-/
theorem add_le_max {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K)
    (hO : ∀ x, x ∈ O ↔ w x ≤ 1) (x y : K) : w (x + y) ≤ max (w x) (w y) := by
  have key : ∀ x y : K, w x ≤ w y → w (x + y) ≤ w y := by
    intro x y h
    by_cases hy : y = 0
    · subst hy; simpa using h
    have hp : 0 < w y := w.pos hy
    have h1 : x / y ∈ O := by rw [hO, map_div₀, div_le_one hp]; exact h
    have h2 : x / y + 1 ∈ O := O.add_mem _ _ h1 O.one_mem
    rw [hO, div_add_one hy, map_div₀, div_le_one hp] at h2
    exact h2
  rcases le_total (w x) (w y) with h | h
  · exact (key x y h).trans (le_max_right _ _)
  · rw [add_comm]; exact (key y x h).trans (le_max_left _ _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hc`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(hw _ _).trans_lt (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))`.
-/
theorem sum_lt {K ι : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : ∀ x y, w (x + y) ≤ max (w x) (w y)) (f : ι → K) (c : ℝ) (hc : 0 < c) (s : Finset ι)
    (h : ∀ j ∈ s, w (f j) < c) : w (∑ j ∈ s, f j) < c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans_lt (max_lt (h a (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

/- English proof (translation)
Take `⟨i, hi, hmax⟩` from `s.exists_max_image (fun j => w (f j)) hs`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h1 : w (∑ j ∈ s.erase i, f j) < w (f i)`. Use `sum_lt w hw f _ (w.pos (hf i hi)) _ fun j hj => ?_` and prove the remaining obligations.

Take `⟨hji, hjs⟩` from `Finset.mem_erase.1 hj`. Conclude with `lt_of_le_of_ne (hmax j hjs) (hc j hjs i hi hji)`. Rewrite `h0` using `[← Finset.add_sum_erase s f hi]`. Establish `h2 : ∑ j ∈ s.erase i, f j = - f i` using `by linear_combination h0`. Rewrite `h1` using `[h2, w.map_neg]`.

Conclude with `lt_irrefl _ h1`.
-/
theorem exists_eq_of_sum_eq_zero {K ι : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : ∀ x y, w (x + y) ≤ max (w x) (w y)) (f : ι → K) (s : Finset ι) (hs : s.Nonempty)
    (hf : ∀ j ∈ s, f j ≠ 0) (h0 : ∑ j ∈ s, f j = 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ w (f i) = w (f j) := by
  classical
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => w (f j)) hs
  by_contra hc
  push Not at hc
  have h1 : w (∑ j ∈ s.erase i, f j) < w (f i) := by
    refine sum_lt w hw f _ (w.pos (hf i hi)) _ fun j hj => ?_
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.1 hj
    exact lt_of_le_of_ne (hmax j hjs) (hc j hjs i hi hji)
  rw [← Finset.add_sum_erase s f hi] at h0
  have h2 : ∑ j ∈ s.erase i, f j = - f i := by linear_combination h0
  rw [h2, w.map_neg] at h1
  exact lt_irrefl _ h1

/- English proof (translation)
Establish `h0 : v.valuation F a ≠ 0` using `by simpa using ha`. Rewrite using `[NumberField.HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ h0]`. Use `⟨Multiplicative.toAdd (WithZero.unzero h0), ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[Real.log_zpow]`.
-/
theorem log_adicAbv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0) :
    ∃ z : ℤ, Real.log (NumberField.HeightOneSpectrum.adicAbv F v a) =
      (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : v.valuation F a ≠ 0 := by simpa using ha
  rw [NumberField.HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  refine ⟨Multiplicative.toAdd (WithZero.unzero h0), ?_⟩
  push_cast
  rw [Real.log_zpow]

/- English proof (translation)
Take `⟨p, hp, hp0⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := F) α)`. Rewrite `hp0` using `[Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]`. Establish `hc : ∀ j ∈ p.support, p.coeff j ≠ 0` using `fun j hj => Polynomial.mem_support_iff.1 hj`. Establish `hne : ∀ j ∈ p.support, algebraMap F (AlgebraicClosure F) (p.coeff j) ≠ 0` using `fun j hj => by`. Simplify using `using hc j hj`.

Take `⟨i, hi, j, hj, hij, h⟩` from `exists_eq_of_sum_eq_zero e.w (add_le_max e.w e.O e.mem_O) _ p.support (Polynomial.support_nonempty.2 hp) (fun j hj => mul_ne_zero (hne j hj) (pow_ne_zero _ hα)) hp0`. Take `⟨zi, hzi⟩` from `log_adicAbv v _ (hc i hi)`. Take `⟨zj, hzj⟩` from `log_adicAbv v _ (hc j hj)`. Establish `hl` using `congrArg Real.log h`. Rewrite `hl` using `[map_mul, map_mul, map_pow, map_pow, Real.log_mul (e.w.pos (hne i hi)).ne' (pow_pos (e.w.pos hα) _).ne', Real.log_mul (e.w.pos (hne j hj)).ne' (pow_pos (e.w.pos hα) _).ne', Real.log_pow, Real.log_pow, e.w_alg, e.w_alg, hzi, hzj]`.

Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases. Use `⟨j - i, zi - zj, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_sub hlt.le]`. Use `push_cast`. Take the linear combination `-hl`.

Use `⟨i - j, zj - zi, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_sub hlt.le]`. Use `push_cast`. Take the linear combination `hl`.
-/
theorem log_w_rat (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
    (α : AlgebraicClosure F) (hα : α ≠ 0) :
    ∃ (m : ℕ) (z : ℤ), 0 < m ∧
      (m : ℝ) * Real.log (e.w α) = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  obtain ⟨p, hp, hp0⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := F) α)
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp0
  have hc : ∀ j ∈ p.support, p.coeff j ≠ 0 := fun j hj => Polynomial.mem_support_iff.1 hj
  have hne : ∀ j ∈ p.support, algebraMap F (AlgebraicClosure F) (p.coeff j) ≠ 0 := fun j hj => by
    simpa using hc j hj
  obtain ⟨i, hi, j, hj, hij, h⟩ := exists_eq_of_sum_eq_zero e.w (add_le_max e.w e.O e.mem_O) _ p.support
    (Polynomial.support_nonempty.2 hp) (fun j hj => mul_ne_zero (hne j hj) (pow_ne_zero _ hα)) hp0
  obtain ⟨zi, hzi⟩ := log_adicAbv v _ (hc i hi)
  obtain ⟨zj, hzj⟩ := log_adicAbv v _ (hc j hj)
  have hl := congrArg Real.log h
  rw [map_mul, map_mul, map_pow, map_pow,
    Real.log_mul (e.w.pos (hne i hi)).ne' (pow_pos (e.w.pos hα) _).ne',
    Real.log_mul (e.w.pos (hne j hj)).ne' (pow_pos (e.w.pos hα) _).ne',
    Real.log_pow, Real.log_pow, e.w_alg, e.w_alg, hzi, hzj] at hl
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, zi - zj, by omega, ?_⟩
    rw [Nat.cast_sub hlt.le]; push_cast; linear_combination -hl
  · refine ⟨i - j, zj - zi, by omega, ?_⟩
    rw [Nat.cast_sub hlt.le]; push_cast; linear_combination hl

end GlobalTheory.ExtValueGroup
