import Mathlib
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Use `set N : ℕ := Ideal.absNorm m with hN`. Establish `hN0 : N ≠ 0`. Rewrite using `[hN]`. Conclude with `fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hNR : (N : ℝ) ≠ 0` using `by exact_mod_cast hN0`.

Use `⟨(N : ℝ) * ∑ i, ‖latticeBasis K i‖, fun z => ?_⟩` and prove the remaining obligations. Use `set w : mixedSpace K := (N : ℝ)⁻¹ • (z - 1) with hw`. Establish `hmem` using `(ZSpan.floor (latticeBasis K) w).2`. Take `⟨a, ha⟩` from `(mem_span_latticeBasis K).mp hmem`. Use `⟨1 + (N : 𝓞 K) * a, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_sub_cancel_left]`. Conclude with `m.mul_mem_right _ (Ideal.absNorm_mem m)`. Establish `ha' : mixedEmbedding K (a : K) = (ZSpan.floor (latticeBasis K) w : mixedSpace K)` using `ha`. Establish `h1 : z - mixedEmbedding K ((1 + (N : 𝓞 K) * a : 𝓞 K) : K) = (N : ℝ) • ZSpan.fract (latticeBasis K) w`. Rewrite using `[ZSpan.fract_apply, ← ha', smul_sub, hw, smul_inv_smul₀ hNR]`.

Simplify using `only [map_add, map_one, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, _root_.norm_smul, Real.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (ZSpan.norm_fract_le _ _) (Nat.cast_nonneg _)`.
-/
theorem exists_near_one_mod_ideal (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) : ∃ C : ℝ, ∀ z : mixedSpace K, ∃ β : 𝓞 K, β - 1 ∈ m ∧
      ‖z - mixedEmbedding K β‖ ≤ C := by
  set N : ℕ := Ideal.absNorm m with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨(N : ℝ) * ∑ i, ‖latticeBasis K i‖, fun z => ?_⟩
  set w : mixedSpace K := (N : ℝ)⁻¹ • (z - 1) with hw
  have hmem := (ZSpan.floor (latticeBasis K) w).2
  obtain ⟨a, ha⟩ := (mem_span_latticeBasis K).mp hmem
  refine ⟨1 + (N : 𝓞 K) * a, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact m.mul_mem_right _ (Ideal.absNorm_mem m)
  · have ha' : mixedEmbedding K (a : K) = (ZSpan.floor (latticeBasis K) w : mixedSpace K) := ha
    have h1 : z - mixedEmbedding K ((1 + (N : 𝓞 K) * a : 𝓞 K) : K)
        = (N : ℝ) • ZSpan.fract (latticeBasis K) w := by
      rw [ZSpan.fract_apply, ← ha', smul_sub, hw, smul_inv_smul₀ hNR]
      simp only [map_add, map_one, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      ring
    rw [h1, _root_.norm_smul, Real.norm_natCast]
    exact mul_le_mul_of_nonneg_left (ZSpan.norm_fract_le _ _) (Nat.cast_nonneg _)

/- English proof (translation)
Introduce `K _ _ m φ hm hc hh h1 x hx`. Take `⟨C, hC⟩` from `exists_near_one_mod_ideal K m hm`. Use `choose β hβm hβ using hC`. Use `set y : ℕ → mixedSpace K := fun n => ((n : ℝ) + 1)⁻¹ • mixedEmbedding K (β (((n : ℝ) + 1) • x)) with hy`. Establish `hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1` using `fun n => by positivity`.

Establish `hlim : Filter.Tendsto y Filter.atTop (nhds x)`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * C) Filter.atTop (nhds 0)`. Simplify using `using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0` and prove the remaining obligations.

Establish `: x - y n = ((n : ℝ) + 1)⁻¹ • (((n : ℝ) + 1) • x - mixedEmbedding K (β (((n : ℝ) + 1) • x)))`. Rewrite using `[smul_sub, inv_smul_smul₀ (hpos n).ne']`. Rewrite using `[norm_sub_rev, this, _root_.norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hpos n)).le, one_div]`. Conclude with `mul_le_mul_of_nonneg_left (hβ _) (inv_pos.mpr (hpos n)).le`. Establish `hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0}` using `isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const`.

Establish `hca : ContinuousAt φ x` using `hc.continuousAt (hopen.mem_nhds hx)`. Establish `hev : ∀ᶠ n in Filter.atTop, φ (y n) = 1` using `by filter_upwards [hlim.eventually (hopen.mem_nhds hx)] with n hn`. Establish `hne : β (((n : ℝ) + 1) • x) ≠ 0`. Introduce `h0`. Apply `hn` to reduce the goal to its premises.

Simplify using `[hy, h0]`. Simplify using `only [hy]`. Rewrite using `[hh _ _ (inv_pos.mpr (hpos n))]`. Conclude with `h1 _ hne (hβm _)`. Establish `h2 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds (φ x))` using `hca.tendsto.comp hlim`.

Establish `h3 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds 1)` using `tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)`. Conclude with `tendsto_nhds_unique h2 h3`.
-/
theorem eq_one_of_homogeneous_of_eq_one_on_class :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (φ : mixedSpace K → ℂ), m ≠ ⊥ → ContinuousOn φ {x | mixedEmbedding.norm x ≠ 0} → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → φ (mixedEmbedding K β) = 1) → ∀ x, mixedEmbedding.norm x ≠ 0 → φ x = 1 := by
  intro K _ _ m φ hm hc hh h1 x hx
  obtain ⟨C, hC⟩ := exists_near_one_mod_ideal K m hm
  choose β hβm hβ using hC
  set y : ℕ → mixedSpace K := fun n =>
    ((n : ℝ) + 1)⁻¹ • mixedEmbedding K (β (((n : ℝ) + 1) • x)) with hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlim : Filter.Tendsto y Filter.atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * C) Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have : x - y n = ((n : ℝ) + 1)⁻¹ •
        (((n : ℝ) + 1) • x - mixedEmbedding K (β (((n : ℝ) + 1) • x))) := by
      rw [smul_sub, inv_smul_smul₀ (hpos n).ne']
    rw [norm_sub_rev, this, _root_.norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hpos n)).le, one_div]
    exact mul_le_mul_of_nonneg_left (hβ _) (inv_pos.mpr (hpos n)).le
  have hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
  have hca : ContinuousAt φ x := hc.continuousAt (hopen.mem_nhds hx)
  have hev : ∀ᶠ n in Filter.atTop, φ (y n) = 1 := by
    filter_upwards [hlim.eventually (hopen.mem_nhds hx)] with n hn
    have hne : β (((n : ℝ) + 1) • x) ≠ 0 := by
      intro h0
      apply hn
      simp [hy, h0]
    simp only [hy]
    rw [hh _ _ (inv_pos.mpr (hpos n))]
    exact h1 _ hne (hβm _)
  have h2 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds (φ x)) := hca.tendsto.comp hlim
  have h3 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  exact tendsto_nhds_unique h2 h3

end GlobalTheory
