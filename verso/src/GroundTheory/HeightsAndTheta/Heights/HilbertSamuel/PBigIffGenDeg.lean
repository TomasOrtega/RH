import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBigIffGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace BigIffGenDeg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `hmem : ((n : ℤ)) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)` using `by show mConeMap y (C (n : ℤ)) = 0`. Rewrite using `[map_natCast C n, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]`. Rewrite `hmem` using `[h.2.2.1]`. Conclude with `(Ideal.mem_bot.mp hmem)` after adjusting the coercions.
-/
theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ)) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [map_natCast C n, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot.mp hmem)

/- English proof (translation)
Introduce `k`. Take `⟨i, hi⟩` from `h.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Use `show mConeMap y (X ⟨k, i⟩) = 0`. Simplify using `[mConeMap, h0]`.
-/
theorem coord_ne_zero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show mConeMap y (X ⟨k, i⟩) = 0
  simp [mConeMap, h0]

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D M P₀ hD1 har hP0 hs`. Use `charZero_of_isArithVar har` as an intermediate fact. Establish `hy` using `coord_ne_zero_of_isArithVar har`. Take `⟨C, hC⟩` from `hA K ι Ω y D M.a hD1 har (nefOnGenericDeg_of_semipos hN hD hP0 hs)`. Use `set δ : ℝ := (genDeg (mCoordIdeal y) D M.a : ℝ) with hδdef`.

Use `set F : ℝ := (D.factorial : ℝ) with hFdef`. Establish `hF : 0 < F` using `by positivity`. Use `set r : ℕ → ℕ := fun n => Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y M.a n)) with hrdef`. Establish `hrank : ∀ n : ℕ, |(r n : ℝ) - δ * (n : ℝ) ^ D / F| ≤ C * ((n : ℝ) + 1) ^ (D - 1)` using `fun n => by`. Simplify using `only [hrdef]`.

Rewrite using `[hR K ι Ω y M.a n hy]`. Conclude with `hC n`. Establish `hC0 : 0 ≤ C`. Use `(abs_nonneg _).trans (hrank 0)` as an intermediate fact. Simplify using `using this`.

Establish `hpow : ∀ x : ℝ, 1 ≤ x → (x + 1) ^ (D - 1) ≤ 2 ^ (D - 1) * x ^ (D - 1)` using `fun x hx => by`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith) _`. Establish `hsplit : ∀ x : ℝ, x ^ D = x * x ^ (D - 1)` using `fun x => by`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hδ0 : (0 : ℤ) < genDeg (mCoordIdeal y) D M.a ↔ 0 < δ`. Rewrite using `[hδdef]`. Conclude with `Iff.rfl` after adjusting the coercions.

Rewrite using `[hδ0]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, j, hj, hev⟩`. Assume the negation of the conclusion as `hδ`. Use `push Not at hδ`.

Use `set B : ℝ := C * 2 ^ (D - 1) * (j : ℝ) ^ (D - 1) with hB`. Take `⟨n, ⟨q, s, hcq, hli, hmem⟩, hnN⟩` from `(hev.and (eventually_ge_atTop (max 1 (⌈B / c⌉₊ + 1)))).exists`. Establish `hn1 : 1 ≤ n` using `le_of_max_le_left hnN`. Establish `hnB : B < c * n`. Establish `h1 : B / c < n`.

Use `Nat.le_ceil (B / c)` as an intermediate fact. Establish `h2 : ((⌈B / c⌉₊ + 1 : ℕ) : ℝ) ≤ n` using `by exact_mod_cast le_of_max_le_right hnN`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h1` using `[div_lt_iff₀ hc, mul_comm]`. Then use the resulting hypothesis.

Use `set p := AddSubgroup.toIntSubmodule (chartLat y M.a (j * n))`. Establish `: Module.Finite ℤ p` using `Module.Finite.iff_fg.mpr (by`. Use `hL K ι Ω y M.a (j * n) hy` as an intermediate fact. Conclude with `(Submodule.fg_iff_addSubgroup_fg _).mpr this)`. Establish `hle : q ≤ r (j * n)`.

Establish `hli' : LinearIndependent ℤ (fun i => (⟨s i, hmem i⟩ : p))` using `LinearIndependent.of_comp p.subtype hli`. Simplify using `using hli'.fintype_card_le_finrank`. Establish `hjn : (1 : ℝ) ≤ ((j * n : ℕ) : ℝ)` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)`. Establish `hup : (r (j * n) : ℝ) ≤ B * (n : ℝ) ^ (D - 1)`. Establish `h1` using `le_of_abs_le (hrank (j * n))`.

Establish `h2 : δ * ((j * n : ℕ) : ℝ) ^ D / F ≤ 0` using `div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hδ (by positivity)) hF.le`. Establish `h3` using `mul_le_mul_of_nonneg_left (hpow _ hjn) hC0`. Establish `h4 : C * (2 ^ (D - 1) * ((j * n : ℕ) : ℝ) ^ (D - 1)) = B * (n : ℝ) ^ (D - 1)`. Rewrite using `[hB]`. Use `push_cast`.

Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : c * (n : ℝ) ^ D ≤ B * (n : ℝ) ^ (D - 1)` using `hcq.trans ((by exact_mod_cast hle : (q : ℝ) ≤ r (j * n)).trans hup)`. Rewrite `hq` using `[hsplit, ← mul_assoc]`.

Establish `hpos : 0 < (n : ℝ) ^ (D - 1)` using `by positivity`. Conclude with `absurd (le_of_mul_le_mul_right hq hpos) (not_le.mpr hnB)`. Introduce `hδ`. Use `⟨δ / (2 * F), by positivity, 1, le_rfl, ?_⟩` and prove the remaining obligations. Use `set N : ℝ := 2 * F * C * 2 ^ (D - 1) / δ with hN'`.

Use `filter_upwards [eventually_ge_atTop (max 1 ⌈N⌉₊)] with n hnN`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast le_of_max_le_left hnN`. Establish `hnN' : N ≤ n` using `(Nat.le_ceil N).trans (by exact_mod_cast le_of_max_le_right hnN)`. Use `set p := AddSubgroup.toIntSubmodule (chartLat y M.a n)`. Take `⟨f, hf⟩` from `exists_linearIndependent_of_le_finrank (le_refl (Module.finrank ℤ p))`.

Use `⟨_, fun i => (f i : Ω), ?_, hf.map' p.subtype (Submodule.ker_subtype p), fun i => by` and prove the remaining obligations. Rewrite using `[one_mul]`. Conclude with `(f i).2⟩`. Establish `h1` using `neg_le_of_abs_le (hrank n)`. Establish `h2` using `mul_le_mul_of_nonneg_left (hpow _ hn1) hC0`.

Establish `h3 : C * 2 ^ (D - 1) ≤ δ / (2 * F) * n`. Rewrite `hnN'` using `[hN', div_le_iff₀ hδ]`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : C * 2 ^ (D - 1) * (n : ℝ) ^ (D - 1) ≤ δ / (2 * F) * (n : ℝ) ^ D`.

Rewrite using `[hsplit, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right h3 (by positivity)`. Express the relevant statement in the definitionally equal form `δ / (2 * F) * (n : ℝ) ^ D ≤ (r n : ℝ)`. Take the linear combination `h1 + h2 + h4`.
-/
theorem proof (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement)
    (hL : SectionLatticeFinite.Statement) (hR : ChartLatRank.Statement)
    (hA : NefSectionsAsymptotic.Statement) : BigIffGenDeg.Statement := by
  intro K _ ι _ Ω _ y D M P₀ hD1 har hP0 hs
  have := charZero_of_isArithVar har
  have hy := coord_ne_zero_of_isArithVar har
  obtain ⟨C, hC⟩ := hA K ι Ω y D M.a hD1 har (nefOnGenericDeg_of_semipos hN hD hP0 hs)
  set δ : ℝ := (genDeg (mCoordIdeal y) D M.a : ℝ) with hδdef
  set F : ℝ := (D.factorial : ℝ) with hFdef
  have hF : 0 < F := by positivity
  set r : ℕ → ℕ := fun n => Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y M.a n)) with hrdef
  have hrank : ∀ n : ℕ, |(r n : ℝ) - δ * (n : ℝ) ^ D / F| ≤ C * ((n : ℝ) + 1) ^ (D - 1) := fun n => by
    simp only [hrdef]
    rw [hR K ι Ω y M.a n hy]
    exact hC n
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hrank 0)
    simpa using this
  have hpow : ∀ x : ℝ, 1 ≤ x → (x + 1) ^ (D - 1) ≤ 2 ^ (D - 1) * x ^ (D - 1) := fun x hx => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hsplit : ∀ x : ℝ, x ^ D = x * x ^ (D - 1) := fun x => by
    rw [← pow_succ']
    congr 1
    omega
  have hδ0 : (0 : ℤ) < genDeg (mCoordIdeal y) D M.a ↔ 0 < δ := by
    rw [hδdef]
    exact_mod_cast Iff.rfl
  rw [hδ0]
  constructor
  · rintro ⟨c, hc, j, hj, hev⟩
    by_contra hδ
    push Not at hδ
    set B : ℝ := C * 2 ^ (D - 1) * (j : ℝ) ^ (D - 1) with hB
    obtain ⟨n, ⟨q, s, hcq, hli, hmem⟩, hnN⟩ :=
      (hev.and (eventually_ge_atTop (max 1 (⌈B / c⌉₊ + 1)))).exists
    have hn1 : 1 ≤ n := le_of_max_le_left hnN
    have hnB : B < c * n := by
      have h1 : B / c < n := by
        have := Nat.le_ceil (B / c)
        have h2 : ((⌈B / c⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hnN
        push_cast at h2
        linarith
      rwa [div_lt_iff₀ hc, mul_comm] at h1
    set p := AddSubgroup.toIntSubmodule (chartLat y M.a (j * n))
    have : Module.Finite ℤ p := Module.Finite.iff_fg.mpr (by
      have := hL K ι Ω y M.a (j * n) hy
      exact (Submodule.fg_iff_addSubgroup_fg _).mpr this)
    have hle : q ≤ r (j * n) := by
      have hli' : LinearIndependent ℤ (fun i => (⟨s i, hmem i⟩ : p)) :=
        LinearIndependent.of_comp p.subtype hli
      simpa using hli'.fintype_card_le_finrank
    have hjn : (1 : ℝ) ≤ ((j * n : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hup : (r (j * n) : ℝ) ≤ B * (n : ℝ) ^ (D - 1) := by
      have h1 := le_of_abs_le (hrank (j * n))
      have h2 : δ * ((j * n : ℕ) : ℝ) ^ D / F ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hδ (by positivity)) hF.le
      have h3 := mul_le_mul_of_nonneg_left (hpow _ hjn) hC0
      have h4 : C * (2 ^ (D - 1) * ((j * n : ℕ) : ℝ) ^ (D - 1)) = B * (n : ℝ) ^ (D - 1) := by
        rw [hB]; push_cast; rw [mul_pow]; ring
      linarith
    have hq : c * (n : ℝ) ^ D ≤ B * (n : ℝ) ^ (D - 1) :=
      hcq.trans ((by exact_mod_cast hle : (q : ℝ) ≤ r (j * n)).trans hup)
    rw [hsplit, ← mul_assoc] at hq
    have hpos : 0 < (n : ℝ) ^ (D - 1) := by positivity
    exact absurd (le_of_mul_le_mul_right hq hpos) (not_le.mpr hnB)
  · intro hδ
    refine ⟨δ / (2 * F), by positivity, 1, le_rfl, ?_⟩
    set N : ℝ := 2 * F * C * 2 ^ (D - 1) / δ with hN'
    filter_upwards [eventually_ge_atTop (max 1 ⌈N⌉₊)] with n hnN
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hnN
    have hnN' : N ≤ n := (Nat.le_ceil N).trans (by exact_mod_cast le_of_max_le_right hnN)
    set p := AddSubgroup.toIntSubmodule (chartLat y M.a n)
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (le_refl (Module.finrank ℤ p))
    refine ⟨_, fun i => (f i : Ω), ?_, hf.map' p.subtype (Submodule.ker_subtype p), fun i => by
      rw [one_mul]; exact (f i).2⟩
    have h1 := neg_le_of_abs_le (hrank n)
    have h2 := mul_le_mul_of_nonneg_left (hpow _ hn1) hC0
    have h3 : C * 2 ^ (D - 1) ≤ δ / (2 * F) * n := by
      rw [hN', div_le_iff₀ hδ] at hnN'
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h4 : C * 2 ^ (D - 1) * (n : ℝ) ^ (D - 1) ≤ δ / (2 * F) * (n : ℝ) ^ D := by
      rw [hsplit, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    change δ / (2 * F) * (n : ℝ) ^ D ≤ (r n : ℝ)
    linear_combination h1 + h2 + h4

end BigIffGenDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
