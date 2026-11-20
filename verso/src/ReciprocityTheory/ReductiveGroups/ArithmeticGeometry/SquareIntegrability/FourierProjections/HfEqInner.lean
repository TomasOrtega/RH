import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropABSt

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

/- English proof (translation)
Simplify using `[Hf, PiLp.inner_apply]`.
-/
theorem Hf_eq_inner (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp [Hf, PiLp.inner_apply]

/- English proof (translation)
Establish `h : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace]`. Conclude with `⟨((stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr h)).repr⟩`.
-/
theorem paIso_ex : Nonempty (EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * Fintype.card ι))) := by
  have h : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    rw [finrank_real_of_complex, finrank_euclideanSpace]
  exact ⟨((stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr h)).repr⟩

/- English proof (translation)
Break down `S.eq_empty_or_nonempty with hS0 | ⟨i₀, hi₀⟩` into its components or cases. Rewrite using `[hS0, Finset.card_empty, Nat.cast_zero]`. Establish `: 0 < R` using `lt_of_lt_of_le hR0 hR`. Check the signs of the components of the expression. Use `set c := Real.sqrt (q * Real.pi) with hc`.

Establish `hcpos : 0 < c`. Establish `h1` using `hlat _ (i₀ : lat Y.b).2 i₀.2`. Assume the negation of the conclusion as `hle`. Rewrite `hle` using `[not_lt]`. Establish `: c * ‖((i₀ : lat Y.b) : EuclideanSpace ℂ ι)‖ ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hle (norm_nonneg _)`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨e⟩` from `(paIso_ex : Nonempty (EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * Fintype.card ι))))`. Set `g : ({γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} : Set (lat Y.b)) → EuclideanSpace ℝ (Fin (2 * Fintype.card ι))` to `fun i => c • e ((i : lat Y.b) : EuclideanSpace ℂ ι)`. Establish `hg : Function.Injective g`. Introduce `i j hij`.

Establish `h1 : e ((i : lat Y.b) : EuclideanSpace ℂ ι) = e ((j : lat Y.b) : EuclideanSpace ℂ ι)` using `smul_right_injective _ hcpos.ne' hij`. Conclude with `Subtype.ext (Subtype.ext (e.injective h1))`. Establish `hcard : ((S.image g).card : ℝ) ≤ (3 * R / R0) ^ (2 * Fintype.card ι)`. Use `hP (2 * Fintype.card ι) (S.image g) R0 R hR0 hR ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite using `[norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_pos hcpos]`. Conclude with `hS i hi`. Introduce `x hx y hy hxy`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hx`.

Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hy`. Establish `hij : ((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι) ≠ 0`. Introduce `h0`. Apply `hxy` to reduce the goal to its premises. Rewrite `h0` using `[sub_eq_zero]`.

Simplify using `only [g, h0]`. Establish `hmem : ((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι) ∈ lat Y.b` using `Submodule.sub_mem _ (i : lat Y.b).2 (j : lat Y.b).2`. Establish `hd : dist (g i) (g j) = c * ‖((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι)‖`. Simplify using `only [g, dist_eq_norm, ← smul_sub, ← map_sub, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_pos hcpos]`. Rewrite using `[hd]`.

Conclude with `hlat _ hmem hij`. Rewrite `hcard` using `[Finset.card_image_of_injective S hg]`. Then use the resulting hypothesis.
-/
theorem paCount (hP : Ext.PackingCount) (Y : GT ι) {q : ℕ} {R0 : ℝ} (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) (R : ℝ) (hR : R0 ≤ R)
    (S : Finset ({γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} : Set (lat Y.b)))
    (hS : ∀ i ∈ S, Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖ ≤ R) :
    (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * Fintype.card ι) := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨i₀, hi₀⟩
  · rw [hS0, Finset.card_empty, Nat.cast_zero]
    have : 0 < R := lt_of_lt_of_le hR0 hR
    positivity
  set c := Real.sqrt (q * Real.pi) with hc
  have hcpos : 0 < c := by
    have h1 := hlat _ (i₀ : lat Y.b).2 i₀.2
    by_contra hle
    rw [not_lt] at hle
    have : c * ‖((i₀ : lat Y.b) : EuclideanSpace ℂ ι)‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (norm_nonneg _)
    linarith
  obtain ⟨e⟩ := (paIso_ex : Nonempty (EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * Fintype.card ι))))
  let g : ({γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} : Set (lat Y.b)) →
      EuclideanSpace ℝ (Fin (2 * Fintype.card ι)) := fun i => c • e ((i : lat Y.b) : EuclideanSpace ℂ ι)
  have hg : Function.Injective g := by
    intro i j hij
    have h1 : e ((i : lat Y.b) : EuclideanSpace ℂ ι) = e ((j : lat Y.b) : EuclideanSpace ℂ ι) :=
      smul_right_injective _ hcpos.ne' hij
    exact Subtype.ext (Subtype.ext (e.injective h1))
  have hcard : ((S.image g).card : ℝ) ≤ (3 * R / R0) ^ (2 * Fintype.card ι) := by
    refine hP (2 * Fintype.card ι) (S.image g) R0 R hR0 hR ?_ ?_
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_pos hcpos]
      exact hS i hi
    · intro x hx y hy hxy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      have hij : ((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι) ≠ 0 := by
        intro h0
        apply hxy
        rw [sub_eq_zero] at h0
        simp only [g, h0]
      have hmem : ((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι) ∈ lat Y.b :=
        Submodule.sub_mem _ (i : lat Y.b).2 (j : lat Y.b).2
      have hd : dist (g i) (g j) =
          c * ‖((i : lat Y.b) : EuclideanSpace ℂ ι) - ((j : lat Y.b) : EuclideanSpace ℂ ι)‖ := by
        simp only [g, dist_eq_norm, ← smul_sub, ← map_sub, norm_smul, LinearIsometryEquiv.norm_map,
          Real.norm_eq_abs, abs_of_pos hcpos]
      rw [hd]
      exact hlat _ hmem hij
  rwa [Finset.card_image_of_injective S hg] at hcard

/- English proof (translation)
Use `set s : Set (lat Y.b) := {γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} with hs`. Set `f : lat Y.b → ℝ` to `fun γ => Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)`. Establish `hfun : (fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then 0 else Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) = s.indicator f`. Use function extensionality and compare the values at `γ`. Distinguish the cases in `h0 : (γ : EuclideanSpace ℂ ι) = 0`.

Establish `: γ ∉ s` using `fun h => h h0`. Rewrite using `[if_pos h0, Set.indicator_of_notMem this]`. Establish `: γ ∈ s` using `h0`. Rewrite using `[if_neg h0, Set.indicator_of_mem this]`. Establish `hqpi : (0 : ℝ) ≤ q * Real.pi` using `by positivity`.

Establish `hh : ∀ i : s, Real.exp (-(Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖) ^ 2 / 16) = f i`. Introduce `i`. Simplify using `only [f]`. Use `congr 1`. Rewrite using `[mul_pow, Real.sq_sqrt hqpi]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨hsum, hle⟩` from `hA s (fun i => Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖) (Fintype.card ι) R0 hR0 hR (fun i => hlat _ (i : lat Y.b).2 i.2) (fun R hR' S hS => paCount hP Y hR0 hlat R hR' S hS)`. Simplify using `only [hh] at hsum hle`. Rewrite using `[hfun]`. Use `⟨(summable_subtype_iff_indicator).1 hsum, ?_⟩` and prove the remaining obligations.

Rewrite using `[← tsum_subtype]`. Conclude with `hle`.
-/
theorem paTail (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2) :
    Summable (fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) ∧
    ∑' γ : lat Y.b, (if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) ≤
      2 * 9 ^ Fintype.card ι * Real.exp (-R0 ^ 2 / 16) := by
  set s : Set (lat Y.b) := {γ : lat Y.b | (γ : EuclideanSpace ℂ ι) ≠ 0} with hs
  let f : lat Y.b → ℝ := fun γ => Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)
  have hfun : (fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) = s.indicator f := by
    funext γ
    by_cases h0 : (γ : EuclideanSpace ℂ ι) = 0
    · have : γ ∉ s := fun h => h h0
      rw [if_pos h0, Set.indicator_of_notMem this]
    · have : γ ∈ s := h0
      rw [if_neg h0, Set.indicator_of_mem this]
  have hqpi : (0 : ℝ) ≤ q * Real.pi := by positivity
  have hh : ∀ i : s, Real.exp (-(Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖) ^ 2 / 16) =
      f i := by
    intro i
    simp only [f]
    congr 1
    rw [mul_pow, Real.sq_sqrt hqpi]
    ring
  obtain ⟨hsum, hle⟩ := hA s (fun i => Real.sqrt (q * Real.pi) * ‖((i : lat Y.b) : EuclideanSpace ℂ ι)‖)
    (Fintype.card ι) R0 hR0 hR (fun i => hlat _ (i : lat Y.b).2 i.2)
    (fun R hR' S hS => paCount hP Y hR0 hlat R hR' S hS)
  simp only [hh] at hsum hle
  rw [hfun]
  refine ⟨(summable_subtype_iff_indicator).1 hsum, ?_⟩
  rw [← tsum_subtype]
  exact hle

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
