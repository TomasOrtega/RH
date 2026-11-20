import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QUniq

def chr {V : Type} [Fintype V] (μ x : V → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ))

/- English proof (translation)
Simplify using `only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]`.
-/
theorem chr_add {V : Type} [Fintype V] (μ x y : V → ℝ) : chr μ (x + y) = chr μ x * chr μ y := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]

/- English proof (translation)
Simplify using `only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.exp_add]`.
-/
theorem chr_add' {V : Type} [Fintype V] (μ ν x : V → ℝ) : chr (μ + ν) x = chr μ x * chr ν x := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.exp_add]

/- English proof (translation)
Simplify using `[chr]`.
-/
theorem chr_zero {V : Type} [Fintype V] (μ : V → ℝ) : chr μ 0 = 1 := by simp [chr]

/- English proof (translation)
Simplify using `[chr]`.
-/
theorem chr_zero' {V : Type} [Fintype V] (x : V → ℝ) : chr 0 x = 1 := by simp [chr]

/- English proof (translation)
Establish `: (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ)) = ((2 * Real.pi * ∑ v, μ v * x v : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[chr, this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_chr {V : Type} [Fintype V] (μ x : V → ℝ) : ‖chr μ x‖ = 1 := by
  have : (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ)) = ((2 * Real.pi * ∑ v, μ v * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [chr, this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Take `⟨v, hv⟩` from `Function.ne_iff.1 h`. Establish `hv' : (μ v : ℂ) ≠ 0` using `by exact_mod_cast hv`. Use `⟨Pi.single v (1 / (2 * μ v)), ?_⟩` and prove the remaining obligations. Establish `: ∑ w, (μ w : ℂ) * ((Pi.single v (1 / (2 * μ v)) : V → ℝ) w : ℂ) = 1 / 2`. Rewrite using `[Finset.sum_eq_single v]`.

Simplify using `only [Pi.single_eq_same]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`.

Simplify using the standard rewrite rules. Rewrite using `[chr, this, ← Complex.exp_pi_mul_I]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_chr {V : Type} [Fintype V] (μ : V → ℝ) (h : μ ≠ 0) : ∃ g, chr μ g = -1 := by
  classical
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  have hv' : (μ v : ℂ) ≠ 0 := by exact_mod_cast hv
  refine ⟨Pi.single v (1 / (2 * μ v)), ?_⟩
  have : ∑ w, (μ w : ℂ) * ((Pi.single v (1 / (2 * μ v)) : V → ℝ) w : ℂ) = 1 / 2 := by
    rw [Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]; push_cast; field_simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  rw [chr, this, ← Complex.exp_pi_mul_I]
  congr 1; ring

/- English proof (translation)
Rewrite using `[show g = f from funext e]` and apply the resulting hypothesis.
-/
theorem hasSum_congr' {ι : Type} {f g : ι → ℂ} {d : ℂ} (h : HasSum f d) (e : ∀ i, g i = f i) : HasSum g d := by
  rwa [show g = f from funext e]

/- English proof (translation)
Establish `h2` using `((h x).add (h (x + g))).div_const 2`. Establish `hd : (d + d) / 2 = d` using `by ring`. Rewrite `h2` using `[hd]`. Use `hasSum_congr' h2 (fun i => ?_)` and prove the remaining obligations. Rewrite using `[chr_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hasSum_average_chr_of_hasSum {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (C : ι → ℂ) (d : ℂ)
    (h : ∀ x, HasSum (fun i => C i * chr (μ i) x) d) (g : V → ℝ) (x : V → ℝ) :
    HasSum (fun i => C i * ((1 + chr (μ i) g) / 2) * chr (μ i) x) d := by
  have h2 := ((h x).add (h (x + g))).div_const 2
  have hd : (d + d) / 2 = d := by ring
  rw [hd] at h2
  refine hasSum_congr' h2 (fun i => ?_)
  rw [chr_add]
  ring

/- English proof (translation)
Rewrite using `[norm_div]`. Establish `h1` using `norm_add_le (1 : ℂ) (chr μ x)`. Rewrite `h1` using `[norm_one, norm_chr]`. Establish `h2 : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite using `[h2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem norm_one_add_chr_div_two_le_one {V : Type} [Fintype V] (μ x : V → ℝ) : ‖(1 + chr μ x) / 2‖ ≤ 1 := by
  rw [norm_div]
  have h1 := norm_add_le (1 : ℂ) (chr μ x)
  rw [norm_one, norm_chr] at h1
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith

/- English proof (translation)
Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Conclude with `⟨B, fun i => le_rfl, by simp, h⟩`. Introduce `j S _ ih`. Take `⟨C, hCn, hCS, hC⟩` from `ih`. Distinguish the cases in `hj : C j = 0`.

Use `⟨C, hCn, fun i hi => ?_, hC⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `hj`. Conclude with `hCS i hi`. Establish `hB : B j ≠ 0`.

Introduce `hB0`. Apply `hj` to reduce the goal to its premises. Establish `h3` using `hCn j`. Rewrite `h3` using `[hB0, norm_zero]`. Conclude with `norm_le_zero_iff.mp h3`.

Take `⟨g, hg⟩` from `exists_chr (μ j) (hμ j hB)`. Use `⟨fun i => C i * ((1 + chr (μ i) g) / 2), fun i => ?_, fun i hi => ?_, fun x => hasSum_average_chr_of_hasSum μ C d hC g x⟩` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one]`.

Conclude with `hCn i`. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Simplify using `[hg]`. Simplify using `[hCS i hi]`.
-/
theorem kill_freq {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) (S : Finset ι) :
    ∃ C : ι → ℂ, (∀ i, ‖C i‖ ≤ ‖B i‖) ∧ (∀ i ∈ S, C i = 0) ∧ ∀ x, HasSum (fun i => C i * chr (μ i) x) d := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨B, fun i => le_rfl, by simp, h⟩
  · intro j S _ ih
    obtain ⟨C, hCn, hCS, hC⟩ := ih
    by_cases hj : C j = 0
    · refine ⟨C, hCn, fun i hi => ?_, hC⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hj
      · exact hCS i hi
    · have hB : B j ≠ 0 := by
        intro hB0
        apply hj
        have h3 := hCn j
        rw [hB0, norm_zero] at h3
        exact norm_le_zero_iff.mp h3
      obtain ⟨g, hg⟩ := exists_chr (μ j) (hμ j hB)
      refine ⟨fun i => C i * ((1 + chr (μ i) g) / 2), fun i => ?_, fun i hi => ?_,
        fun x => hasSum_average_chr_of_hasSum μ C d hC g x⟩
      · rw [norm_mul]
        calc ‖C i‖ * ‖(1 + chr (μ i) g) / 2‖ ≤ ‖C i‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_one_add_chr_div_two_le_one _ _) (norm_nonneg _)
          _ ≤ ‖B i‖ := by
              rw [mul_one]
              exact hCn i
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · simp [hg]
        · simp [hCS i hi]

/- English proof (translation)
Establish `hB : Summable B`. Establish `h0` using `(h 0).summable`. Simplify `h0` using `[chr_zero]`. Establish `hnB : Summable (fun i => ‖B i‖)` using `summable_norm_iff.mpr hB`. Establish `key : ∀ ε > 0, ‖d‖ ≤ ε`.

Introduce `ε hε`. Take `⟨S, hS⟩` from `(summable_iff_vanishing_norm.mp hnB) ε hε`. Take `⟨C, hCn, hCS, hC⟩` from `kill_freq μ B d hμ h S`. Establish `hC0` using `Filter.Tendsto.norm (hC 0)`. Use `le_of_tendsto' hC0 (fun t => ?_)` and prove the remaining obligations.

Simplify using `only [chr_zero, mul_one]`. Establish `e1 : ∑ i ∈ t \ S, C i = ∑ i ∈ t, C i` using `Finset.sum_subset Finset.sdiff_subset (fun i hi hni => hCS i (by`. Rewrite `hni` using `[Finset.mem_sdiff]`. Use the proof step `tauto))`. Rewrite using `[← e1]`.

Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hd`. Establish `hpos : 0 < ‖d‖` using `norm_pos_iff.mpr hd`. Establish `h3` using `key (‖d‖ / 2) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem const_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) : d = 0 := by
  classical
  have hB : Summable B := by
    have h0 := (h 0).summable
    simpa [chr_zero] using h0
  have hnB : Summable (fun i => ‖B i‖) := summable_norm_iff.mpr hB
  have key : ∀ ε > 0, ‖d‖ ≤ ε := by
    intro ε hε
    obtain ⟨S, hS⟩ := (summable_iff_vanishing_norm.mp hnB) ε hε
    obtain ⟨C, hCn, hCS, hC⟩ := kill_freq μ B d hμ h S
    have hC0 := Filter.Tendsto.norm (hC 0)
    refine le_of_tendsto' hC0 (fun t => ?_)
    simp only [chr_zero, mul_one]
    have e1 : ∑ i ∈ t \ S, C i = ∑ i ∈ t, C i :=
      Finset.sum_subset Finset.sdiff_subset (fun i hi hni => hCS i (by
        rw [Finset.mem_sdiff] at hni
        tauto))
    rw [← e1]
    calc ‖∑ i ∈ t \ S, C i‖ ≤ ∑ i ∈ t \ S, ‖C i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ t \ S, ‖B i‖ := Finset.sum_le_sum (fun i _ => hCn i)
      _ ≤ ‖∑ i ∈ t \ S, ‖B i‖‖ := Real.le_norm_self _
      _ ≤ ε := (hS _ Finset.sdiff_disjoint).le
  by_contra hd
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have h3 := key (‖d‖ / 2) (by linarith)
  linarith

/- English proof (translation)
Apply `neg_eq_zero.mp` to reduce the goal to its premises. Apply `const_eq_zero (fun i => μ i + -μ j) (Function.update B j 0) (-B j)` to reduce the goal to its premises. Introduce `i hi h0`. Establish `hij : i ≠ j`. Introduce and unpack `rfl`.

Simplify using `at hi`. Conclude with `hij (hμ (add_neg_eq_zero.mp h0))`. Introduce `x`. Establish `h1` using `((h x).mul_left (chr (-μ j) x)).update j 0`. Establish `hc : chr (-μ j) x * chr (μ j) x = 1`.

Rewrite using `[← chr_add', neg_add_cancel, chr_zero']`. Establish `hval : (0 - chr (-μ j) x * (B j * chr (μ j) x) + chr (-μ j) x * 0) = -B j`. Take the linear combination `(-B j) * hc`. Rewrite `h1` using `[hval]`. Use `hasSum_congr' h1 (fun i => ?_)` and prove the remaining obligations.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hij, Function.update_of_ne hij, chr_add']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (hμ : Function.Injective μ)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) 0) (j : ι) : B j = 0 := by
  classical
  apply neg_eq_zero.mp
  apply const_eq_zero (fun i => μ i + -μ j) (Function.update B j 0) (-B j)
  · intro i hi h0
    have hij : i ≠ j := by
      rintro rfl
      simp at hi
    exact hij (hμ (add_neg_eq_zero.mp h0))
  · intro x
    have h1 := ((h x).mul_left (chr (-μ j) x)).update j 0
    have hc : chr (-μ j) x * chr (μ j) x = 1 := by
      rw [← chr_add', neg_add_cancel, chr_zero']
    have hval : (0 - chr (-μ j) x * (B j * chr (μ j) x) + chr (-μ j) x * 0) = -B j := by
      linear_combination (-B j) * hc
    rw [hval] at h1
    refine hasSum_congr' h1 (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Function.update_of_ne hij, Function.update_of_ne hij, chr_add']
      ring

end GlobalTheory.HilbertThetaSeries.QUniq

/- English proof (translation)
Simplify using `only [ez, GlobalTheory.HilbertThetaSeries.QUniq.chr, UpperHalfPlane.coe_mk]`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Simplify using `only [mul_add, Finset.sum_add_distrib]`.
-/
private theorem ez_at_imaginary_unit_shift_eq {F : Type} [Field F] [NumberField F] (ζ : F) (x : InfinitePlace F → ℝ) :
    ez ζ (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)) =
      GlobalTheory.HilbertThetaSeries.QUniq.chr (fun v => reAt v ζ) x *
        Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I) := by
  simp only [ez, GlobalTheory.HilbertThetaSeries.QUniq.chr, UpperHalfPlane.coe_mk]
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]

open GlobalTheory.HilbertThetaSeries.QUniq in

/- English proof (translation)
Introduce `F _ _ _ f a b ha hb`. Use function extensionality and compare the values at `ξ`. Establish `hinj : Function.Injective (fun ζ : F => fun v : InfinitePlace F => reAt v ζ)`. Introduce `ζ η hζη`. Take `⟨v⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `hv` using `IsTotallyReal.isReal v`. Establish `h1` using `congrFun hζη v`. Simplify using `only [reAt] at h1`. Apply `(InfinitePlace.embedding_of_isReal hv).injective` to reduce the goal to its premises. Rewrite `h1` using `[← InfinitePlace.embedding_of_isReal_apply hv ζ, ← InfinitePlace.embedding_of_isReal_apply hv η, Complex.ofReal_re, Complex.ofReal_re]`.

Conclude with `h1`. Establish `hsum : ∀ x : InfinitePlace F → ℝ, HasSum (fun ζ => ((a ζ - b ζ) * Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I)) * chr (fun v => reAt v ζ) x) 0`. Introduce `x`. Establish `h2` using `(ha.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp))).sub (hb.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)))`. Rewrite `h2` using `[sub_self]`.

Use `hasSum_congr' h2 (fun ζ => ?_)` and prove the remaining obligations. Simplify using `only [ez_at_imaginary_unit_shift_eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `coef_eq_zero (fun ζ : F => fun v => reAt v ζ) _ hinj hsum ξ`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (Complex.exp_ne_zero _))`.
-/
theorem GlobalTheory.HilbertThetaSeries.hasQ_unique : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ f b → a = b := by
  intro F _ _ _ f a b ha hb
  funext ξ
  have hinj : Function.Injective (fun ζ : F => fun v : InfinitePlace F => reAt v ζ) := by
    intro ζ η hζη
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hv := IsTotallyReal.isReal v
    have h1 := congrFun hζη v
    simp only [reAt] at h1
    apply (InfinitePlace.embedding_of_isReal hv).injective
    rw [← InfinitePlace.embedding_of_isReal_apply hv ζ, ← InfinitePlace.embedding_of_isReal_apply hv η,
      Complex.ofReal_re, Complex.ofReal_re] at h1
    exact h1
  have hsum : ∀ x : InfinitePlace F → ℝ, HasSum (fun ζ => ((a ζ - b ζ) *
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I)) *
        chr (fun v => reAt v ζ) x) 0 := by
    intro x
    have h2 := (ha.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp))).sub
      (hb.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)))
    rw [sub_self] at h2
    refine hasSum_congr' h2 (fun ζ => ?_)
    simp only [ez_at_imaginary_unit_shift_eq]
    ring
  have key := coef_eq_zero (fun ζ : F => fun v => reAt v ζ) _ hinj hsum ξ
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (Complex.exp_ne_zero _))
