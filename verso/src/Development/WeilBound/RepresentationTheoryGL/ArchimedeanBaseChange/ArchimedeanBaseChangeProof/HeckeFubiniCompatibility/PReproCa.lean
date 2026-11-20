import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG.ReproL

/- English proof (translation)
Establish `h1` using `Complex.norm_exp_sub_one_le hz`. Establish `h2` using `Complex.norm_exp_sub_one_le (x := -z) (by rwa [norm_neg])`. Rewrite `h2` using `[norm_neg]`. Establish `e : Complex.cosh z - 1 = ((Complex.exp z - 1) + (Complex.exp (-z) - 1)) / 2`. Rewrite using `[show Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 from rfl]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_div]`. Establish `h3` using `norm_add_le (Complex.exp z - 1) (Complex.exp (-z) - 1)`. Establish `h4 : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite using `[h4]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_cosh_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Complex.cosh z - 1‖ ≤ 2 * ‖z‖ := by
  have h1 := Complex.norm_exp_sub_one_le hz
  have h2 := Complex.norm_exp_sub_one_le (x := -z) (by rwa [norm_neg])
  rw [norm_neg] at h2
  have e : Complex.cosh z - 1 = ((Complex.exp z - 1) + (Complex.exp (-z) - 1)) / 2 := by
    rw [show Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 from rfl]; ring
  rw [e, norm_div]
  have h3 := norm_add_le (Complex.exp z - 1) (Complex.exp (-z) - 1)
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4]
  linarith

/- English proof (translation)
Establish `hA : ∀ f : Inf N → Fin N → ℂ, Continuous f → Continuous fun χ => Formalism.REAL.Amat (f χ)`. Introduce `f hf`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [Formalism.REAL.Amat, Matrix.of_apply]`. Use `split_ifs`.

Conclude with `(continuous_apply a).comp hf`. Conclude with `continuous_const`. Conclude with `continuous_const`. Establish `hg : ∀ s : Bool, Continuous fun χ : Inf N => GlobalTheory.Dec.gelfVal (χ s) 2`. Introduce `s`.

Unfold `GlobalTheory.Dec.gelfVal`. Use `continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_` and prove the remaining obligations. Establish `hf : Continuous fun χ : Inf N => fun c : Fin N => χ s c + ((N : ℂ) - 1) / 2` using `continuous_pi fun c => (continuous_apply_apply s c).add continuous_const`. Conclude with `((hA _ hf).pow 2).matrix_elem a b`. Unfold `cas`.

Conclude with `continuous_const.mul ((hg true).add (hg false))`.
-/
theorem continuous_cas (N : ℕ) : Continuous fun χ : Inf N => cas χ := by
  have hA : ∀ f : Inf N → Fin N → ℂ, Continuous f → Continuous fun χ => Formalism.REAL.Amat (f χ) := by
    intro f hf
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply a).comp hf
    · exact continuous_const
    · exact continuous_const
  have hg : ∀ s : Bool, Continuous fun χ : Inf N => GlobalTheory.Dec.gelfVal (χ s) 2 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    have hf : Continuous fun χ : Inf N => fun c : Fin N => χ s c + ((N : ℂ) - 1) / 2 :=
      continuous_pi fun c => (continuous_apply_apply s c).add continuous_const
    exact ((hA _ hf).pow 2).matrix_elem a b
  unfold cas
  exact continuous_const.mul ((hg true).add (hg false))

/- English proof (translation)
Establish `hS : IsCompact {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R}`. Establish `e : {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} = Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R`. Use extensionality with `χ`. Simplify using `[Set.mem_pi]`. Rewrite using `[e]`.

Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Take `⟨C, hC⟩` from `hS.exists_bound_of_continuousOn (continuous_cas N).continuousOn`. Use `set C' := max C 0 with hC'`. Establish `hC'0 : 0 ≤ C'` using `le_max_right _ _`. Use `set s := Real.sqrt C' with hs`.

Establish `hs0 : 0 ≤ s` using `Real.sqrt_nonneg _`. Use `set T : ℝ := 1 / (4 * (s + 1)) with hT`. Establish `hT0 : 0 < T` using `by positivity`. Establish `hTs : T * s ≤ 1 / 4`. Rewrite using `[hT, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]`.

Use the polynomial consequences of the given equalities and inequalities. Set `f : ContDiffBump (0 : ℝ)` to `⟨T / 2, T, by positivity, by linarith⟩`. Use `set g : ℝ → ℝ := f.normed volume with hg`. Establish `hsupp : ∀ t, g t ≠ 0 → |t| < T`. Introduce `t ht`.

Establish `: t ∈ Function.support g` using `ht`. Rewrite `this` using `[hg, ContDiffBump.support_normed_eq]`. Simplify `this` using `[Metric.mem_ball, Real.dist_eq]`. Use `⟨g, T, hT0, ⟨ContDiffBump.contDiff_normed f, fun t => ?_, fun t ht => ?_⟩, ?_⟩` and prove the remaining obligations. Use `ContDiffBump.normed_neg f (μ := volume) t` as an intermediate fact.

Simplify `this` using `[hg]`. Assume the negation of the conclusion as `h`. Conclude with `absurd (hsupp t h) (not_lt.2 ht.le)`. Introduce `χ hχ`. Use `set c := cas χ with hc`.

Establish `hcC : ‖c‖ ≤ C'` using `(hC χ hχ).trans (le_max_left _ _)`. Establish `hroot : ‖c ^ (1 / 2 : ℂ)‖ ≤ s`. Establish `e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, hs]`. Conclude with `Real.sqrt_le_sqrt hcC`.

Establish `hgc : Continuous g` using `(ContDiffBump.contDiff_normed f (n := 0)).continuous`. Establish `hgcs : HasCompactSupport g` using `ContDiffBump.hasCompactSupport_normed f`. Establish `hgC : HasCompactSupport fun t => (g t : ℂ)` using `hgcs.comp_left Complex.ofReal_zero`. Establish `hcont1 : Continuous fun t : ℝ => Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))` using `Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)`. Establish `hi1 : Integrable fun t : ℝ => (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))` using `((Complex.continuous_ofReal.comp hgc).mul hcont1).integrable_of_hasCompactSupport (hgC.mul_right)`.

Establish `hi2 : Integrable fun t : ℝ => (g t : ℂ)` using `(Complex.continuous_ofReal.comp hgc).integrable_of_hasCompactSupport hgC`. Establish `hone : ∫ t, (g t : ℂ) = 1`. Rewrite using `[integral_complex_ofReal, hg, ContDiffBump.integral_normed]`. Simplify using the standard rewrite rules. Establish `h3 : ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) = (∫ t, (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))) - ∫ t, (g t : ℂ)`.

Rewrite using `[← integral_sub hi1 hi2]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree. Establish `hdiff : coshT g c - 1 = ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)`.

Rewrite using `[h3, hone]`. Both sides reduce to the same expression. Establish `hbound : ∀ t, ‖(g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ g t * (1 / 2)`. Introduce `t`. Distinguish the cases in `h0 : g t = 0`.

Simplify using `[h0]`. Establish `ht` using `hsupp t h0`. Establish `hz : ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ ≤ 1 / 4`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hgt : 0 ≤ g t` using `ContDiffBump.nonneg_normed f t`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgt]`. Use `mul_le_mul_of_nonneg_left ?_ hgt` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hle : ‖coshT g c - 1‖ ≤ 1 / 2`.

Rewrite using `[hdiff]`. Combine the equalities or inequalities in the displayed calculation. Use `norm_sub_norm_le (1 : ℂ) (1 - coshT g c)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel, norm_one, norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bump (N : ℕ) (R : ℝ) : ∃ (g : ℝ → ℝ) (T : ℝ), 0 < T ∧ IsBump g T ∧
    ∀ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) → 1 / 2 ≤ ‖coshT g (cas χ)‖ := by
  have hS : IsCompact {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} := by
    have e : {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} =
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R := by
      ext χ; simp [Set.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_cas N).continuousOn
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set s := Real.sqrt C' with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set T : ℝ := 1 / (4 * (s + 1)) with hT
  have hT0 : 0 < T := by positivity
  have hTs : T * s ≤ 1 / 4 := by
    rw [hT, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  let f : ContDiffBump (0 : ℝ) := ⟨T / 2, T, by positivity, by linarith⟩
  set g : ℝ → ℝ := f.normed volume with hg
  have hsupp : ∀ t, g t ≠ 0 → |t| < T := by
    intro t ht
    have : t ∈ Function.support g := ht
    rw [hg, ContDiffBump.support_normed_eq] at this
    simpa [Metric.mem_ball, Real.dist_eq] using this
  refine ⟨g, T, hT0, ⟨ContDiffBump.contDiff_normed f, fun t => ?_, fun t ht => ?_⟩, ?_⟩
  · have := ContDiffBump.normed_neg f (μ := volume) t
    simpa [hg] using this
  · by_contra h
    exact absurd (hsupp t h) (not_lt.2 ht.le)
  intro χ hχ
  set c := cas χ with hc
  have hcC : ‖c‖ ≤ C' := (hC χ hχ).trans (le_max_left _ _)
  have hroot : ‖c ^ (1 / 2 : ℂ)‖ ≤ s := by
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, hs]
    exact Real.sqrt_le_sqrt hcC
  have hgc : Continuous g := (ContDiffBump.contDiff_normed f (n := 0)).continuous
  have hgcs : HasCompactSupport g := ContDiffBump.hasCompactSupport_normed f
  have hgC : HasCompactSupport fun t => (g t : ℂ) := hgcs.comp_left Complex.ofReal_zero
  have hcont1 : Continuous fun t : ℝ => Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)
  have hi1 : Integrable fun t : ℝ => (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    ((Complex.continuous_ofReal.comp hgc).mul hcont1).integrable_of_hasCompactSupport (hgC.mul_right)
  have hi2 : Integrable fun t : ℝ => (g t : ℂ) :=
    (Complex.continuous_ofReal.comp hgc).integrable_of_hasCompactSupport hgC
  have hone : ∫ t, (g t : ℂ) = 1 := by
    rw [integral_complex_ofReal, hg, ContDiffBump.integral_normed]; simp
  have h3 : ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) =
      (∫ t, (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))) - ∫ t, (g t : ℂ) := by
    rw [← integral_sub hi1 hi2]; congr 1; funext t; ring
  have hdiff : coshT g c - 1 = ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) := by
    rw [h3, hone]; rfl
  have hbound : ∀ t, ‖(g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ g t * (1 / 2) := by
    intro t
    by_cases h0 : g t = 0
    · simp [h0]
    have ht := hsupp t h0
    have hz : ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |t| * ‖c ^ (1 / 2 : ℂ)‖ ≤ T * s := mul_le_mul ht.le hroot (norm_nonneg _) hT0.le
        _ ≤ 1 / 4 := hTs
    have hgt : 0 ≤ g t := ContDiffBump.nonneg_normed f t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgt]
    refine mul_le_mul_of_nonneg_left ?_ hgt
    calc ‖Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1‖ ≤ 2 * ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ :=
          norm_cosh_sub_one_le (hz.trans (by norm_num))
      _ ≤ 1 / 2 := by linarith
  have hle : ‖coshT g c - 1‖ ≤ 1 / 2 := by
    rw [hdiff]
    calc ‖∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ ∫ t, g t * (1 / 2) :=
          norm_integral_le_of_norm_le ((hgc.mul continuous_const).integrable_of_hasCompactSupport hgcs.mul_right)
            (Filter.Eventually.of_forall hbound)
      _ = 1 / 2 := by rw [integral_mul_const, hg, ContDiffBump.integral_normed]; ring
  have := norm_sub_norm_le (1 : ℂ) (1 - coshT g c)
  rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
  linarith

/- English proof (translation)
Substitute `h` using the available equality. Use `⟨fun i => m.toList.get (Fin.cast (by simp) i), ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map]`. Establish `e : List.ofFn (fun i : Fin (Multiset.card m) => m.toList.get (Fin.cast (by simp) i)) = m.toList` using `List.ext_get (by simp) (by simp)`. Rewrite using `[e, Multiset.coe_toList]`.
-/
theorem exists_enum {N : ℕ} (m : Multiset ℂ) (h : Multiset.card m = N) :
    ∃ e : Fin N → ℂ, Multiset.map e Finset.univ.val = m := by
  subst h
  refine ⟨fun i => m.toList.get (Fin.cast (by simp) i), ?_⟩
  rw [Fin.univ_val_map]
  have e : List.ofFn (fun i : Fin (Multiset.card m) => m.toList.get (Fin.cast (by simp) i)) = m.toList :=
    List.ext_get (by simp) (by simp)
  rw [e, Multiset.coe_toList]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

/- English proof (translation)
Take `⟨m1, h1, b1⟩` from `hR v.embedding`. Take `⟨m2, h2, b2⟩` from `hR (ComplexEmbedding.conjugate v.embedding)`. Take `⟨e1, he1⟩` from `exists_enum m1 h1.1`. Take `⟨e2, he2⟩` from `exists_enum m2 h2.1`. Use `⟨fun s => if s then e1 else e2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s i`. Consider the cases of `s`. Conclude with `b2 _ (he2 ▸ Multiset.mem_map_of_mem e2 (Finset.mem_univ_val i))`. Conclude with `b1 _ (he1 ▸ Multiset.mem_map_of_mem e1 (Finset.mem_univ_val i))`. Introduce `g`.

Establish `key` using `(hB E N (Submodule.span ℂ {φ}) v (fun s => if s then e1 else e2)).2 ⟨by simpa [he1] using h1, by simpa [he2] using h2⟩`. Conclude with `key φ (Submodule.mem_span_singleton_self φ) g`.
-/
theorem exists_chi (hB : Bridge.BridgeSt) (R : ℝ) (v : InfinitePlace E) (φ : Sm E N)
    (hR : PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ})) :
    ∃ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) ∧ ∀ g : GA E N, IsEig χ (Bridge.along v g φ.1) := by
  obtain ⟨m1, h1, b1⟩ := hR v.embedding
  obtain ⟨m2, h2, b2⟩ := hR (ComplexEmbedding.conjugate v.embedding)
  obtain ⟨e1, he1⟩ := exists_enum m1 h1.1
  obtain ⟨e2, he2⟩ := exists_enum m2 h2.1
  refine ⟨fun s => if s then e1 else e2, ?_, ?_⟩
  · intro s i
    cases s
    · exact b2 _ (he2 ▸ Multiset.mem_map_of_mem e2 (Finset.mem_univ_val i))
    · exact b1 _ (he1 ▸ Multiset.mem_map_of_mem e1 (Finset.mem_univ_val i))
  · intro g
    have key := (hB E N (Submodule.span ℂ {φ}) v (fun s => if s then e1 else e2)).2
      ⟨by simpa [he1] using h1, by simpa [he2] using h2⟩
    exact key φ (Submodule.mem_span_singleton_self φ) g

end PositivityTheory.Rg.BcB.CG.ReproL
