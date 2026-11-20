import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStartA

noncomputable section

open Formalism.REAL Matrix MeasureTheory

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Set `S : Set C(Γ, ℂ)` to `{g | ∃ τ i j, (g : Γ → ℂ) = fun k => κ τ k i j}`. Set `A : StarSubalgebra ℂ C(Γ, ℂ)` to `StarAlgebra.adjoin ℂ S`. Establish `hsep : A.SeparatesPoints`. Introduce `x y hxy`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, κ τ x ≠ κ τ y := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hxy (hK.sep x y h)`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, κ τ x i j ≠ κ τ y i j := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hτ (Matrix.ext h)`. Conclude with `⟨fun k => κ τ k i j, ⟨⟨fun k => κ τ k i j, hK.cont τ i j⟩, StarAlgebra.subset_adjoin ℂ S ⟨τ, i, j, rfl⟩, rfl⟩, hij⟩`. Establish `hsub : A.toSubalgebra ≤ (monoAlg hK H).comap (ContinuousMap.coeFnAlgHom ℂ)`. Rewrite using `[StarAlgebra.adjoin_toSubalgebra]`.

Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `g (hg | hg)`. Take `⟨τ, i, j, hg⟩` from `hg show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)`. Rewrite using `[hg]`. Conclude with `entry_mem hK hH τ i j`.

Take `⟨τ, i, j, hg⟩` from `Set.mem_star.1 hg show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)`. Establish `: (g : Γ → ℂ) = fun k => κ (bar τ) k i j`. Use function extensionality and compare the values at `k`. Establish `h1` using `congrFun hg k`. Simplify using `only [ContinuousMap.star_apply] at h1`.

Rewrite using `[hK.conj, ← h1, star_star]`. Rewrite using `[this]`. Conclude with `entry_mem hK hH (bar τ) i j`. Establish `hle : ∀ h ∈ A, ⇑h ∈ Submodule.span ℂ (Mono κ H)` using `fun h hh => hsub hh`. Establish `htop` using `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep`.

Establish `hg : g ∈ A.topologicalClosure` using `by rw [htop]; exact StarSubalgebra.mem_top`. Rewrite `hg` using `[← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe]`. Conclude with `closure_mono (fun h hh => hle h hh) hg`.
-/
theorem dense [CompactSpace Γ] [T2Space Γ] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    (g : C(Γ, ℂ)) : g ∈ closure {h : C(Γ, ℂ) | ⇑h ∈ Submodule.span ℂ (Mono κ H)} := by
  let S : Set C(Γ, ℂ) := {g | ∃ τ i j, (g : Γ → ℂ) = fun k => κ τ k i j}
  let A : StarSubalgebra ℂ C(Γ, ℂ) := StarAlgebra.adjoin ℂ S
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨τ, hτ⟩ : ∃ τ, κ τ x ≠ κ τ y := by
      by_contra h
      push Not at h
      exact hxy (hK.sep x y h)
    obtain ⟨i, j, hij⟩ : ∃ i j, κ τ x i j ≠ κ τ y i j := by
      by_contra h
      push Not at h
      exact hτ (Matrix.ext h)
    exact ⟨fun k => κ τ k i j, ⟨⟨fun k => κ τ k i j, hK.cont τ i j⟩,
      StarAlgebra.subset_adjoin ℂ S ⟨τ, i, j, rfl⟩, rfl⟩, hij⟩
  have hsub : A.toSubalgebra ≤ (monoAlg hK H).comap (ContinuousMap.coeFnAlgHom ℂ) := by
    rw [StarAlgebra.adjoin_toSubalgebra]
    apply Algebra.adjoin_le
    rintro g (hg | hg)
    · obtain ⟨τ, i, j, hg⟩ := hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      rw [hg]
      exact entry_mem hK hH τ i j
    · obtain ⟨τ, i, j, hg⟩ := Set.mem_star.1 hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      have : (g : Γ → ℂ) = fun k => κ (bar τ) k i j := by
        funext k
        have h1 := congrFun hg k
        simp only [ContinuousMap.star_apply] at h1
        rw [hK.conj, ← h1, star_star]
      rw [this]
      exact entry_mem hK hH (bar τ) i j
  have hle : ∀ h ∈ A, ⇑h ∈ Submodule.span ℂ (Mono κ H) := fun h hh => hsub hh
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hg : g ∈ A.topologicalClosure := by rw [htop]; exact StarSubalgebra.mem_top
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hg
  exact closure_mono (fun h hh => hle h hh) hg

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hspan : ∀ g ∈ Submodule.span ℂ (Mono κ H), Continuous g ∧ ∫ k, g k * f k ∂μ = 0`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`.

Consider the case `mem g hg`. Use `⟨?_, hcon g hg⟩` and prove the remaining obligations. Take `⟨m, lab, c, I, K, -, rfl⟩` from `hg`. Conclude with `mono_cont hK lab c I K`. Consider the case `zero => exact ⟨continuous_const, by simp⟩`.

Consider the case `add g g' _ _ h h'`. Use `⟨h.1.add h'.1, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, add_mul]`. Rewrite using `[integral_add (integrable_of_cont μ (f := fun k => g k * f k) (h.1.mul hf)) (integrable_of_cont μ (f := fun k => g' k * f k) (h'.1.mul hf)), h.2, h'.2, add_zero]`. Consider the case `smul a g _ h`.

Use `⟨h.1.const_smul a, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc]`. Rewrite using `[integral_const_mul, h.2, mul_zero]`. Set `F : C(Γ, ℂ)` to `⟨fun k => star (f k), hf.star⟩`. Set `f' : C(Γ, ℂ)` to `⟨f, hf⟩`.

Establish `hclose` using `dense hK hH F`. Establish `hbound : ∀ ε > 0, ‖∫ k, F k * f k ∂μ‖ ≤ ε * (‖f'‖ * μ.real Set.univ)`. Introduce `ε hε`. Take `⟨b, hb, hdist⟩` from `Metric.mem_closure_iff.1 hclose ε hε`. Establish `hb'` using `hspan b hb`.

Establish `heq : ∫ k, F k * f k ∂μ = ∫ k, (F k - b k) * f k ∂μ`. Rewrite using `[← sub_zero (∫ k, F k * f k ∂μ), ← hb'.2, ← integral_sub (integrable_of_cont μ (f := fun k => F k * f k) (F.continuous.mul hf)) (integrable_of_cont μ (f := fun k => b k * f k) (b.continuous.mul hf))]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq, ← mul_assoc]`. Use `norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h1 : ‖F k - b k‖ ≤ ε`. Use `ContinuousMap.norm_coe_le_norm (F - b) k` as an intermediate fact.

Rewrite `hdist` using `[dist_eq_norm]`. Simplify using `only [ContinuousMap.sub_apply] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ‖f k‖ ≤ ‖f'‖` using `ContinuousMap.norm_coe_le_norm f' k`. Conclude with `mul_le_mul h1 h2 (norm_nonneg _) hε.le`.

Establish `hzero : ∫ k, F k * f k ∂μ = 0`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖∫ k, F k * f k ∂μ‖` using `norm_pos_iff.2 hne`. Use `set C := ‖f'‖ * μ.real Set.univ`. Establish `hC : 0 ≤ C` using `mul_nonneg (norm_nonneg _) measureReal_nonneg`.

Use `set x := ‖∫ k, F k * f k ∂μ‖`. Use `hbound (x / (2 * (C + 1))) (by positivity)` as an intermediate fact. Establish `h3 : x / (2 * (C + 1)) * C ≤ x / 2`. Rewrite using `[div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre : ∀ k, F k * f k = ((‖f k‖ ^ 2 : ℝ) : ℂ)`. Introduce `k`. Simplify using `only [F, ContinuousMap.coe_mk]`. Rewrite using `[Complex.ofReal_pow]`.

Conclude with `RCLike.conj_mul (f k)`. Rewrite `hzero` using `[hre, integral_complex_ofReal, Complex.ofReal_eq_zero]`. Establish `hint : Integrable (fun k => ‖f k‖ ^ 2) μ`. Use `(integrable_of_cont μ (f := fun k => ((‖f k‖ ^ 2 : ℝ) : ℂ)) (by fun_prop)).re` as an intermediate fact. Conclude with `this`.

Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖f k‖) hint).1 hzero`. Establish `hfun` using `(Continuous.ae_eq_iff_eq μ (by fun_prop) continuous_const).1 hae`. Establish `h0 : ‖f x‖ ^ 2 = 0` using `congrFun hfun x`. Conclude with `hx (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))`.
-/
theorem nonvanish [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] [T2Space Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    {f : Γ → ℂ} (hf : Continuous f) (x : Γ) (hx : f x ≠ 0) : ∃ g ∈ Mono κ H, ∫ k, g k * f k ∂μ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hspan : ∀ g ∈ Submodule.span ℂ (Mono κ H), Continuous g ∧ ∫ k, g k * f k ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      refine ⟨?_, hcon g hg⟩
      obtain ⟨m, lab, c, I, K, -, rfl⟩ := hg
      exact mono_cont hK lab c I K
    | zero => exact ⟨continuous_const, by simp⟩
    | add g g' _ _ h h' =>
      refine ⟨h.1.add h'.1, ?_⟩
      simp only [Pi.add_apply, add_mul]
      rw [integral_add (integrable_of_cont μ (f := fun k => g k * f k) (h.1.mul hf))
        (integrable_of_cont μ (f := fun k => g' k * f k) (h'.1.mul hf)), h.2, h'.2,
        add_zero]
    | smul a g _ h =>
      refine ⟨h.1.const_smul a, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2, mul_zero]
  let F : C(Γ, ℂ) := ⟨fun k => star (f k), hf.star⟩
  let f' : C(Γ, ℂ) := ⟨f, hf⟩
  have hclose := dense hK hH F
  have hbound : ∀ ε > 0, ‖∫ k, F k * f k ∂μ‖ ≤ ε * (‖f'‖ * μ.real Set.univ) := by
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hclose ε hε
    have hb' := hspan b hb
    have heq : ∫ k, F k * f k ∂μ = ∫ k, (F k - b k) * f k ∂μ := by
      rw [← sub_zero (∫ k, F k * f k ∂μ), ← hb'.2, ← integral_sub
        (integrable_of_cont μ (f := fun k => F k * f k) (F.continuous.mul hf))
        (integrable_of_cont μ (f := fun k => b k * f k) (b.continuous.mul hf))]
      congr 1
      funext k
      ring
    rw [heq, ← mul_assoc]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [norm_mul]
    have h1 : ‖F k - b k‖ ≤ ε := by
      have := ContinuousMap.norm_coe_le_norm (F - b) k
      rw [dist_eq_norm] at hdist
      simp only [ContinuousMap.sub_apply] at this
      linarith
    have h2 : ‖f k‖ ≤ ‖f'‖ := ContinuousMap.norm_coe_le_norm f' k
    exact mul_le_mul h1 h2 (norm_nonneg _) hε.le
  have hzero : ∫ k, F k * f k ∂μ = 0 := by
    by_contra hne
    have hpos : 0 < ‖∫ k, F k * f k ∂μ‖ := norm_pos_iff.2 hne
    set C := ‖f'‖ * μ.real Set.univ
    have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) measureReal_nonneg
    set x := ‖∫ k, F k * f k ∂μ‖
    have := hbound (x / (2 * (C + 1))) (by positivity)
    have h3 : x / (2 * (C + 1)) * C ≤ x / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hre : ∀ k, F k * f k = ((‖f k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [F, ContinuousMap.coe_mk]
    rw [Complex.ofReal_pow]
    exact RCLike.conj_mul (f k)
  simp_rw [hre, integral_complex_ofReal, Complex.ofReal_eq_zero] at hzero
  have hint : Integrable (fun k => ‖f k‖ ^ 2) μ := by
    have := (integrable_of_cont μ (f := fun k => ((‖f k‖ ^ 2 : ℝ) : ℂ)) (by fun_prop)).re
    exact this
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖f k‖) hint).1 hzero
  have hfun := (Continuous.ae_eq_iff_eq μ (by fun_prop) continuous_const).1 hae
  have h0 : ‖f x‖ ^ 2 = 0 := congrFun hfun x
  exact hx (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))

end SWS

end PositivityTheory.Rg.Cz

end
