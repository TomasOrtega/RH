import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.AdelicParseval

/- English proof (translation)
Establish `hr` using `hv.orthogonalFamily.range_linearIsometry`. Establish `hle : Submodule.span ℂ (Set.range v) ≤ ⨆ i, LinearMap.range (LinearIsometry.toSpanSingleton ℂ H (hv.1 i)).toLinearMap`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Use `Submodule.mem_iSup_of_mem a ⟨1, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hx'` using `Submodule.topologicalClosure_mono hle hx`. Rewrite `hx'` using `[← hr]`. Take `⟨c, rfl⟩` from `hx'`. Apply the tactic sequence `have hs := hv.orthogonalFamily.hasSum_linearIsometry c`.

Apply the tactic sequence `have hc : ∀ a, inner ℂ (v a) (hv.orthogonalFamily.linearIsometry c) = c a := by`. Introduce `a`. Establish `h1` using `(innerSL ℂ (v a)).hasSum hs`. Establish `h2 : HasSum (fun b => innerSL ℂ (v a) (LinearIsometry.toSpanSingleton ℂ H (hv.1 b) (c b))) (c a)`. Use `hasSum_ite_eq a (c a) using 2 with b` and compare the differences between its conclusion and the goal.

Simplify using `only [LinearIsometry.toSpanSingleton_apply, innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.1 hv a b]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Conclude with `h1.unique h2`. Establish `hn` using `lp.hasSum_norm (p := 2) (by simp) c`. Simplify using `only [LinearIsometry.coe_toLinearMap, hc, LinearIsometry.norm_map]`. Simplify using `using hn`.
-/
theorem hasSum_sq_inner_of_mem_closure {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {v : A → H} (hv : Orthonormal ℂ v) {x : H}
    (hx : x ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    HasSum (fun a => ‖inner ℂ (v a) x‖ ^ 2) (‖x‖ ^ 2) := by
  classical
  have hr := hv.orthogonalFamily.range_linearIsometry
  have hle : Submodule.span ℂ (Set.range v) ≤
      ⨆ i, LinearMap.range (LinearIsometry.toSpanSingleton ℂ H (hv.1 i)).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.mem_iSup_of_mem a ⟨1, ?_⟩
    simp
  have hx' := Submodule.topologicalClosure_mono hle hx
  rw [← hr] at hx'
  obtain ⟨c, rfl⟩ := hx'
  have hs := hv.orthogonalFamily.hasSum_linearIsometry c
  have hc : ∀ a, inner ℂ (v a) (hv.orthogonalFamily.linearIsometry c) = c a := by
    intro a
    have h1 := (innerSL ℂ (v a)).hasSum hs
    have h2 : HasSum (fun b => innerSL ℂ (v a) (LinearIsometry.toSpanSingleton ℂ H (hv.1 b) (c b))) (c a) := by
      convert hasSum_ite_eq a (c a) using 2 with b
      simp only [LinearIsometry.toSpanSingleton_apply, innerSL_apply_apply, inner_smul_right,
        orthonormal_iff_ite.1 hv a b]
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    exact h1.unique h2
  have hn := lp.hasSum_norm (p := 2) (by simp) c
  simp only [LinearIsometry.coe_toLinearMap, hc, LinearIsometry.norm_map]
  simpa using hn

/- English proof (translation)
Set `T : C(X, ℂ) →L[ℂ] Lp ℂ 2 m` to `ContinuousMap.toLp 2 m ℂ`. Establish `hT : ∀ p q : C(X, ℂ), inner ℂ (T p) (T q) = ∫ x, (starRingEnd ℂ) (p x) * q x ∂m`. Introduce `p q`. Rewrite using `[ContinuousMap.inner_toLp]`. Simplify using `only [mul_comm]`.

Set `V : Submodule ℂ C(X, ℂ)` to `Submodule.span ℂ (Set.range e)`. Establish `hV1 : (1 : C(X, ℂ)) ∈ V` using `Submodule.subset_span h1`. Establish `hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V`. Introduce `p hp q hq`. Establish `: V * V ≤ V`.

Rewrite using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩`. Conclude with `hmul a b`. Conclude with `this (Submodule.mul_mem_mul hp hq)`.

Establish `hVstar : ∀ p ∈ V, star p ∈ V`. Introduce `p hp`. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span (hstar a)`. Consider the case `zero => rw [star_zero]`. Conclude with `V.zero_mem`. Consider the case `add x y _ _ hx hy => rw [star_add]`. Conclude with `V.add_mem hx hy`.

Consider the case `smul c x _ hx => rw [star_smul]`. Conclude with `V.smul_mem _ hx`. Set `S : StarSubalgebra ℂ C(X, ℂ)` to `{ toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq) star_mem' := fun {p} hp => hVstar p hp }`. Establish `hS : S.topologicalClosure = ⊤`. Use `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_` and prove the remaining obligations.

Introduce `x y hxy`. Take `⟨a, ha⟩` from `hsep x y hxy`. Conclude with `⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ha⟩`. Establish `hv : Orthonormal ℂ (fun a => T (e a))`. Rewrite using `[orthonormal_iff_ite]`.

Introduce `a b`. Rewrite using `[hT, horth]`. Set `W` to `(Submodule.span ℂ (Set.range fun a => T (e a))).topologicalClosure`. Establish `hcl : IsClosed {p : C(X, ℂ) | T p ∈ W}` using `(Submodule.isClosed_topologicalClosure _).preimage T.continuous`. Establish `hsub : (S : Set C(X, ℂ)) ⊆ {p : C(X, ℂ) | T p ∈ W}`.

Introduce `p hp`. Establish `hp' : p ∈ V` using `hp`. Use `show T p ∈ W`. Use `clear hp`. Proceed by induction on `hp' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)`. Consider the case `zero => rw [map_zero]`. Conclude with `W.zero_mem`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `W.add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `W.smul_mem _ hx`. Establish `hφ : φ ∈ S.topologicalClosure` using `by rw [hS]; trivial`.

Establish `h0 : T φ ∈ W` using `closure_minimal hsub hcl hφ`. Establish `hs` using `hasSum_sq_inner_of_mem_closure hv h0`. Simplify using `only [hT] at hs`. Establish `hn : ‖T φ‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 ∂m`. Establish `h2` using `hT φ φ`.

Rewrite `h2` using `[inner_self_eq_norm_sq_to_K]`. Establish `h3 : ∫ x, (starRingEnd ℂ) (φ x) * φ x ∂m = ∫ x, ((‖φ x‖ ^ 2 : ℝ) : ℂ) ∂m` using `integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.conj_mul'])`. Rewrite `h2` using `[h3, integral_complex_ofReal]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← h2, Complex.ofReal_pow]`.

Both sides reduce to the same expression. Rewrite `hs` using `[hn]`. Then use the resulting hypothesis.
-/
theorem hasSum_sq_integral {X A : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [DecidableEq A] (m : Measure X) [IsFiniteMeasure m]
    (e : A → C(X, ℂ)) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b) (hstar : ∀ a, ∃ c, e c = star (e a))
    (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y)
    (horth : ∀ a b, ∫ x, (starRingEnd ℂ) (e a x) * e b x ∂m = if a = b then 1 else 0) (φ : C(X, ℂ)) :
    HasSum (fun a => ‖∫ x, (starRingEnd ℂ) (e a x) * φ x ∂m‖ ^ 2) (∫ x, ‖φ x‖ ^ 2 ∂m) := by
  let T : C(X, ℂ) →L[ℂ] Lp ℂ 2 m := ContinuousMap.toLp 2 m ℂ
  have hT : ∀ p q : C(X, ℂ), inner ℂ (T p) (T q) = ∫ x, (starRingEnd ℂ) (p x) * q x ∂m := by
    intro p q
    rw [ContinuousMap.inner_toLp]
    simp only [mul_comm]
  let V : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range e)
  have hV1 : (1 : C(X, ℂ)) ∈ V := Submodule.subset_span h1
  have hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V := by
    intro p hp q hq
    have : V * V ≤ V := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact hmul a b
    exact this (Submodule.mul_mem_mul hp hq)
  have hVstar : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span (hstar a)
    | zero => rw [star_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(X, ℂ) :=
    { toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq)
      star_mem' := fun {p} hp => hVstar p hp }
  have hS : S.topologicalClosure = ⊤ := by
    refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
    intro x y hxy
    obtain ⟨a, ha⟩ := hsep x y hxy
    exact ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ha⟩
  have hv : Orthonormal ℂ (fun a => T (e a)) := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [hT, horth]
  let W := (Submodule.span ℂ (Set.range fun a => T (e a))).topologicalClosure
  have hcl : IsClosed {p : C(X, ℂ) | T p ∈ W} :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hsub : (S : Set C(X, ℂ)) ⊆ {p : C(X, ℂ) | T p ∈ W} := by
    intro p hp
    have hp' : p ∈ V := hp
    show T p ∈ W
    clear hp
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem _ hx
  have hφ : φ ∈ S.topologicalClosure := by rw [hS]; trivial
  have h0 : T φ ∈ W := closure_minimal hsub hcl hφ
  have hs := hasSum_sq_inner_of_mem_closure hv h0
  simp only [hT] at hs
  have hn : ‖T φ‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 ∂m := by
    have h2 := hT φ φ
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : ∫ x, (starRingEnd ℂ) (φ x) * φ x ∂m = ∫ x, ((‖φ x‖ ^ 2 : ℝ) : ℂ) ∂m :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.conj_mul'])
    rw [h3, integral_complex_ofReal] at h2
    apply Complex.ofReal_injective
    rw [← h2, Complex.ofReal_pow]
    rfl
  rwa [hn] at hs

/- English proof (translation)
Use `letI : MeasurableSpace X := borel X`. Use `haveI : BorelSpace X := ⟨rfl⟩`. Establish `hm : AEMeasurable π ν` using `hπ.measurable.aemeasurable`. Establish `hi : ∀ p q : C(X, ℂ), ∫ x, (starRingEnd ℂ) (p x) * q x ∂(ν.map π) = ∫ x, (starRingEnd ℂ) (p (π x)) * q (π x) ∂ν` using `fun p q => integral_map hm ((Complex.continuous_conj.comp p.continuous).mul q.continuous).aestronglyMeasurable`. Establish `hs` using `hasSum_sq_integral (ν.map π) e h1 hmul hstar hsep (fun a b => by rw [hi, horth]) φ`.

Simplify using `only [hi] at hs`. Rewrite `hs` using `[integral_map (f := fun x => ‖φ x‖ ^ 2) hm (φ.continuous.norm.pow 2).aestronglyMeasurable]`. Establish `hint : Integrable (fun x => ‖φ (π x)‖ ^ 2) ν` using `Integrable.of_bound ((φ.continuous.comp hπ).norm.pow 2).aestronglyMeasurable (‖φ‖ ^ 2) (Filter.Eventually.of_forall fun x => by`. Rewrite using `[Real.norm_of_nonneg (sq_nonneg _)]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (φ.norm_coe_le_norm _) 2)`.

Establish `h2` using `ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable`. Rewrite `h2` using `[hs.tsum_eq, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]`. Simplify using `only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm] at h2`. Conclude with `h2.symm`.
-/
theorem tsum_enorm_sq_integral {X G A : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [DecidableEq A] (ν : Measure G) [IsFiniteMeasure ν] (π : G → X)
    (hπ : Continuous π)
    (e : A → C(X, ℂ)) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b) (hstar : ∀ a, ∃ c, e c = star (e a))
    (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y)
    (horth : ∀ a b, ∫ x, (starRingEnd ℂ) (e a (π x)) * e b (π x) ∂ν = if a = b then 1 else 0) (φ : C(X, ℂ)) :
    ∑' a, ‖∫ x, (starRingEnd ℂ) (e a (π x)) * φ (π x) ∂ν‖ₑ ^ 2 = ∫⁻ x, ‖φ (π x)‖ₑ ^ 2 ∂ν := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  have hm : AEMeasurable π ν := hπ.measurable.aemeasurable
  have hi : ∀ p q : C(X, ℂ), ∫ x, (starRingEnd ℂ) (p x) * q x ∂(ν.map π) =
      ∫ x, (starRingEnd ℂ) (p (π x)) * q (π x) ∂ν := fun p q =>
    integral_map hm ((Complex.continuous_conj.comp p.continuous).mul q.continuous).aestronglyMeasurable
  have hs := hasSum_sq_integral (ν.map π) e h1 hmul hstar hsep (fun a b => by rw [hi, horth]) φ
  simp only [hi] at hs
  rw [integral_map (f := fun x => ‖φ x‖ ^ 2) hm (φ.continuous.norm.pow 2).aestronglyMeasurable] at hs
  have hint : Integrable (fun x => ‖φ (π x)‖ ^ 2) ν :=
    Integrable.of_bound ((φ.continuous.comp hπ).norm.pow 2).aestronglyMeasurable (‖φ‖ ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (φ.norm_coe_le_norm _) 2)
  have h2 := ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable
  rw [hs.tsum_eq, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)] at h2
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm] at h2
  exact h2.symm

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {ψ : AddChar (Ad E) ℂ}

/- English proof (translation)
Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ.norm]`. Simplify using the standard rewrite rules.
-/
theorem conj_psi (hψ : StdPsi ψ) (y : Ad E) : (starRingEnd ℂ) (ψ y) = ψ (-y) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ.norm]
  simp

/- English proof (translation)
Take `⟨t, ht⟩` from `Function.ne_iff.1 hξ`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 E)`. Take `⟨y, hy⟩` from `hψ.loc ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩`. Generalize the expression as in `sFin E _ = z at hy`. Use `⟨Pi.single t (-(algebraMap E (Ad E) (ξ t)⁻¹ * z)), ?_⟩` and prove the remaining obligations.

Rewrite using `[dot, Finset.sum_eq_single t]`. Rewrite using `[Pi.single_eq_same, mul_neg, neg_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]`. Conclude with `hy`. Introduce `s _ hs`. Simplify using `[Pi.single_eq_of_ne hs]`.

Simplify using the standard rewrite rules.
-/
theorem exists_dot_ne_one (hψ : StdPsi ψ) {ξ : ι → E} (hξ : ξ ≠ 0) : ∃ y : ι → Ad E, ψ (-dot ξ y) ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hξ
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
  generalize sFin E _ = z at hy
  refine ⟨Pi.single t (-(algebraMap E (Ad E) (ξ t)⁻¹ * z)), ?_⟩
  rw [dot, Finset.sum_eq_single t]
  · rw [Pi.single_eq_same, mul_neg, neg_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
    exact hy
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

/- English proof (translation)
Take `⟨y, hy⟩` from `exists_dot_ne_one hψ hξ`. Establish `hP : Per (ratV E ι) (fun x => ψ (-dot ξ x) * 1)` using `hψ.per_twist (Φ := fun _ => 1) ⟨continuous_const, fun _ _ _ => rfl⟩ ξ`. Establish `h1` using `avg_add_right _ _ (isCoLat_ratV E ι) _ hP y`. Establish `h2 : (fun x => ψ (-dot ξ (x + y)) * 1) = fun x => ψ (-dot ξ y) * (ψ (-dot ξ x) * 1)`. Use function extensionality and compare the values at `x`.

Rewrite using `[dot_add_right, neg_add, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2, avg_const_mul]`. Establish `h3 : (ψ (-dot ξ y) - 1) * avg (ratV E ι) (fun x => ψ (-dot ξ x) * 1) = 0`. Rewrite using `[sub_mul, h1, one_mul, sub_self]`.

Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hy)`.
-/
theorem avg_char_eq_zero (hψ : StdPsi ψ) {ξ : ι → E} (hξ : ξ ≠ 0) :
    avg (ratV E ι) (fun x => ψ (-dot ξ x) * 1) = 0 := by
  obtain ⟨y, hy⟩ := exists_dot_ne_one hψ hξ
  have hP : Per (ratV E ι) (fun x => ψ (-dot ξ x) * 1) :=
    hψ.per_twist (Φ := fun _ => 1) ⟨continuous_const, fun _ _ _ => rfl⟩ ξ
  have h1 := avg_add_right _ _ (isCoLat_ratV E ι) _ hP y
  have h2 : (fun x => ψ (-dot ξ (x + y)) * 1) = fun x => ψ (-dot ξ y) * (ψ (-dot ξ x) * 1) := by
    funext x
    rw [dot_add_right, neg_add, AddChar.map_add_eq_mul]
    ring
  rw [h2, avg_const_mul] at h1
  have h3 : (ψ (-dot ξ y) - 1) * avg (ratV E ι) (fun x => ψ (-dot ξ x) * 1) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hy)

/- English proof (translation)
Simplify using `[dot]`.
-/
theorem dot_neg_left (ξ : ι → E) (x : ι → Ad E) : dot (-ξ) x = -dot ξ x := by
  simp [dot]

/- English proof (translation)
Introduce `E _ _ ι _ ψ hψ Φ hΦ _ _ ν D hν hD h1`. Establish `hL` using `isCoLat_ratV E ι`. Take `⟨-, K, hK, hcov⟩` from `id hL`. Use `set Γ := ratV E ι with hΓ`. Establish `hav : ∀ f, Per Γ f → avg Γ f = ∫ x in D, f x ∂ν` using `fun f hf => by`.

Rewrite using `[(setIntegral_eq_mass_mul_avg _ Γ hL ν D hν hD f hf).2.2.2, h1]`. Simplify using the standard rewrite rules. Establish `: IsFiniteMeasure (ν.restrict D)` using `⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`. Establish `hπ : Continuous (QuotientAddGroup.mk : (ι → Ad E) → (ι → Ad E) ⧸ Γ)` using `QuotientAddGroup.continuous_mk`. Establish `: CompactSpace ((ι → Ad E) ⧸ Γ)` using `⟨by`.

Use `(hK.image hπ).of_isClosed_subset isClosed_univ fun q _ => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨γ, hγ, hk⟩` from `hcov x`. Use `⟨γ + x, hk, QuotientAddGroup.eq.2 ?_⟩` and prove the remaining obligations. Simplify using `using hγ⟩`.

Establish `desc : ∀ f : (ι → Ad E) → ℂ, Per Γ f → ∃ p : C((ι → Ad E) ⧸ Γ, ℂ), ∀ x : ι → Ad E, p (x : (ι → Ad E) ⧸ Γ) = f x`. Introduce `f hf`. Establish `hw : ∀ x y : ι → Ad E, (QuotientAddGroup.leftRel Γ) x y → f x = f y`. Introduce `x y hxy`. Rewrite `hxy` using `[QuotientAddGroup.leftRel_apply]`.

Rewrite using `[← hf.2 _ hxy x]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Conclude with `⟨⟨Quotient.lift f hw, hf.1.quotient_lift hw⟩, fun x => rfl⟩`. Establish `hP : ∀ ξ : ι → E, Per Γ (fun x => ψ (-dot ξ x) * 1)` using `fun ξ => hψ.per_twist (Φ := fun _ => 1) ⟨continuous_const, fun _ _ _ => rfl⟩ ξ`.

Use `choose e he using fun a : ι → E => desc _ (hP (-a))`. Simplify using `only [dot_neg_left, neg_neg, mul_one] at he`. Take `⟨φ, hφ⟩` from `desc Φ hΦ`. Establish `ext : ∀ p q : C((ι → Ad E) ⧸ Γ, ℂ), (∀ x : ι → Ad E, p (x : (ι → Ad E) ⧸ Γ) = q (x : (ι → Ad E) ⧸ Γ)) → p = q`. Introduce `p q h`.

Use extensionality with `z`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective z`. Conclude with `h x`. Establish `key` using `tsum_enorm_sq_integral (ν.restrict D) _ hπ e ⟨0, ext _ _ fun x => by simp [he, dot_zero_left]⟩ (fun a b => ⟨a + b, ext _ _ fun x => by simp [he, dot_add_left, AddChar.map_add_eq_mul]⟩) (fun a => ⟨-a, ext _ _ fun x => by simp [he, dot_neg_left, conj_psi hψ]⟩) (fun z w hzw => by`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective z`.

Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective w`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `hzw (QuotientAddGroup.eq.2 ((hψ.forall_dot_eq_one_iff _).1 fun a => ?_))` and prove the remaining obligations. Establish `h1` using `hcon a`.

Rewrite `h1` using `[he, he]`. Establish `hne : ψ (dot a y) ≠ 0` using `fun h => by simpa [h] using hψ.norm (dot a y)`. Use `mul_left_cancel₀ hne ?_` and prove the remaining obligations. Rewrite using `[mul_one, ← AddChar.map_add_eq_mul, ← h1]`. Use `congr 1`.

Rewrite using `[add_neg_eq_iff_eq_add, ← dot_add_right, add_neg_cancel_left])`. Use the proof step `(fun a b => by`. Simplify using `only [he, conj_psi hψ]`. Establish `h2 : ∀ x, ψ (-dot a x) * ψ (dot b x) = ψ (-dot (a - b) x) * 1` using `fun x => by`. Rewrite using `[mul_one, ← AddChar.map_add_eq_mul, sub_eq_add_neg, dot_add_left, dot_neg_left, neg_add, neg_neg]`.

Simplify using `only [h2]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Simplify using `[dot_zero_left, Measure.real, h1]`. Rewrite using `[← hav _ (hP (a - b))]`.

Conclude with `avg_char_eq_zero hψ (sub_ne_zero.2 hab))`. Use `φ`. Simplify using `only [he, hφ, conj_psi hψ] at key`. Rewrite using `[← key]`. Conclude with `tsum_congr fun ξ => by rw [hav _ (hψ.per_twist hΦ ξ)]`.
-/
theorem tsum_enorm_avg_sq : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → ∀ [MeasurableSpace (ι → Ad E)] [BorelSpace (ι → Ad E)] (ν : Measure (ι → Ad E)) (D : Set (ι → Ad E)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratV E ι) D ν → ν D = 1 → ∑' ξ : ι → E, ‖avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x)‖ₑ ^ 2 = ∫⁻ x in D, ‖Φ x‖ₑ ^ 2 ∂ν := by
  classical
  intro E _ _ ι _ ψ hψ Φ hΦ _ _ ν D hν hD h1
  have hL := isCoLat_ratV E ι
  obtain ⟨-, K, hK, hcov⟩ := id hL
  set Γ := ratV E ι with hΓ
  have hav : ∀ f, Per Γ f → avg Γ f = ∫ x in D, f x ∂ν := fun f hf => by
    rw [(setIntegral_eq_mass_mul_avg _ Γ hL ν D hν hD f hf).2.2.2, h1]
    simp
  have : IsFiniteMeasure (ν.restrict D) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hπ : Continuous (QuotientAddGroup.mk : (ι → Ad E) → (ι → Ad E) ⧸ Γ) := QuotientAddGroup.continuous_mk
  have : CompactSpace ((ι → Ad E) ⧸ Γ) := ⟨by
    refine (hK.image hπ).of_isClosed_subset isClosed_univ fun q _ => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨γ, hγ, hk⟩ := hcov x
    refine ⟨γ + x, hk, QuotientAddGroup.eq.2 ?_⟩
    simpa using hγ⟩
  have desc : ∀ f : (ι → Ad E) → ℂ, Per Γ f →
      ∃ p : C((ι → Ad E) ⧸ Γ, ℂ), ∀ x : ι → Ad E, p (x : (ι → Ad E) ⧸ Γ) = f x := by
    intro f hf
    have hw : ∀ x y : ι → Ad E, (QuotientAddGroup.leftRel Γ) x y → f x = f y := by
      intro x y hxy
      rw [QuotientAddGroup.leftRel_apply] at hxy
      rw [← hf.2 _ hxy x]
      congr 1
      abel
    exact ⟨⟨Quotient.lift f hw, hf.1.quotient_lift hw⟩, fun x => rfl⟩
  have hP : ∀ ξ : ι → E, Per Γ (fun x => ψ (-dot ξ x) * 1) := fun ξ =>
    hψ.per_twist (Φ := fun _ => 1) ⟨continuous_const, fun _ _ _ => rfl⟩ ξ
  choose e he using fun a : ι → E => desc _ (hP (-a))
  simp only [dot_neg_left, neg_neg, mul_one] at he
  obtain ⟨φ, hφ⟩ := desc Φ hΦ
  have ext : ∀ p q : C((ι → Ad E) ⧸ Γ, ℂ),
      (∀ x : ι → Ad E, p (x : (ι → Ad E) ⧸ Γ) = q (x : (ι → Ad E) ⧸ Γ)) → p = q := by
    intro p q h
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact h x
  have key := tsum_enorm_sq_integral (ν.restrict D) _ hπ e
    ⟨0, ext _ _ fun x => by simp [he, dot_zero_left]⟩
    (fun a b => ⟨a + b, ext _ _ fun x => by simp [he, dot_add_left, AddChar.map_add_eq_mul]⟩)
    (fun a => ⟨-a, ext _ _ fun x => by simp [he, dot_neg_left, conj_psi hψ]⟩)
    (fun z w hzw => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
      by_contra hcon
      push Not at hcon
      refine hzw (QuotientAddGroup.eq.2 ((hψ.forall_dot_eq_one_iff _).1 fun a => ?_))
      have h1 := hcon a
      rw [he, he] at h1
      have hne : ψ (dot a y) ≠ 0 := fun h => by simpa [h] using hψ.norm (dot a y)
      refine mul_left_cancel₀ hne ?_
      rw [mul_one, ← AddChar.map_add_eq_mul, ← h1]
      congr 1
      rw [add_neg_eq_iff_eq_add, ← dot_add_right, add_neg_cancel_left])
    (fun a b => by
      simp only [he, conj_psi hψ]
      have h2 : ∀ x, ψ (-dot a x) * ψ (dot b x) = ψ (-dot (a - b) x) * 1 := fun x => by
        rw [mul_one, ← AddChar.map_add_eq_mul, sub_eq_add_neg, dot_add_left, dot_neg_left, neg_add, neg_neg]
      simp only [h2]
      split_ifs with hab
      · subst hab
        simp [dot_zero_left, Measure.real, h1]
      · rw [← hav _ (hP (a - b))]
        exact avg_char_eq_zero hψ (sub_ne_zero.2 hab))
    φ
  simp only [he, hφ, conj_psi hψ] at key
  rw [← key]
  exact tsum_congr fun ξ => by rw [hav _ (hψ.per_twist hΦ ξ)]

end GlobalTheory.AdelicParseval
