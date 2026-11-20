import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.SeparatingCharacters

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ K hK hKcov A _ χ hχc hχmul hχadd hχ0 hχnorm hχker hχinj μ 𝓕 hμ h𝓕 h𝓕1 Φ hΦc hΦper hsum`. Use `haveI := hμ`. Use `haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance`. Establish `hχz : ∀ a, χ a 0 = 1`. Introduce `a`.

Establish `hne : χ a 0 ≠ 0`. Introduce `h`. Use `hχnorm a 0` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`.

Establish `h2 : χ a 0 * χ a 0 = χ a 0 * 1` using `by rw [← hχmul, add_zero, mul_one]`. Conclude with `(mul_left_cancel₀ hne h2)`. Establish `hχne : ∀ a x, χ a x ≠ 0`. Introduce `a x h`. Use `hχnorm a x` as an intermediate fact.

Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`. Establish `hstar : ∀ a x, star (χ a x) = χ (-a) x`. Introduce `a x`. Establish `h1 : star (χ a x) * χ a x = 1`.

Use `Complex.conj_mul' (χ a x)` as an intermediate fact. Rewrite `this` using `[hχnorm]`. Simplify using `using this`. Establish `h2 : χ (-a) x * χ a x = 1` using `by rw [← hχadd, neg_add_cancel, hχ0]`. Conclude with `mul_right_cancel₀ (hχne a x) (h1.trans h2.symm)`.

Establish `hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x`. Introduce `a γ hγ x`. Rewrite using `[hχmul, (hχker γ).mpr hγ a, one_mul]`. Establish `lift : ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) → ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = f x`. Introduce `f hf hper`.

Establish `hwd : ∀ x y : G, (QuotientAddGroup.mk x : G ⧸ Γ) = QuotientAddGroup.mk y → f x = f y`. Introduce `x y hxy`. Establish `h1` using `hper _ (QuotientAddGroup.eq.mp hxy) x`. Establish `e : -x + y + x = y` using `by abel`. Rewrite `h1` using `[e]`.

Conclude with `h1.symm`. Use `⟨⟨fun q => Quotient.liftOn' q f (fun x y h => hwd x y (Quotient.sound' h)), ?_⟩, fun x => rfl⟩` and prove the remaining obligations. Conclude with `(QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr hf`. Use `haveI : CompactSpace (G ⧸ Γ) := by`. Use `⟨?_⟩` and prove the remaining obligations.

Establish `himg : (QuotientAddGroup.mk '' K : Set (G ⧸ Γ)) = Set.univ`. Use `Set.eq_univ_of_forall fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨γ, hγ, hk⟩` from `hKcov x`. Use `⟨γ + x, hk, QuotientAddGroup.eq.mpr ?_⟩` and prove the remaining obligations.

Rewrite using `[show -(γ + x) + x = -γ by abel]`. Conclude with `neg_mem hγ`. Rewrite using `[← himg]`. Conclude with `hK.image QuotientAddGroup.continuous_mk`. Establish `hc : ∀ a, ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = χ a x` using `fun a => lift _ (hχc a) (hχper a)`.

Use `choose e he using hc`. Take `⟨P, hP⟩` from `lift Φ hΦc hΦper`. Establish `h𝓕lt : μ 𝓕 < ⊤` using `by rw [h𝓕1]; exact ENNReal.one_lt_top`. Establish `hint : ∀ w : C(G ⧸ Γ, ℂ), IntegrableOn (fun x => w (QuotientAddGroup.mk x)) 𝓕 μ`. Introduce `w`.

Conclude with `Measure.integrableOn_of_bounded h𝓕lt.ne (w.continuous.comp QuotientAddGroup.continuous_mk).aestronglyMeasurable (M := ‖w‖) (Filter.Eventually.of_forall fun x => w.norm_coe_le_norm _)`. Choose the witnesses or unpack the hypotheses as in `⟨I, hI⟩ : ∃ I : C(G ⧸ Γ, ℂ) →L[ℂ] ℂ, ∀ w, I w = ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ := by`. Use `⟨LinearMap.mkContinuous { toFun := fun w => ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ map_add' := fun v w => by` and prove the remaining obligations. Simplify using `only [ContinuousMap.add_apply]`. Conclude with `integral_add (hint v) (hint w)`.

Use the proof step `map_smul' := fun c w => by`. Simplify using `only [ContinuousMap.smul_apply, RingHom.id_apply]`. Conclude with `integral_smul c _ } 1 (fun w => ?_), fun w => rfl⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hprod : ∀ a a', e a * e a' = e (a + a')`.

Introduce `a a'`. Use extensionality with `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Simplify using `[he, hχadd]`. Establish `hstarE : ∀ a, star (e a) = e (-a)`.

Introduce `a`. Use extensionality with `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Simplify using `only [ContinuousMap.star_apply, he]`. Conclude with `hstar a x`.

Establish `hone : e 0 = 1`. Use extensionality with `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Simplify using `[he, hχ0]`. Establish `hnorm1 : ∀ a, ‖e a‖ ≤ 1`.

Introduce `a`. Use `(ContinuousMap.norm_le _ zero_le_one).mpr fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Rewrite using `[he, hχnorm]`. Establish `hortho : ∀ a, I (e a) = if a = 0 then 1 else 0`.

Introduce `a`. Rewrite using `[hI]`. Repeatedly rewrite using `[he]`. Use `split_ifs with ha`. Substitute `ha` using the available equality.

Simplify using `[hχ0, Measure.real, h𝓕1]`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, χ a y ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `ha (hχinj a hcon)`.

Establish `htr : IsAddFundamentalDomain Γ (y +ᵥ 𝓕) μ` using `h𝓕.vadd_of_comm y`. Establish `key : (∫ x in 𝓕, χ a x ∂μ) = χ a y * ∫ x in 𝓕, χ a x ∂μ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Set.image_vadd]`. Conclude with `(measurePreserving_add_left μ y).setIntegral_image_emb (measurableEmbedding_addLeft y) _ _`.

Use `_ = ∫ x in 𝓕, χ a y * χ a x ∂μ := by simp_rw [hχmul]`. Use `_ = χ a y * ∫ x in 𝓕, χ a x ∂μ := integral_const_mul _ _`. Establish `h1 : (1 - χ a y) * ∫ x in 𝓕, χ a x ∂μ = 0`. Rewrite using `[sub_mul, one_mul]`. Conclude with `sub_eq_zero.mpr key`.

Break down `mul_eq_zero.mp h1 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hy`. Conclude with `h`. Use `set c : A → ℂ := fun b => ∫ x in 𝓕, χ b x * Φ x ∂μ with hcdef`. Establish `hcoef : ∀ b, c b = I (e b * P)`.

Introduce `b`. Rewrite using `[hI]`. Simplify using `[hcdef, he, hP]`. Establish `hsumn : Summable (fun a => ‖c a‖)` using `summable_norm_iff.mpr hsum`. Establish `hgs : Summable (fun a => c a • e (-a))`.

Use `Summable.of_norm_bounded hsumn fun a => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `set g : C(G ⧸ Γ, ℂ) := ∑' a, c a • e (-a) with hgdef`. Establish `hgcoef : ∀ b, I (e b * g) = c b`. Introduce `b`.

Establish `step : I (e b * g) = ∑' a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a))` using `(I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))).map_tsum hgs`. Rewrite using `[step]`. Establish `hterm : ∀ a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a)) = if a = b then c b else 0`. Introduce `a`. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_smul_comm, map_smul, hprod, hortho, smul_eq_mul]`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : b + -a ≠ 0` using `fun h' => h (add_neg_eq_zero.mp h').symm`. Simplify using `[h, h']`.

Rewrite using `[tsum_congr hterm, tsum_ite_eq]`. Use `set H : C(G ⧸ Γ, ℂ) := P - g with hHdef`. Establish `hH : ∀ b, I (e b * H) = 0`. Introduce `b`. Rewrite using `[hHdef, mul_sub, map_sub, ← hcoef, hgcoef, sub_self]`.

Set `V : Submodule ℂ C(G ⧸ Γ, ℂ)` to `Submodule.span ℂ (Set.range e)`. Establish `hVmul : ∀ u ∈ V, ∀ v ∈ V, u * v ∈ V`. Introduce `u hu v hv`. Establish `h1` using `Submodule.mul_mem_mul hu hv`. Rewrite `h1` using `[Submodule.span_mul_span]`.

Use `Submodule.span_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, rfl⟩, _, ⟨a', rfl⟩, rfl⟩`. Conclude with `⟨a + a', (hprod a a').symm⟩`. Establish `hVone : (1 : C(G ⧸ Γ, ℂ)) ∈ V`. Rewrite using `[← hone]`.

Conclude with `Submodule.subset_span ⟨0, rfl⟩`. Establish `hVstar : ∀ u ∈ V, star u ∈ V`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, rfl⟩` from `hx`. Rewrite using `[hstarE]`. Conclude with `Submodule.subset_span ⟨-a, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [star_add]`.

Conclude with `V.add_mem hx hy`. Consider the case `smul r x _ hx => rw [star_smul]`. Conclude with `V.smul_mem _ hx`. Set `S : StarSubalgebra ℂ C(G ⧸ Γ, ℂ)` to `{ carrier := (V : Set C(G ⧸ Γ, ℂ)) add_mem' := fun ha hb => V.add_mem ha hb zero_mem' := V.zero_mem mul_mem' := fun ha hb => hVmul _ ha _ hb one_mem' := hVone algebraMap_mem' := fun r => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`.

Conclude with `V.smul_mem r hVone`. Use the proof step `star_mem' := fun ha => hVstar _ ha }`. Establish `hsep : S.SeparatesPoints`. Introduce `q q' hne`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective q'`. Establish `hnot : -x + y ∉ Γ` using `fun h => hne (QuotientAddGroup.eq.mpr h)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, χ a (-x + y) ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hnot ((hχker _).mp hcon)`. Use `⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [he]`. Introduce `heq`. Apply `ha` to reduce the goal to its premises.

Rewrite using `[hχmul, ← heq, ← hχmul, neg_add_cancel, hχz]`. Establish `hcl` using `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep`. Establish `hZ : IsClosed {q : C(G ⧸ Γ, ℂ) | I (q * H) = 0}` using `isClosed_eq (I.continuous.comp (continuous_id.mul continuous_const)) continuous_const`. Establish `hSZ : (S : Set C(G ⧸ Γ, ℂ)) ⊆ {q : C(G ⧸ Γ, ℂ) | I (q * H) = 0}`. Introduce `u hu`.

Express the relevant statement in the definitionally equal form `u ∈ V at hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `hH a`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Set.mem_setOf_eq] at hx hy ⊢`. Rewrite using `[add_mul, map_add, hx, hy, add_zero]`. Consider the case `smul r x _ hx`.

Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Rewrite using `[smul_mul_assoc, map_smul, hx, smul_zero]`. Establish `hmem : star H ∈ closure (S : Set C(G ⧸ Γ, ℂ))`. Rewrite using `[← StarSubalgebra.topologicalClosure_coe, hcl]`. Simplify using the standard rewrite rules.

Establish `hHH : I (star H * H) = 0` using `closure_minimal hSZ hZ hmem`. Use `set k : G → ℂ := fun x => H (QuotientAddGroup.mk x) with hkdef`. Establish `hkc : Continuous k` using `H.continuous.comp QuotientAddGroup.continuous_mk`. Establish `hkper : ∀ γ : Γ, ∀ x, k (γ +ᵥ x) = k x`. Introduce `γ x`.

Use `show H (QuotientAddGroup.mk ((γ : G) + x)) = H (QuotientAddGroup.mk x)`. Use `congr 1`. Use `QuotientAddGroup.eq.mpr ?_` and prove the remaining obligations. Rewrite using `[show -((γ : G) + x) + x = -(γ : G) by abel]`. Conclude with `neg_mem γ.2`.

Establish `hpt : ∀ x, (star H * H) (QuotientAddGroup.mk x) = ((‖k x‖ ^ 2 : ℝ) : ℂ)`. Introduce `x`. Rewrite using `[ContinuousMap.mul_apply, ContinuousMap.star_apply, Complex.ofReal_pow]`. Conclude with `Complex.conj_mul' _`. Establish `hr : ∫ x in 𝓕, ‖k x‖ ^ 2 ∂μ = 0`.

Rewrite `hHH` using `[hI]`. Rewrite `hHH` using `[hpt]`. Rewrite `hHH` using `[integral_complex_ofReal]`. Conclude with `hHH` after adjusting the coercions. Establish `hkint : Integrable (fun x => ‖k x‖ ^ 2) (μ.restrict 𝓕)`.

Use `(hint (star H * H)).norm.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [hpt, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `abs_of_nonneg (by positivity)`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun x => by positivity) hkint).mp hr`. Use `set t : Set G := {x | k x ≠ 0} with htdef`.

Establish `ht : IsOpen t` using `isOpen_ne_fun hkc continuous_const`. Establish `h1 : μ.restrict 𝓕 t = 0`. Rewrite `hae` using `[Filter.EventuallyEq, ae_iff]`. Use `measure_mono_null ?_ hae` and prove the remaining obligations. Introduce `x hx`.

Conclude with `pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)`. Rewrite `h1` using `[Measure.restrict_apply ht.measurableSet]`. Establish `h2 : μ t = 0`. Use `h𝓕.measure_zero_of_invariant t (fun γ => ?_) h1` and prove the remaining obligations. Use extensionality with `x`.

Rewrite using `[Set.mem_vadd_set_iff_neg_vadd_mem]`. Simplify using `only [htdef, Set.mem_setOf_eq, hkper]`. Establish `h3 : t = ∅` using `(ht.measure_eq_zero_iff μ).mp h2`. Establish `hk0 : k 0 = 0`. Assume the negation of the conclusion as `hne`.

Establish `: (0 : G) ∈ t` using `hne`. Rewrite `this` using `[h3]`. Conclude with `this`. Establish `hg0 : g (QuotientAddGroup.mk 0) = ∑' a, c a`. Establish `hev` using `(ContinuousMap.evalCLM ℂ (QuotientAddGroup.mk 0 : G ⧸ Γ)).map_tsum hgs`.

Simplify using `only [ContinuousMap.evalCLM_apply] at hev`. Rewrite using `[hgdef, hev]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[ContinuousMap.smul_apply, he, hχz, smul_eq_mul, mul_one]`.

Establish `: k 0 = Φ 0 - ∑' a, c a`. Rewrite using `[hkdef]`. Simplify using `only [hHdef, ContinuousMap.sub_apply, hP]`. Rewrite using `[hg0]`. Rewrite `this` using `[hk0]`.

Conclude with `(sub_eq_zero.mp this.symm).symm`.
-/
theorem tsum_coefficients_eq_value_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ) → ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ = Φ 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hKcov A _ χ hχc hχmul hχadd hχ0 hχnorm hχker hχinj μ 𝓕 hμ h𝓕 h𝓕1 Φ hΦc hΦper hsum
  classical
  haveI := hμ
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance

  have hχz : ∀ a, χ a 0 = 1 := by
    intro a
    have hne : χ a 0 ≠ 0 := by
      intro h; have := hχnorm a 0; rw [h, norm_zero] at this; exact zero_ne_one this
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [← hχmul, add_zero, mul_one]
    exact (mul_left_cancel₀ hne h2)
  have hχne : ∀ a x, χ a x ≠ 0 := by
    intro a x h; have := hχnorm a x; rw [h, norm_zero] at this; exact zero_ne_one this
  have hstar : ∀ a x, star (χ a x) = χ (-a) x := by
    intro a x
    have h1 : star (χ a x) * χ a x = 1 := by
      have := Complex.conj_mul' (χ a x)
      rw [hχnorm] at this
      simpa using this
    have h2 : χ (-a) x * χ a x = 1 := by rw [← hχadd, neg_add_cancel, hχ0]
    exact mul_right_cancel₀ (hχne a x) (h1.trans h2.symm)
  have hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [hχmul, (hχker γ).mpr hγ a, one_mul]

  have lift : ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = f x := by
    intro f hf hper
    have hwd : ∀ x y : G, (QuotientAddGroup.mk x : G ⧸ Γ) = QuotientAddGroup.mk y → f x = f y := by
      intro x y hxy
      have h1 := hper _ (QuotientAddGroup.eq.mp hxy) x
      have e : -x + y + x = y := by abel
      rw [e] at h1
      exact h1.symm
    refine ⟨⟨fun q => Quotient.liftOn' q f (fun x y h => hwd x y (Quotient.sound' h)), ?_⟩, fun x => rfl⟩
    exact (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr hf

  haveI : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have himg : (QuotientAddGroup.mk '' K : Set (G ⧸ Γ)) = Set.univ := by
      refine Set.eq_univ_of_forall fun q => ?_
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨γ, hγ, hk⟩ := hKcov x
      refine ⟨γ + x, hk, QuotientAddGroup.eq.mpr ?_⟩
      rw [show -(γ + x) + x = -γ by abel]
      exact neg_mem hγ
    rw [← himg]
    exact hK.image QuotientAddGroup.continuous_mk
  have hc : ∀ a, ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = χ a x :=
    fun a => lift _ (hχc a) (hχper a)
  choose e he using hc
  obtain ⟨P, hP⟩ := lift Φ hΦc hΦper

  have h𝓕lt : μ 𝓕 < ⊤ := by rw [h𝓕1]; exact ENNReal.one_lt_top
  have hint : ∀ w : C(G ⧸ Γ, ℂ), IntegrableOn (fun x => w (QuotientAddGroup.mk x)) 𝓕 μ := by
    intro w
    exact Measure.integrableOn_of_bounded h𝓕lt.ne
      (w.continuous.comp QuotientAddGroup.continuous_mk).aestronglyMeasurable
      (M := ‖w‖) (Filter.Eventually.of_forall fun x => w.norm_coe_le_norm _)
  obtain ⟨I, hI⟩ : ∃ I : C(G ⧸ Γ, ℂ) →L[ℂ] ℂ,
      ∀ w, I w = ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ := by
    refine ⟨LinearMap.mkContinuous
      { toFun := fun w => ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ
        map_add' := fun v w => by
          simp only [ContinuousMap.add_apply]
          exact integral_add (hint v) (hint w)
        map_smul' := fun c w => by
          simp only [ContinuousMap.smul_apply, RingHom.id_apply]
          exact integral_smul c _ } 1 (fun w => ?_), fun w => rfl⟩
    calc ‖∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ‖ ≤ ‖w‖ * μ.real 𝓕 :=
          norm_setIntegral_le_of_norm_le_const h𝓕lt (fun x _ => w.norm_coe_le_norm _)
      _ = 1 * ‖w‖ := by simp [Measure.real, h𝓕1]

  have hprod : ∀ a a', e a * e a' = e (a + a') := by
    intro a a'; ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp [he, hχadd]
  have hstarE : ∀ a, star (e a) = e (-a) := by
    intro a; ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [ContinuousMap.star_apply, he]
    exact hstar a x
  have hone : e 0 = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp [he, hχ0]
  have hnorm1 : ∀ a, ‖e a‖ ≤ 1 := by
    intro a
    refine (ContinuousMap.norm_le _ zero_le_one).mpr fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [he, hχnorm]

  have hortho : ∀ a, I (e a) = if a = 0 then 1 else 0 := by
    intro a
    rw [hI]
    simp_rw [he]
    split_ifs with ha
    · subst ha
      simp [hχ0, Measure.real, h𝓕1]
    · obtain ⟨y, hy⟩ : ∃ y, χ a y ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact ha (hχinj a hcon)
      have htr : IsAddFundamentalDomain Γ (y +ᵥ 𝓕) μ := h𝓕.vadd_of_comm y
      have key : (∫ x in 𝓕, χ a x ∂μ) = χ a y * ∫ x in 𝓕, χ a x ∂μ := by
        calc (∫ x in 𝓕, χ a x ∂μ) = ∫ x in y +ᵥ 𝓕, χ a x ∂μ :=
              h𝓕.setIntegral_eq htr (fun γ x => hχper a γ γ.2 x)
          _ = ∫ x in 𝓕, χ a (y + x) ∂μ := by
              rw [← Set.image_vadd]
              exact (measurePreserving_add_left μ y).setIntegral_image_emb
                (measurableEmbedding_addLeft y) _ _
          _ = ∫ x in 𝓕, χ a y * χ a x ∂μ := by simp_rw [hχmul]
          _ = χ a y * ∫ x in 𝓕, χ a x ∂μ := integral_const_mul _ _
      have h1 : (1 - χ a y) * ∫ x in 𝓕, χ a x ∂μ = 0 := by
        rw [sub_mul, one_mul]
        exact sub_eq_zero.mpr key
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hy
      · exact h

  set c : A → ℂ := fun b => ∫ x in 𝓕, χ b x * Φ x ∂μ with hcdef
  have hcoef : ∀ b, c b = I (e b * P) := by
    intro b
    rw [hI]
    simp [hcdef, he, hP]
  have hsumn : Summable (fun a => ‖c a‖) := summable_norm_iff.mpr hsum
  have hgs : Summable (fun a => c a • e (-a)) := by
    refine Summable.of_norm_bounded hsumn fun a => ?_
    calc ‖c a • e (-a)‖ ≤ ‖c a‖ * ‖e (-a)‖ := norm_smul_le _ _
      _ ≤ ‖c a‖ * 1 := by gcongr; exact hnorm1 _
      _ = ‖c a‖ := mul_one _
  set g : C(G ⧸ Γ, ℂ) := ∑' a, c a • e (-a) with hgdef
  have hgcoef : ∀ b, I (e b * g) = c b := by
    intro b
    have step : I (e b * g) = ∑' a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a)) :=
      (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))).map_tsum hgs
    rw [step]
    have hterm : ∀ a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a)) =
        if a = b then c b else 0 := by
      intro a
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_smul_comm, map_smul,
        hprod, hortho, smul_eq_mul]
      by_cases h : a = b
      · subst h; simp
      · have h' : b + -a ≠ 0 := fun h' => h (add_neg_eq_zero.mp h').symm
        simp [h, h']
    rw [tsum_congr hterm, tsum_ite_eq]
  set H : C(G ⧸ Γ, ℂ) := P - g with hHdef
  have hH : ∀ b, I (e b * H) = 0 := by
    intro b
    rw [hHdef, mul_sub, map_sub, ← hcoef, hgcoef, sub_self]

  let V : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hVmul : ∀ u ∈ V, ∀ v ∈ V, u * v ∈ V := by
    intro u hu v hv
    have h1 := Submodule.mul_mem_mul hu hv
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨a', rfl⟩, rfl⟩
    exact ⟨a + a', (hprod a a').symm⟩
  have hVone : (1 : C(G ⧸ Γ, ℂ)) ∈ V := by
    rw [← hone]; exact Submodule.subset_span ⟨0, rfl⟩
  have hVstar : ∀ u ∈ V, star u ∈ V := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [hstarE]
      exact Submodule.subset_span ⟨-a, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul r x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := (V : Set C(G ⧸ Γ, ℂ))
      add_mem' := fun ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      mul_mem' := fun ha hb => hVmul _ ha _ hb
      one_mem' := hVone
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem r hVone
      star_mem' := fun ha => hVstar _ ha }
  have hsep : S.SeparatesPoints := by
    intro q q' hne
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q'
    have hnot : -x + y ∉ Γ := fun h => hne (QuotientAddGroup.eq.mpr h)
    obtain ⟨a, ha⟩ : ∃ a, χ a (-x + y) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ((hχker _).mp hcon)
    refine ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
    simp only [he]
    intro heq
    apply ha
    rw [hχmul, ← heq, ← hχmul, neg_add_cancel, hχz]
  have hcl := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep

  have hZ : IsClosed {q : C(G ⧸ Γ, ℂ) | I (q * H) = 0} :=
    isClosed_eq (I.continuous.comp (continuous_id.mul continuous_const)) continuous_const
  have hSZ : (S : Set C(G ⧸ Γ, ℂ)) ⊆ {q : C(G ⧸ Γ, ℂ) | I (q * H) = 0} := by
    intro u hu
    change u ∈ V at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hH a
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [add_mul, map_add, hx, hy, add_zero]
    | smul r x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [smul_mul_assoc, map_smul, hx, smul_zero]
  have hmem : star H ∈ closure (S : Set C(G ⧸ Γ, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hcl]
    simp
  have hHH : I (star H * H) = 0 := closure_minimal hSZ hZ hmem

  set k : G → ℂ := fun x => H (QuotientAddGroup.mk x) with hkdef
  have hkc : Continuous k := H.continuous.comp QuotientAddGroup.continuous_mk
  have hkper : ∀ γ : Γ, ∀ x, k (γ +ᵥ x) = k x := by
    intro γ x
    show H (QuotientAddGroup.mk ((γ : G) + x)) = H (QuotientAddGroup.mk x)
    congr 1
    refine QuotientAddGroup.eq.mpr ?_
    rw [show -((γ : G) + x) + x = -(γ : G) by abel]
    exact neg_mem γ.2
  have hpt : ∀ x, (star H * H) (QuotientAddGroup.mk x) = ((‖k x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [ContinuousMap.mul_apply, ContinuousMap.star_apply, Complex.ofReal_pow]
    exact Complex.conj_mul' _
  have hr : ∫ x in 𝓕, ‖k x‖ ^ 2 ∂μ = 0 := by
    rw [hI] at hHH
    simp_rw [hpt] at hHH
    rw [integral_complex_ofReal] at hHH
    exact_mod_cast hHH
  have hkint : Integrable (fun x => ‖k x‖ ^ 2) (μ.restrict 𝓕) := by
    refine (hint (star H * H)).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpt, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hkint).mp hr
  set t : Set G := {x | k x ≠ 0} with htdef
  have ht : IsOpen t := isOpen_ne_fun hkc continuous_const
  have h1 : μ.restrict 𝓕 t = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro x hx
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  rw [Measure.restrict_apply ht.measurableSet] at h1
  have h2 : μ t = 0 := by
    refine h𝓕.measure_zero_of_invariant t (fun γ => ?_) h1
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [htdef, Set.mem_setOf_eq, hkper]
  have h3 : t = ∅ := (ht.measure_eq_zero_iff μ).mp h2
  have hk0 : k 0 = 0 := by
    by_contra hne
    have : (0 : G) ∈ t := hne
    rw [h3] at this
    exact this
  have hg0 : g (QuotientAddGroup.mk 0) = ∑' a, c a := by
    have hev := (ContinuousMap.evalCLM ℂ (QuotientAddGroup.mk 0 : G ⧸ Γ)).map_tsum hgs
    simp only [ContinuousMap.evalCLM_apply] at hev
    rw [hgdef, hev]
    congr 1; funext a
    rw [ContinuousMap.smul_apply, he, hχz, smul_eq_mul, mul_one]
  have : k 0 = Φ 0 - ∑' a, c a := by
    rw [hkdef]
    simp only [hHdef, ContinuousMap.sub_apply, hP]
    rw [hg0]
  rw [hk0] at this
  exact (sub_eq_zero.mp this.symm).symm

end GlobalTheory.SeparatingCharacters
