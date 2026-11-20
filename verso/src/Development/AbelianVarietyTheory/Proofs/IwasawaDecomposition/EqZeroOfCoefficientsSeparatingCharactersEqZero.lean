import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

open MeasureTheory

namespace GlobalTheory.SeparatingCharacters

open MeasureTheory in
open scoped Pointwise in

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ K hK hKΓ A _ χ hχc hχx hχa hχ0 hχn hsep μ 𝓕 hμ h𝓕 Φ hΦc hΦp hcoef`. Use `haveI : Countable Γ := Set.countable_univ_iff.mp isLindelof_univ.countable_of_discrete`. Establish `hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x`. Introduce `a γ hγ x`. Rewrite using `[add_comm, hχx, (hsep γ).2 hγ a, mul_one]`.

Establish `hinv : ∀ {f : G → ℂ}, (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) → ∀ x y : G, (QuotientAddGroup.leftRel Γ) x y → f x = f y`. Introduce `f hf x y hxy`. Establish `h` using `QuotientAddGroup.leftRel_apply.mp hxy`. Rewrite using `[← hf _ h x]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Use `haveI : CompactSpace (G ⧸ Γ) := by`. Use `⟨?_⟩` and prove the remaining obligations. Establish `: (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K`. Use `(Set.eq_univ_of_forall fun q => ?_).symm` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨γ, hγ, hx⟩` from `hKΓ x`. Use `⟨γ + x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientAddGroup.eq]`. Simplify using `using Γ.neg_mem hγ`.

Rewrite using `[this]`. Conclude with `hK.image QuotientAddGroup.continuous_mk`. Choose the witnesses or unpack the hypotheses as in `⟨C, hC⟩ : ∃ C, ∀ x, ‖Φ x‖ ≤ C := by`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hΦc.continuousOn`. Use `⟨C, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, hx⟩` from `hKΓ x`. Rewrite using `[← hΦp γ hγ x]`. Conclude with `hC _ hx`. Establish `h𝓕fin : μ 𝓕 < ⊤` using `_root_.GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hKΓ μ h𝓕`. Set `ψ : A → C(G ⧸ Γ, ℂ)` to `fun a => ⟨Quotient.lift (s := QuotientAddGroup.leftRel Γ) (χ a) (hinv (hχper a)), (hχc a).quotient_lift _⟩`.

Establish `hψ : ∀ a (x : G), ψ a (x : G ⧸ Γ) = χ a x` using `fun _ _ => rfl`. Establish `hψmul : ∀ a b, ψ a * ψ b = ψ (a + b)`. Introduce `a b`. Use extensionality with `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Rewrite using `[ContinuousMap.mul_apply, hψ, hψ, hψ, hχa]`. Establish `hψ0 : ψ 0 = 1`. Use extensionality with `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Rewrite using `[hψ, hχ0, ContinuousMap.one_apply]`.

Establish `hψstar : ∀ a, star (ψ a) = ψ (-a)`. Introduce `a`. Use extensionality with `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Rewrite using `[ContinuousMap.star_apply, hψ, hψ]`.

Establish `hz : χ a x ≠ 0`. Introduce `h`. Use `hχn a x` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`.

Establish `h1 : χ (-a) x * χ a x = 1` using `by rw [← hχa, neg_add_cancel, hχ0]`. Establish `h2 : (starRingEnd ℂ) (χ a x) * χ a x = 1`. Rewrite using `[Complex.conj_mul', hχn]`. Evaluate the numerical expressions. Conclude with `mul_right_cancel₀ hz (h2.trans h1.symm)`.

Set `S : Submodule ℂ C(G ⧸ Γ, ℂ)` to `Submodule.span ℂ (Set.range ψ)`. Establish `hSψ : ∀ a, ψ a ∈ S` using `fun a => Submodule.subset_span ⟨a, rfl⟩`. Establish `hSmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S`. Introduce `f g hf hg`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem f hf`. Take `⟨a, rfl⟩` from `hf`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨b, rfl⟩` from `hg`.

Rewrite using `[hψmul]`. Conclude with `hSψ _`. Consider the case `zero => rw [mul_zero]`. Conclude with `S.zero_mem`. Consider the case `add x y _ _ hx hy => rw [mul_add]`.

Conclude with `S.add_mem hx hy`. Consider the case `smul c x _ hx => rw [mul_smul_comm]`. Conclude with `S.smul_mem c hx`. Consider the case `zero => rw [zero_mul]`. Conclude with `S.zero_mem`.

Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `S.add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_mul_assoc]`. Conclude with `S.smul_mem c hx`. Establish `hSstar : ∀ f, f ∈ S → star f ∈ S`.

Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨a, rfl⟩` from `hf`. Rewrite using `[hψstar]`.

Conclude with `hSψ _`. Consider the case `zero => rw [star_zero]`. Conclude with `S.zero_mem`. Consider the case `add x y _ _ hx hy => rw [star_add]`. Conclude with `S.add_mem hx hy`.

Consider the case `smul c x _ hx => rw [star_smul]`. Conclude with `S.smul_mem _ hx`. Establish `hSalg : ∀ c : ℂ, algebraMap ℂ C(G ⧸ Γ, ℂ) c ∈ S`. Introduce `c`. Rewrite using `[Algebra.algebraMap_eq_smul_one, ← hψ0]`.

Conclude with `S.smul_mem c (hSψ 0)`. Set `T : StarSubalgebra ℂ C(G ⧸ Γ, ℂ)` to `{ carrier := S mul_mem' := fun {f g} hf hg => hSmul f g hf hg one_mem' := hψ0 ▸ hSψ 0 add_mem' := fun {f g} hf hg => S.add_mem hf hg zero_mem' := S.zero_mem algebraMap_mem' := hSalg star_mem' := fun {f} hf => hSstar f hf }`. Establish `hTsep : T.SeparatesPoints`. Introduce `q r hqr`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective r`. Establish `hnot : -x + y ∉ Γ` using `fun h => hqr (QuotientAddGroup.eq.mpr h)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, χ a (-x + y) ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hnot ((hsep _).1 h)`. Use `⟨ψ a, ⟨ψ a, hSψ a, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hψ]`. Introduce `hxy`. Establish `hz : χ a x ≠ 0`.

Introduce `h`. Use `hχn a x` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`. Apply `ha` to reduce the goal to its premises.

Establish `: χ a y = χ a x * χ a (-x + y)` using `by rw [← hχx, add_neg_cancel_left]`. Rewrite `this` using `[← hxy]`. Conclude with `(mul_right_eq_self₀.mp this.symm).resolve_right hz`. Establish `hclos` using `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints T hTsep`. Establish `hint : ∀ f : C(G ⧸ Γ, ℂ), IntegrableOn (fun x => f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x) 𝓕 μ`.

Introduce `f`. Use `Measure.integrableOn_of_bounded (M := ‖f‖ * C) h𝓕fin.ne (((map_continuous f).comp QuotientAddGroup.continuous_mk).mul hΦc).aestronglyMeasurable (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (f.norm_coe_le_norm _) (hC x) (norm_nonneg _) (norm_nonneg f)`. Set `L₀ : C(G ⧸ Γ, ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun f => ∫ x in 𝓕, f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ map_add' := fun f g => by`.

Simplify using `only [ContinuousMap.add_apply, add_mul]`. Conclude with `integral_add (hint f) (hint g)`. Use the proof step `map_smul' := fun c f => by`. Simplify using `only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]`. Conclude with `integral_const_mul c _ }`.

Set `L : C(G ⧸ Γ, ℂ) →L[ℂ] ℂ` to `L₀.mkContinuous (C * μ.real 𝓕) fun f => by`. Establish `h` using `norm_setIntegral_le_of_norm_le_const (f := fun x => f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x) h𝓕fin (C := ‖f‖ * C) fun x _ => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (f.norm_coe_le_norm _) (hC x) (norm_nonneg _) (norm_nonneg f)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hL : ∀ f, L f = ∫ x in 𝓕, f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ` using `fun _ => rfl`. Establish `hTL : ((T.topologicalClosure : StarSubalgebra ℂ C(G ⧸ Γ, ℂ)) : Set C(G ⧸ Γ, ℂ)) ⊆ {f | L f = 0}`. Rewrite using `[StarSubalgebra.topologicalClosure_coe]`. Use `closure_minimal ?_ (isClosed_eq L.continuous continuous_const)` and prove the remaining obligations. Introduce `f hf`.

Express the relevant statement in the definitionally equal form `f ∈ S at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨a, rfl⟩` from `hf`. Conclude with `hcoef a`.

Consider the case `zero => exact map_zero L`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Set.mem_setOf_eq] at hx hy ⊢`. Rewrite using `[map_add, hx, hy, add_zero]`. Consider the case `smul c x _ hx`.

Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Rewrite using `[map_smul, hx, smul_zero]`. Set `Φq : C(G ⧸ Γ, ℂ)` to `⟨Quotient.lift (s := QuotientAddGroup.leftRel Γ) Φ (hinv hΦp), hΦc.quotient_lift _⟩`. Establish `hzero : L (star Φq) = 0`. Apply `hTL` to reduce the goal to its premises.

Rewrite using `[hclos]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hzero` using `[hL]`. Establish `hsq : ∫ x in 𝓕, ‖Φ x‖ ^ 2 ∂μ = 0`. Establish `: ∫ x in 𝓕, (star Φq) (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ = ((∫ x in 𝓕, ‖Φ x‖ ^ 2 ∂μ : ℝ) : ℂ)`.

Rewrite using `[← integral_complex_ofReal]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [ContinuousMap.star_apply]`. Express the relevant statement in the definitionally equal form `(starRingEnd ℂ) (Φ x) * Φ x = _`. Rewrite using `[Complex.conj_mul']`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite `hzero` using `[this]`. Conclude with `hzero` after adjusting the coercions. Establish `hsqint : IntegrableOn (fun x => ‖Φ x‖ ^ 2) 𝓕 μ`.

Use `Measure.integrableOn_of_bounded (M := C ^ 2) h𝓕fin.ne (hΦc.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hC x) 2`. Establish `hae : ∀ᵐ x ∂μ.restrict 𝓕, Φ x = 0`. Use `(integral_eq_zero_iff_of_nonneg (fun x => by positivity) hsqint).mp hsq` as an intermediate fact.

Use `filter_upwards [this] with x hx`. Simplify using `using hx`. Use `set U : Set G := {x | Φ x ≠ 0} with hU`. Establish `hUo : IsOpen U` using `isOpen_ne_fun hΦc continuous_const`. Establish `hUF : μ (U ∩ 𝓕) = 0`.

Rewrite `hae` using `[ae_iff, Measure.restrict_apply hUo.measurableSet]`. Conclude with `hae`. Establish `hUinv : ∀ γ : Γ, γ +ᵥ U = U`. Introduce `γ`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `Φ ((γ : G) + y) ≠ 0`. Rewrite using `[hΦp _ γ.2]`. Conclude with `hy`.

Introduce `hx`. Use `⟨-(γ : G) + x, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Φ (-(γ : G) + x) ≠ 0`. Rewrite using `[← hΦp _ γ.2, add_neg_cancel_left]`. Conclude with `hx`.

Express the relevant statement in the definitionally equal form `(γ : G) + (-(γ : G) + x) = x`. Conclude with `add_neg_cancel_left _ _`. Establish `hU0 : μ U = 0` using `h𝓕.measure_zero_of_invariant U hUinv hUF`. Establish `hUe : U = ∅` using `hUo.measure_eq_zero_iff μ |>.mp hU0`. Use function extensionality and compare the values at `x`.

Assume the negation of the conclusion as `hx`. Establish `: x ∈ U` using `hx`. Rewrite `this` using `[hUe]`. Conclude with `this`.
-/
theorem _root_.GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ a, ∫ x in 𝓕, χ a x * Φ x ∂μ = 0) → Φ = 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hKΓ A _ χ hχc hχx hχa hχ0 hχn hsep μ 𝓕 hμ h𝓕 Φ hΦc hΦp hcoef
  classical
  haveI : Countable Γ := Set.countable_univ_iff.mp isLindelof_univ.countable_of_discrete

  have hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [add_comm, hχx, (hsep γ).2 hγ a, mul_one]
  have hinv : ∀ {f : G → ℂ}, (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      ∀ x y : G, (QuotientAddGroup.leftRel Γ) x y → f x = f y := by
    intro f hf x y hxy
    have h := QuotientAddGroup.leftRel_apply.mp hxy
    rw [← hf _ h x]
    congr 1
    abel
  haveI : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have : (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K := by
      refine (Set.eq_univ_of_forall fun q => ?_).symm
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨γ, hγ, hx⟩ := hKΓ x
      refine ⟨γ + x, hx, ?_⟩
      rw [QuotientAddGroup.eq]
      simpa using Γ.neg_mem hγ
    rw [this]
    exact hK.image QuotientAddGroup.continuous_mk

  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖Φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦc.continuousOn
    refine ⟨C, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKΓ x
    rw [← hΦp γ hγ x]
    exact hC _ hx
  have h𝓕fin : μ 𝓕 < ⊤ := _root_.GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hKΓ μ h𝓕

  let ψ : A → C(G ⧸ Γ, ℂ) := fun a =>
    ⟨Quotient.lift (s := QuotientAddGroup.leftRel Γ) (χ a) (hinv (hχper a)),
      (hχc a).quotient_lift _⟩
  have hψ : ∀ a (x : G), ψ a (x : G ⧸ Γ) = χ a x := fun _ _ => rfl
  have hψmul : ∀ a b, ψ a * ψ b = ψ (a + b) := by
    intro a b
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [ContinuousMap.mul_apply, hψ, hψ, hψ, hχa]
  have hψ0 : ψ 0 = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [hψ, hχ0, ContinuousMap.one_apply]
  have hψstar : ∀ a, star (ψ a) = ψ (-a) := by
    intro a
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [ContinuousMap.star_apply, hψ, hψ]
    have hz : χ a x ≠ 0 := by
      intro h
      have := hχn a x
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have h1 : χ (-a) x * χ a x = 1 := by rw [← hχa, neg_add_cancel, hχ0]
    have h2 : (starRingEnd ℂ) (χ a x) * χ a x = 1 := by
      rw [Complex.conj_mul', hχn]
      norm_num
    exact mul_right_cancel₀ hz (h2.trans h1.symm)

  let S : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range ψ)
  have hSψ : ∀ a, ψ a ∈ S := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hSmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨b, rfl⟩ := hg
        rw [hψmul]
        exact hSψ _
      | zero => rw [mul_zero]; exact S.zero_mem
      | add x y _ _ hx hy => rw [mul_add]; exact S.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm]; exact S.smul_mem c hx
    | zero => rw [zero_mul]; exact S.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact S.smul_mem c hx
  have hSstar : ∀ f, f ∈ S → star f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      rw [hψstar]
      exact hSψ _
    | zero => rw [star_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  have hSalg : ∀ c : ℂ, algebraMap ℂ C(G ⧸ Γ, ℂ) c ∈ S := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← hψ0]
    exact S.smul_mem c (hSψ 0)
  let T : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := S
      mul_mem' := fun {f g} hf hg => hSmul f g hf hg
      one_mem' := hψ0 ▸ hSψ 0
      add_mem' := fun {f g} hf hg => S.add_mem hf hg
      zero_mem' := S.zero_mem
      algebraMap_mem' := hSalg
      star_mem' := fun {f} hf => hSstar f hf }
  have hTsep : T.SeparatesPoints := by
    intro q r hqr
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective r
    have hnot : -x + y ∉ Γ := fun h => hqr (QuotientAddGroup.eq.mpr h)
    obtain ⟨a, ha⟩ : ∃ a, χ a (-x + y) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hnot ((hsep _).1 h)
    refine ⟨ψ a, ⟨ψ a, hSψ a, rfl⟩, ?_⟩
    simp only [hψ]
    intro hxy
    have hz : χ a x ≠ 0 := by
      intro h
      have := hχn a x
      rw [h, norm_zero] at this
      exact zero_ne_one this
    apply ha
    have : χ a y = χ a x * χ a (-x + y) := by rw [← hχx, add_neg_cancel_left]
    rw [← hxy] at this
    exact (mul_right_eq_self₀.mp this.symm).resolve_right hz
  have hclos := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints T hTsep

  have hint : ∀ f : C(G ⧸ Γ, ℂ), IntegrableOn (fun x => f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x) 𝓕 μ := by
    intro f
    refine Measure.integrableOn_of_bounded (M := ‖f‖ * C) h𝓕fin.ne
      (((map_continuous f).comp QuotientAddGroup.continuous_mk).mul hΦc).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm _) (hC x) (norm_nonneg _) (norm_nonneg f)
  let L₀ : C(G ⧸ Γ, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x in 𝓕, f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  let L : C(G ⧸ Γ, ℂ) →L[ℂ] ℂ := L₀.mkContinuous (C * μ.real 𝓕) fun f => by
    have h := norm_setIntegral_le_of_norm_le_const (f := fun x => f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x) h𝓕fin
      (C := ‖f‖ * C) fun x _ => by
        rw [norm_mul]
        exact mul_le_mul (f.norm_coe_le_norm _) (hC x) (norm_nonneg _) (norm_nonneg f)
    calc ‖L₀ f‖ ≤ ‖f‖ * C * μ.real 𝓕 := h
      _ = C * μ.real 𝓕 * ‖f‖ := by ring
  have hL : ∀ f, L f = ∫ x in 𝓕, f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ := fun _ => rfl
  have hTL : ((T.topologicalClosure : StarSubalgebra ℂ C(G ⧸ Γ, ℂ)) : Set C(G ⧸ Γ, ℂ)) ⊆ {f | L f = 0} := by
    rw [StarSubalgebra.topologicalClosure_coe]
    refine closure_minimal ?_ (isClosed_eq L.continuous continuous_const)
    intro f hf
    change f ∈ S at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      exact hcoef a
    | zero => exact map_zero L
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add, hx, hy, add_zero]
    | smul c x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [map_smul, hx, smul_zero]

  let Φq : C(G ⧸ Γ, ℂ) :=
    ⟨Quotient.lift (s := QuotientAddGroup.leftRel Γ) Φ (hinv hΦp), hΦc.quotient_lift _⟩
  have hzero : L (star Φq) = 0 := by
    apply hTL
    rw [hclos]
    trivial
  rw [hL] at hzero
  have hsq : ∫ x in 𝓕, ‖Φ x‖ ^ 2 ∂μ = 0 := by
    have : ∫ x in 𝓕, (star Φq) (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ = ((∫ x in 𝓕, ‖Φ x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [ContinuousMap.star_apply]
      change (starRingEnd ℂ) (Φ x) * Φ x = _
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [this] at hzero
    exact_mod_cast hzero
  have hsqint : IntegrableOn (fun x => ‖Φ x‖ ^ 2) 𝓕 μ := by
    refine Measure.integrableOn_of_bounded (M := C ^ 2) h𝓕fin.ne
      (hΦc.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  have hae : ∀ᵐ x ∂μ.restrict 𝓕, Φ x = 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hsqint).mp hsq
    filter_upwards [this] with x hx
    simpa using hx

  set U : Set G := {x | Φ x ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hΦc continuous_const
  have hUF : μ (U ∩ 𝓕) = 0 := by
    rw [ae_iff, Measure.restrict_apply hUo.measurableSet] at hae
    exact hae
  have hUinv : ∀ γ : Γ, γ +ᵥ U = U := by
    intro γ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change Φ ((γ : G) + y) ≠ 0
      rw [hΦp _ γ.2]
      exact hy
    · intro hx
      refine ⟨-(γ : G) + x, ?_, ?_⟩
      · change Φ (-(γ : G) + x) ≠ 0
        rw [← hΦp _ γ.2, add_neg_cancel_left]
        exact hx
      · change (γ : G) + (-(γ : G) + x) = x
        exact add_neg_cancel_left _ _
  have hU0 : μ U = 0 := h𝓕.measure_zero_of_invariant U hUinv hUF
  have hUe : U = ∅ := hUo.measure_eq_zero_iff μ |>.mp hU0
  funext x
  by_contra hx
  have : x ∈ U := hx
  rw [hUe] at this
  exact this

end GlobalTheory.SeparatingCharacters
