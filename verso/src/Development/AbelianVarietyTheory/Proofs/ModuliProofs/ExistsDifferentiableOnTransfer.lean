import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolPeriods

section HolTo

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X : Scheme.{0}}

/- English proof (translation)
Introduce `U f`. Establish `hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}`. Use extensionality with `b`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, hy b h1 ▸ h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, (hy b h1).symm ▸ h2⟩`. Rewrite using `[hs]`. Conclude with `⟨(h U f).1, (h U f).2.congr fun b hb => by rw [hy b hb.1]⟩`.
-/
theorem isHolTo_congr {B : Set V} {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hy : ∀ b ∈ B, y' b = y b) :
    IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hy b h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hy b h1).symm ▸ h2⟩
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [hy b hb.1]⟩

/- English proof (translation)
Introduce `U f`. Establish `hs : {c ∈ C | ⊤ ≤ y (φ c) ⁻¹ᵁ U} = C ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}`. Use extensionality with `c`. Conclude with `⟨fun hc => ⟨hc.1, hm hc.1, hc.2⟩, fun hc => ⟨hc.1, hc.2.2⟩⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hs]`. Conclude with `hφ.continuousOn.isOpen_inter_preimage hC (h U f).1`. Conclude with `(h U f).2.comp (hφ.mono fun c hc => hc.1) fun c hc => ⟨hm hc.1, hc.2⟩`.
-/
theorem isHolTo_comp {B : Set V} {C : Set W} {y : V → (Sp ℂ ⟶ X)} {φ : W → V} (h : IsHolTo B y)
    (hC : IsOpen C) (hφ : DifferentiableOn ℂ φ C) (hm : Set.MapsTo φ C B) :
    IsHolTo C (fun c => y (φ c)) := by
  intro U f
  have hs : {c ∈ C | ⊤ ≤ y (φ c) ⁻¹ᵁ U} = C ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext c
    exact ⟨fun hc => ⟨hc.1, hm hc.1, hc.2⟩, fun hc => ⟨hc.1, hc.2.2⟩⟩
  refine ⟨?_, ?_⟩
  · rw [hs]; exact hφ.continuousOn.isOpen_inter_preimage hC (h U f).1
  · exact (h U f).2.comp (hφ.mono fun c hc => hc.1) fun c hc => ⟨hm hc.1, hc.2⟩

/- English proof (translation)
Introduce `U f`. Establish `key : ∀ b ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ nhds b ∧ DifferentiableAt ℂ (fun b => valAt' (y b) U f) b`. Introduce `b hb`. Take `⟨B', hb', hsub, hB'⟩` from `h b hb.1`. Establish `hn` using `(hB' U f).1.mem_nhds (⟨hb', hb.2⟩ : b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ U})`.

Conclude with `⟨Filter.mem_of_superset hn fun c hc => ⟨hsub hc.1, hc.2⟩, (hB' U f).2.differentiableAt hn⟩`. Conclude with `⟨isOpen_iff_mem_nhds.2 fun b hb => (key b hb).1, fun b hb => (key b hb).2.differentiableWithinAt⟩`.
-/
theorem isHolTo_of_local {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : ∀ b ∈ B, ∃ B' : Set V, b ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y) : IsHolTo B y := by
  intro U f
  have key : ∀ b ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ nhds b ∧
      DifferentiableAt ℂ (fun b => valAt' (y b) U f) b := by
    intro b hb
    obtain ⟨B', hb', hsub, hB'⟩ := h b hb.1
    have hn := (hB' U f).1.mem_nhds (⟨hb', hb.2⟩ : b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ U})
    exact ⟨Filter.mem_of_superset hn fun c hc => ⟨hsub hc.1, hc.2⟩, (hB' U f).2.differentiableAt hn⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun b hb => (key b hb).1,
    fun b hb => (key b hb).2.differentiableWithinAt⟩

end HolTo

/- English proof (translation)
Establish `han : AnalyticAt ℂ F a` using `GlobalTheory.SCV.analyticAt_of_differentiableOn hF (hU.mem_nhds ha)`. Establish `hc : ContDiffAt ℂ ⊤ F a` using `han.contDiffAt`. Set `f' : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)` to `(LinearEquiv.ofBijective (fderiv ℂ F a : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) hb).toContinuousLinearEquiv`. Establish `hd : HasFDerivAt F (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) a`. Establish `: (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F a` using `by ext1; rfl`.

Rewrite using `[this]`. Conclude with `han.differentiableAt.hasFDerivAt`. Establish `hinv` using `hc.to_localInverse hd (by simp)`. Establish `hs` using `hc.hasStrictFDerivAt' hd (by simp)`. Establish `h1 : ∀ᶠ w in nhds (F a), F (hc.localInverse hd (by simp) w) = w` using `hs.eventually_right_inverse`.

Establish `h2 : ∀ᶠ w in nhds (F a), hc.localInverse hd (by simp) w ∈ U`. Use `hinv.continuousAt` as an intermediate fact. Rewrite `this` using `[ContinuousAt, hc.localInverse_apply_image]`. Conclude with `this (hU.mem_nhds ha)`. Establish `h3 : ∀ᶠ w in nhds (F a), DifferentiableAt ℂ (hc.localInverse hd (by simp)) w` using `(hinv.analyticAt.eventually_analyticAt).mono fun w hw => hw.differentiableAt`.

Take `⟨W, hW, hWo, hWa⟩` from `eventually_nhds_iff.1 (h1.and (h2.and h3))`. Conclude with `⟨W, _, hWo, hWa, fun w hw => (hW w hw).2.2.differentiableWithinAt, fun w hw => ⟨(hW w hw).2.1, (hW w hw).1⟩⟩`.
-/
theorem exists_local_section {n : ℕ} {U : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {a : Fin n → ℂ} (ha : a ∈ U) (hb : Function.Bijective (fderiv ℂ F a)) :
    ∃ (W : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen W ∧ F a ∈ W ∧ DifferentiableOn ℂ G W ∧
      ∀ w ∈ W, G w ∈ U ∧ F (G w) = w := by
  have han : AnalyticAt ℂ F a := GlobalTheory.SCV.analyticAt_of_differentiableOn hF (hU.mem_nhds ha)
  have hc : ContDiffAt ℂ ⊤ F a := han.contDiffAt
  let f' : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ F a : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) hb).toContinuousLinearEquiv
  have hd : HasFDerivAt F (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) a := by
    have : (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F a := by ext1; rfl
    rw [this]; exact han.differentiableAt.hasFDerivAt
  have hinv := hc.to_localInverse hd (by simp)
  have hs := hc.hasStrictFDerivAt' hd (by simp)
  have h1 : ∀ᶠ w in nhds (F a), F (hc.localInverse hd (by simp) w) = w := hs.eventually_right_inverse
  have h2 : ∀ᶠ w in nhds (F a), hc.localInverse hd (by simp) w ∈ U := by
    have := hinv.continuousAt
    rw [ContinuousAt, hc.localInverse_apply_image] at this
    exact this (hU.mem_nhds ha)
  have h3 : ∀ᶠ w in nhds (F a), DifferentiableAt ℂ (hc.localInverse hd (by simp)) w :=
    (hinv.analyticAt.eventually_analyticAt).mono fun w hw => hw.differentiableAt
  obtain ⟨W, hW, hWo, hWa⟩ := eventually_nhds_iff.1 (h1.and (h2.and h3))
  exact ⟨W, _, hWo, hWa, fun w hw => (hW w hw).2.2.differentiableWithinAt,
    fun w hw => ⟨(hW w hw).2.1, (hW w hw).1⟩⟩

/- English proof (translation)
Establish `hc : ∀ i : Fin g, ∃ c : Λ →₀ ℝ, (c.sum fun a r => r • Q b₀ a) = Pi.single i 1` using `fun i => Finsupp.mem_span_range_iff_exists_finsupp.1 (by rw [hspan]; trivial)`. Use `choose c hc using hc`. Set `M : (V → (Λ →+ (Fin g → ℂ))) → V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ))` to `fun R b => ∑ i, (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).smulRight (∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • R b a)`. Establish `hM : ∀ R : V → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => R b x) B) → DifferentiableOn ℂ (M R) B`. Introduce `R hR`.

Use `DifferentiableOn.fun_sum fun i _ => ?_` and prove the remaining obligations. Use `((ContinuousLinearMap.smulRightL ℂ (Fin g → ℂ) (Fin g → ℂ) (ContinuousLinearMap.proj i)).differentiable.comp_differentiableOn ?_)` and prove the remaining obligations. Conclude with `DifferentiableOn.fun_sum fun a _ => (hR a).fun_const_smul _`. Establish `h0 : M Q b₀ = 1` using `by ext1 z`. Establish `: ∀ i, ∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • Q b₀ a = Pi.single i 1` using `fun i => by`.

Rewrite using `[← hc i]`. Simplify using `[Finsupp.sum]`. Simplify using `only [M, this, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.one_apply]`. Use extensionality with `j`. Simplify using `[Pi.single_apply]`.

Establish `hkM : ∀ b ∈ B, ∀ z, k b (M Q b z) = M Q' b z`. Introduce `b hb z`. Simplify using `[M, map_sum, hk b hb]`. Use `⟨B ∩ M Q ⁻¹' {x | IsUnit x}, (hM Q hQ).continuousOn.isOpen_inter_preimage hB Units.isOpen, ⟨hb₀, by simp [h0]⟩, Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Establish `hd : DifferentiableOn ℂ (fun b => M Q' b * Ring.inverse (M Q b)) (B ∩ M Q ⁻¹' {x | IsUnit x})`.

Use `((hM Q' hQ').mono Set.inter_subset_left).mul fun b hb => ?_` and prove the remaining obligations. Conclude with `(differentiableAt_inverse hb.2).comp_differentiableWithinAt b ((hM Q hQ).mono Set.inter_subset_left b hb)`. Establish `hd2 : DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => (M Q' bz.1 * Ring.inverse (M Q bz.1)) bz.2) ((B ∩ M Q ⁻¹' {x | IsUnit x}) ×ˢ Set.univ)` using `(hd.comp differentiableOn_fst fun bz hbz => hbz.1).clm_apply differentiableOn_snd`. Use `hd2.congr fun bz hbz => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.mul_apply, ← hkM _ hbz.1.1, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hbz.1.2, ContinuousLinearMap.one_apply]`.
-/
theorem exists_differentiableOn_transfer {V Λ : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup Λ]
    {g : ℕ} {B : Set V} (hB : IsOpen B) {Q Q' : V → (Λ →+ (Fin g → ℂ))}
    (hQ : ∀ x, DifferentiableOn ℂ (fun b => Q b x) B) (hQ' : ∀ x, DifferentiableOn ℂ (fun b => Q' b x) B)
    {b₀ : V} (hb₀ : b₀ ∈ B) (hspan : Submodule.span ℝ (Set.range (Q b₀)) = ⊤)
    (k : V → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hk : ∀ b ∈ B, ∀ x, Q' b x = k b (Q b x)) :
    ∃ B' : Set V, IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => k bz.1 bz.2) (B' ×ˢ Set.univ) := by
  classical
  have hc : ∀ i : Fin g, ∃ c : Λ →₀ ℝ, (c.sum fun a r => r • Q b₀ a) = Pi.single i 1 := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (by rw [hspan]; trivial)
  choose c hc using hc
  let M : (V → (Λ →+ (Fin g → ℂ))) → V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun R b =>
    ∑ i, (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).smulRight
      (∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • R b a)
  have hM : ∀ R : V → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => R b x) B) →
      DifferentiableOn ℂ (M R) B := by
    intro R hR
    refine DifferentiableOn.fun_sum fun i _ => ?_
    refine ((ContinuousLinearMap.smulRightL ℂ (Fin g → ℂ) (Fin g → ℂ)
      (ContinuousLinearMap.proj i)).differentiable.comp_differentiableOn ?_)
    exact DifferentiableOn.fun_sum fun a _ => (hR a).fun_const_smul _
  have h0 : M Q b₀ = 1 := by
    ext1 z
    have : ∀ i, ∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • Q b₀ a = Pi.single i 1 := fun i => by
      rw [← hc i]; simp [Finsupp.sum]
    simp only [M, this, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.one_apply]
    ext j; simp [Pi.single_apply]
  have hkM : ∀ b ∈ B, ∀ z, k b (M Q b z) = M Q' b z := by
    intro b hb z
    simp [M, map_sum, hk b hb]
  refine ⟨B ∩ M Q ⁻¹' {x | IsUnit x}, (hM Q hQ).continuousOn.isOpen_inter_preimage hB Units.isOpen,
    ⟨hb₀, by simp [h0]⟩, Set.inter_subset_left, ?_⟩
  have hd : DifferentiableOn ℂ (fun b => M Q' b * Ring.inverse (M Q b)) (B ∩ M Q ⁻¹' {x | IsUnit x}) := by
    refine ((hM Q' hQ').mono Set.inter_subset_left).mul fun b hb => ?_
    exact (differentiableAt_inverse hb.2).comp_differentiableWithinAt b
      ((hM Q hQ).mono Set.inter_subset_left b hb)
  have hd2 : DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => (M Q' bz.1 * Ring.inverse (M Q bz.1)) bz.2)
      ((B ∩ M Q ⁻¹' {x | IsUnit x}) ×ˢ Set.univ) :=
    (hd.comp differentiableOn_fst fun bz hbz => hbz.1).clm_apply differentiableOn_snd
  refine hd2.congr fun bz hbz => ?_
  rw [ContinuousLinearMap.mul_apply, ← hkM _ hbz.1.1, ← ContinuousLinearMap.mul_apply,
    Ring.mul_inverse_cancel _ hbz.1.2, ContinuousLinearMap.one_apply]

/- English proof (translation)
Establish `: ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (k z)) U f) 0 w = fderiv ℂ (fun z => valAt' (e z) U f) 0 (k w)`. Introduce `U f`. Use `k.toContinuousLinearEquiv.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)` as an intermediate fact. Establish `h2` using `congrArg (fun L => L w) this`. Simplify `h2` using `[Function.comp_def]`.

Simplify using `only [IsDerivAt0, map_zero, this]`.
-/
theorem isDerivAt0_comp_equiv {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => e (k z)) w v ↔ IsDerivAt0 e (k w) v := by
  have : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (k z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (k w) := by
    intro U f
    have := k.toContinuousLinearEquiv.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    have h2 := congrArg (fun L => L w) this
    simpa [Function.comp_def] using h2
  simp only [IsDerivAt0, map_zero, this]

end GlobalTheory.HolPeriods
