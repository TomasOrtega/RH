import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InstSecondCountableSub
open MeasureTheory Matrix GlobalTheory.Dec GlobalTheory.IwaInt
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IwaInt

open Formalism.REAL

/- English proof (translation)
Introduce `G K B _ _ _ _ _ _ _ _ _ _ _ i j β ν lam μ D hi hj hβ hdec hr hl hν1 hν2 hl1 hl2 hl3 hl4 hm1 hm2 hm3 hD hD0 hDm hμ H hH hHe y`. Take `⟨s, hs, -, hs0, hs1⟩` from `Measure.exists_subset_measure_lt_top (μ := μ) (r := 0) MeasurableSet.univ (Measure.measure_univ_pos.2 hm2)`. Use `set φ : B → ENNReal := s.indicator 1 with hφ`. Establish `hφm : Measurable φ` using `measurable_one.indicator hs`. Establish `hφi : ∫⁻ b, φ b ∂μ = μ s` using `by rw [hφ, lintegral_indicator_one hs]`.

Establish `hmr : ∀ (h : B → ENNReal) (b : B), Measurable h → ∫⁻ x, h x ∂μ = D b * ∫⁻ x, h (x * b) ∂μ`. Introduce `h b hh`. Use `conv_lhs => rw [hμ b]`. Rewrite using `[lintegral_smul_measure, lintegral_map hh (measurable_mul_const b), smul_eq_mul]`. Set `Rf : (G → ENNReal) → G → ENNReal` to `fun f x => ∫⁻ b, f (x * (j b)⁻¹) ∂μ`.

Establish `hjm : Measurable fun q : G × B => q.1 * (j q.2)⁻¹` using `measurable_fst.mul (hj.comp measurable_snd).inv`. Establish `hRm : ∀ f, Measurable f → Measurable (Rf f)` using `fun f hf => Measurable.lintegral_prod_right' (f := fun q : G × B => f (q.1 * (j q.2)⁻¹)) (hf.comp hjm)`. Establish `hRe : ∀ f, Measurable f → ∀ x b, Rf f (x * j b) = Rf f x * D b` using `fun f hf x b => by`. Simplify using `only [Rf]`. Rewrite using `[hmr (fun z => f (x * j b * (j z)⁻¹)) b (hf.comp (hj.inv.const_mul _)), mul_comm]`.

Use `congr 1`. Use `lintegral_congr fun z => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[map_mul]`. Use `group`.

Use `set C : ENNReal := ∫⁻ x, φ (β x) * D (β x) ∂lam with hC`. Establish `hA : ∀ F : G → ENNReal, Measurable F → (∀ x b, F (x * j b) = F x * D b) → ∫⁻ x, F x * φ (β x) ∂lam = C * ∫⁻ k, F (i k) ∂ν`. Introduce `F hF hFe`. Combine the equalities or inequalities in the displayed calculation. Establish `: ∀ k, ∫⁻ x, F (i k * x) * φ (β x) ∂lam = ∫⁻ x, F x * φ (β x) ∂lam` using `fun k => by`.

Rewrite using `[← lintegral_mul_left_eq_self (fun x => F x * φ (β x)) (i k)]`. Simplify using `only [hl]`. Simplify using `[this]`. Use `_ = ∫⁻ x, ∫⁻ k, F (i k * x) * φ (β x) ∂ν ∂lam := lintegral_lintegral_swap (((hF.comp ((hi.comp measurable_fst).mul measurable_snd)).mul ((hφm.comp hβ).comp measurable_snd)).aemeasurable)`. Use `_ = ∫⁻ x, (φ (β x) * D (β x)) * ∫⁻ k, F (i k) ∂ν ∂lam := by`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Take `⟨k₀, hk₀⟩` from `hdec x`. Rewrite using `[← lintegral_mul_right_eq_self (fun k => F (i k)) k₀, ← lintegral_const_mul _ (f := fun k => F (i (k * k₀))) (hF.comp (hi.comp (measurable_mul_const k₀)))]`. Use `lintegral_congr fun k => ?_` and prove the remaining obligations. Establish `: i k * x = i (k * k₀) * j (β x)` using `by rw [map_mul, mul_assoc, ← hk₀]`.

Rewrite using `[this, hFe]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Conclude with `lintegral_mul_const _ ((hφm.comp hβ).mul (hD.comp hβ))`. Establish `hB : ∀ f : G → ENNReal, Measurable f → μ s * ∫⁻ x, f x ∂lam = C * ∫⁻ k, Rf f (i k) ∂ν`.

Introduce `f hf`. Rewrite using `[← hA _ (hRm f hf) (hRe f hf)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_const_mul _ hf]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Simplify using `only [hr]`. Rewrite using `[lintegral_const_mul _ (f := fun b => φ (β x * b)) (hφm.comp (measurable_const_mul _)), lintegral_mul_left_eq_self φ, hφi, mul_comm]`. Use `_ = ∫⁻ b, ∫⁻ x, f x * φ (β (x * j b)) ∂lam ∂μ := lintegral_lintegral_swap (((hf.comp measurable_fst).mul ((hφm.comp hβ).comp (measurable_fst.mul (hj.comp measurable_snd)))).aemeasurable)`. Use `_ = ∫⁻ b, ∫⁻ x, f (x * (j b)⁻¹) * φ (β x) ∂lam ∂μ := by`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations.

Use `conv_rhs => rw [← hl4 b]`. Rewrite using `[lintegral_map (f := fun x => f (x * (j b)⁻¹) * φ (β x)) ((hf.comp (measurable_mul_const _)).mul (hφm.comp hβ)) (measurable_mul_const _)]`. Simplify using the standard rewrite rules. Use `_ = ∫⁻ x, ∫⁻ b, f (x * (j b)⁻¹) * φ (β x) ∂μ ∂lam := (lintegral_lintegral_swap (((hf.comp hjm).mul ((hφm.comp hβ).comp measurable_fst)).aemeasurable)).symm`. Use `_ = _ := by`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_mul_const _ (f := fun b => f (x * (j b)⁻¹)) (hf.comp (hj.inv.const_mul _))]`. Take `⟨g, hg0, hgm, hg1⟩` from `exists_pos_lintegral_lt_of_sigmaFinite lam (ε := 1) one_ne_zero`. Establish `hgm' : Measurable fun x => (g x : ENNReal)` using `hgm.coe_nnreal_ennreal`. Establish `hposI : ∀ {X : Type} [MeasurableSpace X] (m : Measure X) (u : X → ENNReal), m ≠ 0 → Measurable u → (∀ x, u x ≠ 0) → ∫⁻ x, u x ∂m ≠ 0`.

Introduce `X _ m u hm hu h0 h`. Rewrite `h` using `[lintegral_eq_zero_iff hu]`. Establish `: ∀ᵐ x ∂m, False` using `h.mono fun x hx => h0 x hx`. Rewrite `this` using `[ae_iff]`. Conclude with `hm (by simpa using this)`.

Establish `hg` using `hB _ hgm'`. Establish `hC0 : C ≠ 0`. Introduce `h`. Rewrite `hg` using `[h, zero_mul]`. Conclude with `mul_ne_zero hs0.ne' (hposI lam _ hl2 hgm' fun x => by simpa using (hg0 x).ne') hg`.

Establish `hC1 : C ≠ ⊤`. Introduce `h`. Rewrite `hg` using `[h, ENNReal.top_mul (hposI ν (fun k => Rf (fun x => (g x : ENNReal)) (i k)) (IsProbabilityMeasure.ne_zero ν) ((hRm _ hgm').comp hi) fun k => hposI μ _ hm2 (hgm'.comp (hj.inv.const_mul _)) fun x => by simpa using (hg0 _).ne')]`. Conclude with `ENNReal.mul_ne_top hs1.ne (hg1.trans ENNReal.one_lt_top).ne hg`. Set `f : G → ENNReal` to `fun x => H x * (D (β x))⁻¹ * φ (β x)⁻¹`.

Establish `hfm : Measurable f` using `(hH.mul (hD.comp hβ).inv).mul (hφm.comp hβ.inv)`. Establish `hRf : ∀ x, Rf f x = μ s * H x` using `fun x => by`. Establish `e1 : ∀ b, f (x * (j b)⁻¹) = H x * (D (β x))⁻¹ * φ (b * (β x)⁻¹)` using `fun b => by`. Simplify using `only [f]`. Rewrite using `[← map_inv, hHe, hr, hDm, ENNReal.mul_inv (Or.inl (hD0 _).1) (Or.inl (hD0 _).2), _root_.mul_inv_rev, inv_inv]`.

Use `ENNReal.mul_inv_cancel (hD0 b⁻¹).1 (hD0 b⁻¹).2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Rf, e1]`. Rewrite using `[lintegral_const_mul _ (f := fun b => φ (b * (β x)⁻¹)) (hφm.comp (measurable_mul_const _)), hmr (fun b => φ (b * (β x)⁻¹)) (β x) (hφm.comp (measurable_mul_const _))]`. Simplify using `only [mul_inv_cancel_right, hφi]`.

Use `ENNReal.inv_mul_cancel (hD0 (β x)).1 (hD0 (β x)).2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `hB f hfm`. Establish `h2` using `hB (fun x => f (y * x)) (hfm.comp (measurable_const_mul y))`. Establish `h3 : ∀ x, Rf (fun x => f (y * x)) x = Rf f (y * x)` using `fun x => by simp only [Rf, mul_assoc]`.

Rewrite `h2` using `[lintegral_mul_left_eq_self f y, h1, ENNReal.mul_right_inj hC0 hC1]`. Simplify using `only [h3, hRf] at h2`. Rewrite `h2` using `[lintegral_const_mul' _ _ hs1.ne, lintegral_const_mul' _ _ hs1.ne, ENNReal.mul_right_inj hs0.ne' hs1.ne]`. Conclude with `h2.symm`.
-/
theorem lintegral_equivariant_left_invariant : ∀ (G K B : Type) [Group G] [Group K] [Group B] [MeasurableSpace G] [MeasurableSpace K] [MeasurableSpace B]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul₂ B] [MeasurableInv B] [MeasurableMul K]
    (i : K →* G) (j : B →* G) (β : G → B) (ν : Measure K) (lam : Measure G) (μ : Measure B) (D : B → ENNReal),
    Measurable i → Measurable j → Measurable β →
    (∀ x, ∃ k, x = i k * j (β x)) → (∀ x b, β (x * j b) = β x * b) → (∀ k x, β (i k * x) = β x) →
    IsProbabilityMeasure ν → ν.IsMulRightInvariant →
    SigmaFinite lam → lam ≠ 0 → lam.IsMulLeftInvariant → (∀ b, Measure.map (fun x => x * j b) lam = lam) →
    SigmaFinite μ → μ ≠ 0 → μ.IsMulLeftInvariant →
    Measurable D → (∀ b, D b ≠ 0 ∧ D b ≠ ⊤) → (∀ a b, D (a * b) = D a * D b) →
    (∀ b, μ = D b • Measure.map (fun x => x * b) μ) →
    ∀ H : G → ENNReal, Measurable H → (∀ x b, H (x * j b) = H x * D b) →
    ∀ y : G, ∫⁻ k, H (y * i k) ∂ν = ∫⁻ k, H (i k) ∂ν := by
  intro G K B _ _ _ _ _ _ _ _ _ _ _ i j β ν lam μ D hi hj hβ hdec hr hl hν1 hν2 hl1 hl2 hl3 hl4 hm1 hm2 hm3
    hD hD0 hDm hμ H hH hHe y
  obtain ⟨s, hs, -, hs0, hs1⟩ := Measure.exists_subset_measure_lt_top (μ := μ) (r := 0) MeasurableSet.univ
    (Measure.measure_univ_pos.2 hm2)
  set φ : B → ENNReal := s.indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator hs
  have hφi : ∫⁻ b, φ b ∂μ = μ s := by rw [hφ, lintegral_indicator_one hs]
  have hmr : ∀ (h : B → ENNReal) (b : B), Measurable h → ∫⁻ x, h x ∂μ = D b * ∫⁻ x, h (x * b) ∂μ := by
    intro h b hh
    conv_lhs => rw [hμ b]
    rw [lintegral_smul_measure, lintegral_map hh (measurable_mul_const b), smul_eq_mul]
  let Rf : (G → ENNReal) → G → ENNReal := fun f x => ∫⁻ b, f (x * (j b)⁻¹) ∂μ
  have hjm : Measurable fun q : G × B => q.1 * (j q.2)⁻¹ := measurable_fst.mul (hj.comp measurable_snd).inv
  have hRm : ∀ f, Measurable f → Measurable (Rf f) := fun f hf =>
    Measurable.lintegral_prod_right' (f := fun q : G × B => f (q.1 * (j q.2)⁻¹)) (hf.comp hjm)
  have hRe : ∀ f, Measurable f → ∀ x b, Rf f (x * j b) = Rf f x * D b := fun f hf x b => by
    simp only [Rf]
    rw [hmr (fun z => f (x * j b * (j z)⁻¹)) b (hf.comp (hj.inv.const_mul _)), mul_comm]
    congr 1
    refine lintegral_congr fun z => ?_
    congr 1
    rw [map_mul]; group
  set C : ENNReal := ∫⁻ x, φ (β x) * D (β x) ∂lam with hC
  have hA : ∀ F : G → ENNReal, Measurable F → (∀ x b, F (x * j b) = F x * D b) →
      ∫⁻ x, F x * φ (β x) ∂lam = C * ∫⁻ k, F (i k) ∂ν := by
    intro F hF hFe
    calc ∫⁻ x, F x * φ (β x) ∂lam = ∫⁻ k, ∫⁻ x, F (i k * x) * φ (β x) ∂lam ∂ν := by
          have : ∀ k, ∫⁻ x, F (i k * x) * φ (β x) ∂lam = ∫⁻ x, F x * φ (β x) ∂lam := fun k => by
            rw [← lintegral_mul_left_eq_self (fun x => F x * φ (β x)) (i k)]
            simp only [hl]
          simp [this]
      _ = ∫⁻ x, ∫⁻ k, F (i k * x) * φ (β x) ∂ν ∂lam :=
          lintegral_lintegral_swap
            (((hF.comp ((hi.comp measurable_fst).mul measurable_snd)).mul
              ((hφm.comp hβ).comp measurable_snd)).aemeasurable)
      _ = ∫⁻ x, (φ (β x) * D (β x)) * ∫⁻ k, F (i k) ∂ν ∂lam := by
          refine lintegral_congr fun x => ?_
          obtain ⟨k₀, hk₀⟩ := hdec x
          rw [← lintegral_mul_right_eq_self (fun k => F (i k)) k₀,
            ← lintegral_const_mul _ (f := fun k => F (i (k * k₀))) (hF.comp (hi.comp (measurable_mul_const k₀)))]
          refine lintegral_congr fun k => ?_
          have : i k * x = i (k * k₀) * j (β x) := by rw [map_mul, mul_assoc, ← hk₀]
          rw [this, hFe]; ring
      _ = _ := by
          exact lintegral_mul_const _ ((hφm.comp hβ).mul (hD.comp hβ))
  have hB : ∀ f : G → ENNReal, Measurable f → μ s * ∫⁻ x, f x ∂lam = C * ∫⁻ k, Rf f (i k) ∂ν := by
    intro f hf
    rw [← hA _ (hRm f hf) (hRe f hf)]
    calc μ s * ∫⁻ x, f x ∂lam = ∫⁻ x, ∫⁻ b, f x * φ (β (x * j b)) ∂μ ∂lam := by
          rw [← lintegral_const_mul _ hf]
          refine lintegral_congr fun x => ?_
          simp only [hr]
          rw [lintegral_const_mul _ (f := fun b => φ (β x * b)) (hφm.comp (measurable_const_mul _)),
            lintegral_mul_left_eq_self φ, hφi, mul_comm]
      _ = ∫⁻ b, ∫⁻ x, f x * φ (β (x * j b)) ∂lam ∂μ :=
          lintegral_lintegral_swap
            (((hf.comp measurable_fst).mul
              ((hφm.comp hβ).comp (measurable_fst.mul (hj.comp measurable_snd)))).aemeasurable)
      _ = ∫⁻ b, ∫⁻ x, f (x * (j b)⁻¹) * φ (β x) ∂lam ∂μ := by
          refine lintegral_congr fun b => ?_
          conv_rhs => rw [← hl4 b]
          rw [lintegral_map (f := fun x => f (x * (j b)⁻¹) * φ (β x))
            ((hf.comp (measurable_mul_const _)).mul (hφm.comp hβ)) (measurable_mul_const _)]
          simp
      _ = ∫⁻ x, ∫⁻ b, f (x * (j b)⁻¹) * φ (β x) ∂μ ∂lam :=
          (lintegral_lintegral_swap
            (((hf.comp hjm).mul ((hφm.comp hβ).comp measurable_fst)).aemeasurable)).symm
      _ = _ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_mul_const _ (f := fun b => f (x * (j b)⁻¹)) (hf.comp (hj.inv.const_mul _))]
  obtain ⟨g, hg0, hgm, hg1⟩ := exists_pos_lintegral_lt_of_sigmaFinite lam (ε := 1) one_ne_zero
  have hgm' : Measurable fun x => (g x : ENNReal) := hgm.coe_nnreal_ennreal
  have hposI : ∀ {X : Type} [MeasurableSpace X] (m : Measure X) (u : X → ENNReal), m ≠ 0 → Measurable u →
      (∀ x, u x ≠ 0) → ∫⁻ x, u x ∂m ≠ 0 := by
    intro X _ m u hm hu h0 h
    rw [lintegral_eq_zero_iff hu] at h
    have : ∀ᵐ x ∂m, False := h.mono fun x hx => h0 x hx
    rw [ae_iff] at this
    exact hm (by simpa using this)
  have hg := hB _ hgm'
  have hC0 : C ≠ 0 := by
    intro h
    rw [h, zero_mul] at hg
    exact mul_ne_zero hs0.ne' (hposI lam _ hl2 hgm' fun x => by simpa using (hg0 x).ne') hg
  have hC1 : C ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_mul (hposI ν (fun k => Rf (fun x => (g x : ENNReal)) (i k)) (IsProbabilityMeasure.ne_zero ν) ((hRm _ hgm').comp hi) fun k =>
      hposI μ _ hm2 (hgm'.comp (hj.inv.const_mul _)) fun x => by simpa using (hg0 _).ne')] at hg
    exact ENNReal.mul_ne_top hs1.ne (hg1.trans ENNReal.one_lt_top).ne hg
  let f : G → ENNReal := fun x => H x * (D (β x))⁻¹ * φ (β x)⁻¹
  have hfm : Measurable f := (hH.mul (hD.comp hβ).inv).mul (hφm.comp hβ.inv)
  have hRf : ∀ x, Rf f x = μ s * H x := fun x => by
    have e1 : ∀ b, f (x * (j b)⁻¹) = H x * (D (β x))⁻¹ * φ (b * (β x)⁻¹) := fun b => by
      simp only [f]
      rw [← map_inv, hHe, hr, hDm, ENNReal.mul_inv (Or.inl (hD0 _).1) (Or.inl (hD0 _).2), _root_.mul_inv_rev,
        inv_inv]
      have := ENNReal.mul_inv_cancel (hD0 b⁻¹).1 (hD0 b⁻¹).2
      calc _ = H x * (D (β x))⁻¹ * φ (b * (β x)⁻¹) * (D b⁻¹ * (D b⁻¹)⁻¹) := by ring
        _ = _ := by rw [this, mul_one]
    simp only [Rf, e1]
    rw [lintegral_const_mul _ (f := fun b => φ (b * (β x)⁻¹)) (hφm.comp (measurable_mul_const _)),
      hmr (fun b => φ (b * (β x)⁻¹)) (β x) (hφm.comp (measurable_mul_const _))]
    simp only [mul_inv_cancel_right, hφi]
    have := ENNReal.inv_mul_cancel (hD0 (β x)).1 (hD0 (β x)).2
    calc _ = μ s * H x * ((D (β x))⁻¹ * D (β x)) := by ring
      _ = _ := by rw [this, mul_one]
  have h1 := hB f hfm
  have h2 := hB (fun x => f (y * x)) (hfm.comp (measurable_const_mul y))
  have h3 : ∀ x, Rf (fun x => f (y * x)) x = Rf f (y * x) := fun x => by simp only [Rf, mul_assoc]
  rw [lintegral_mul_left_eq_self f y, h1, ENNReal.mul_right_inj hC0 hC1] at h2
  simp only [h3, hRf] at h2
  rw [lintegral_const_mul' _ _ hs1.ne, lintegral_const_mul' _ _ hs1.ne, ENNReal.mul_right_inj hs0.ne' hs1.ne] at h2
  exact h2.symm

/- English proof (translation)
Introduce `Γ ι _ _ _ _ _ _ c L R hc hL hR hL1 hR1 hLm hRm hcont`. Establish `hme : MeasurableEmbedding c` using `hc.measurableEmbedding`. Use `set ν : Measure Γ := Measure.comap c volume with hν`. Establish `hdL : ∀ x y, LinearMap.det (L (x * y)) = LinearMap.det (L x) * LinearMap.det (L y)` using `fun x y => by`. Rewrite using `[hLm, LinearMap.det_comp]`.

Establish `hL0 : ∀ x, LinearMap.det (L x) ≠ 0` using `fun x h => by`. Use `hdL x x⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hL1, h]`. Simplify using `at this`. Establish `hR0 : ∀ x, LinearMap.det (R x) ≠ 0` using `fun x h => by`.

Use `congrArg LinearMap.det (hRm x x⁻¹)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hR1, LinearMap.det_comp, h]`. Simplify using `at this`. Establish `hgen : ∀ (g g' : Γ → Γ) (T T' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), Measurable g → LinearMap.det T ≠ 0 → (∀ x, c (g x) = T (c x)) → (∀ x, c (g' x) = T' (c x)) → (∀ v, T' (T v) = v) → Measure.map g ν = ENNReal.ofReal |(LinearMap.det T)⁻¹| • ν`. Introduce `g g' T T' hg hT h1 h2 h3`.

Use extensionality with `s hs`. Establish `hset : c '' (g ⁻¹' s) = T ⁻¹' (c '' s)`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Conclude with `⟨g w, hw, h1 w⟩`. Introduce and unpack `⟨z, hz, hv⟩`. Establish `e : c (g' z) = v` using `by rw [h2, hv, h3]`. Use `⟨g' z, ?_, e⟩` and prove the remaining obligations. Establish `: g (g' z) = z` using `hc.injective (by rw [h1, e, hv])`.

Simplify `hz` using `[this]`. Rewrite using `[Measure.map_apply hg hs, Measure.smul_apply, hν, hme.comap_apply, hme.comap_apply, hset, ← Measure.map_apply T.continuous_of_finiteDimensional.measurable (hme.measurableSet_image.2 hs), Real.map_linearMap_volume_pi_eq_smul_volume_pi hT, Measure.smul_apply]`. Establish `hleft : ∀ a, Measure.map (fun x => a * x) ν = ENNReal.ofReal |(LinearMap.det (L a))⁻¹| • ν` using `fun a => hgen _ (fun x => a⁻¹ * x) (L a) (L a⁻¹) (measurable_const_mul a) (hL0 a) (hL a) (hL a⁻¹) fun v => by`. Rewrite using `[← LinearMap.comp_apply, ← hLm, inv_mul_cancel, hL1]`. Both sides reduce to the same expression.

Establish `hright : ∀ a, Measure.map (fun x => x * a) ν = ENNReal.ofReal |(LinearMap.det (R a))⁻¹| • ν` using `fun a => hgen _ (fun x => x * a⁻¹) (R a) (R a⁻¹) (measurable_mul_const a) (hR0 a) (fun x => hR x a) (fun x => hR x a⁻¹) fun v => by`. Rewrite using `[← LinearMap.comp_apply, ← hRm, mul_inv_cancel, hR1]`. Both sides reduce to the same expression. Use `set w : Γ → ENNReal := fun x => ENNReal.ofReal |(LinearMap.det (L x))⁻¹| with hw`. Establish `hwm : Measurable w` using `(hcont.measurable.inv.abs).ennreal_ofReal`.

Establish `hσ : SigmaFinite ν` using `SigmaFinite.of_map ν hme.measurable.aemeasurable (by`. Rewrite using `[hν, hme.map_comap]`. Use the proof step `infer_instance)`. Establish `hν0 : ν ≠ 0`. Introduce `h`.

Establish `h1 : ν Set.univ = 0` using `by rw [h]; rfl`. Rewrite `h1` using `[hν, hme.comap_apply, Set.image_univ]`. Conclude with `(hc.isOpen_range.measure_pos volume (Set.range_nonempty c)).ne' h1`. Establish `hsub : ∀ (g : Γ → Γ) (a : Γ) (r : ℝ), Measurable g → Measure.map g ν = ENNReal.ofReal |r⁻¹| • ν → (∀ x, LinearMap.det (L (g x)) = LinearMap.det (L a) * LinearMap.det (L x)) → Measure.map g (ν.withDensity w) = ENNReal.ofReal |LinearMap.det (L a) / r| • ν.withDensity w`. Introduce `g a r hg h1 h2`.

Use `Measure.ext_of_lintegral _ fun f hf => ?_` and prove the remaining obligations. Establish `hwx : ∀ x, w x = ENNReal.ofReal |LinearMap.det (L a)| * w (g x)` using `fun x => by`. Simplify using `only [hw]`. Rewrite using `[← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ (hL0 a), one_mul]`. Rewrite using `[lintegral_map hf hg, lintegral_withDensity_eq_lintegral_mul _ hwm (g := fun x => f (g x)) (hf.comp hg), lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hwm hf]`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`. Rewrite using `[hwx x, mul_assoc]`. Use `_ = ENNReal.ofReal |LinearMap.det (L a)| * ∫⁻ x, (w * f) x ∂(Measure.map g ν) := by`.

Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_map (hwm.mul hf) hg]`. Use `_ = _ := by`. Rewrite using `[h1, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, div_eq_mul_inv]`. Use `⟨ν.withDensity w, SigmaFinite.withDensity_of_ne_top' fun x => ENNReal.ofReal_ne_top, ?_, ⟨fun a => ?_⟩, fun b => ?_⟩` and prove the remaining obligations. Introduce `h`.

Use `withDensity_absolutelyContinuous' (μ := ν) hwm.aemeasurable (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (hL0 x)))).ne')` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `hν0 (Measure.absolutelyContinuous_zero_iff.1 this)`. Rewrite using `[hsub _ a _ (measurable_const_mul a) (hleft a) (hdL a), div_self (hL0 a)]`. Simplify using the standard rewrite rules.

Rewrite using `[hsub _ b _ (measurable_mul_const b) (hright b) (fun x => by rw [hdL, mul_comm]), smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, div_mul_div_cancel₀ (hL0 b), div_self (hR0 b)]`. Simplify using the standard rewrite rules.
-/
theorem exists_measure_of_linear_chart : ∀ (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ] [Fintype ι]
    (c : Γ → (ι → ℝ)) (L R : Γ → ((ι → ℝ) →ₗ[ℝ] (ι → ℝ))), Topology.IsOpenEmbedding c →
    (∀ x y, c (x * y) = L x (c y)) → (∀ x y, c (x * y) = R y (c x)) →
    L 1 = LinearMap.id → R 1 = LinearMap.id →
    (∀ x y, L (x * y) = L x ∘ₗ L y) → (∀ x y, R (x * y) = R y ∘ₗ R x) →
    Continuous (fun x => LinearMap.det (L x)) →
    ∃ μ : Measure Γ, SigmaFinite μ ∧ μ ≠ 0 ∧ μ.IsMulLeftInvariant ∧
      ∀ b, μ = ENNReal.ofReal |LinearMap.det (R b) / LinearMap.det (L b)| • Measure.map (fun x => x * b) μ := by
  intro Γ ι _ _ _ _ _ _ c L R hc hL hR hL1 hR1 hLm hRm hcont
  have hme : MeasurableEmbedding c := hc.measurableEmbedding
  set ν : Measure Γ := Measure.comap c volume with hν
  have hdL : ∀ x y, LinearMap.det (L (x * y)) = LinearMap.det (L x) * LinearMap.det (L y) := fun x y => by
    rw [hLm, LinearMap.det_comp]
  have hL0 : ∀ x, LinearMap.det (L x) ≠ 0 := fun x h => by
    have := hdL x x⁻¹
    rw [mul_inv_cancel, hL1, h] at this
    simp at this
  have hR0 : ∀ x, LinearMap.det (R x) ≠ 0 := fun x h => by
    have := congrArg LinearMap.det (hRm x x⁻¹)
    rw [mul_inv_cancel, hR1, LinearMap.det_comp, h] at this
    simp at this
  have hgen : ∀ (g g' : Γ → Γ) (T T' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), Measurable g → LinearMap.det T ≠ 0 →
      (∀ x, c (g x) = T (c x)) → (∀ x, c (g' x) = T' (c x)) → (∀ v, T' (T v) = v) →
      Measure.map g ν = ENNReal.ofReal |(LinearMap.det T)⁻¹| • ν := by
    intro g g' T T' hg hT h1 h2 h3
    ext s hs
    have hset : c '' (g ⁻¹' s) = T ⁻¹' (c '' s) := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨g w, hw, h1 w⟩
      · rintro ⟨z, hz, hv⟩
        have e : c (g' z) = v := by rw [h2, hv, h3]
        refine ⟨g' z, ?_, e⟩
        have : g (g' z) = z := hc.injective (by rw [h1, e, hv])
        simpa [this] using hz
    rw [Measure.map_apply hg hs, Measure.smul_apply, hν, hme.comap_apply, hme.comap_apply, hset,
      ← Measure.map_apply T.continuous_of_finiteDimensional.measurable (hme.measurableSet_image.2 hs),
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hT, Measure.smul_apply]
  have hleft : ∀ a, Measure.map (fun x => a * x) ν = ENNReal.ofReal |(LinearMap.det (L a))⁻¹| • ν := fun a =>
    hgen _ (fun x => a⁻¹ * x) (L a) (L a⁻¹) (measurable_const_mul a) (hL0 a) (hL a) (hL a⁻¹) fun v => by
      rw [← LinearMap.comp_apply, ← hLm, inv_mul_cancel, hL1]; rfl
  have hright : ∀ a, Measure.map (fun x => x * a) ν = ENNReal.ofReal |(LinearMap.det (R a))⁻¹| • ν := fun a =>
    hgen _ (fun x => x * a⁻¹) (R a) (R a⁻¹) (measurable_mul_const a) (hR0 a) (fun x => hR x a)
      (fun x => hR x a⁻¹) fun v => by
      rw [← LinearMap.comp_apply, ← hRm, mul_inv_cancel, hR1]; rfl
  set w : Γ → ENNReal := fun x => ENNReal.ofReal |(LinearMap.det (L x))⁻¹| with hw
  have hwm : Measurable w := (hcont.measurable.inv.abs).ennreal_ofReal
  have hσ : SigmaFinite ν := SigmaFinite.of_map ν hme.measurable.aemeasurable (by
    rw [hν, hme.map_comap]; infer_instance)
  have hν0 : ν ≠ 0 := by
    intro h
    have h1 : ν Set.univ = 0 := by rw [h]; rfl
    rw [hν, hme.comap_apply, Set.image_univ] at h1
    exact (hc.isOpen_range.measure_pos volume (Set.range_nonempty c)).ne' h1

  have hsub : ∀ (g : Γ → Γ) (a : Γ) (r : ℝ), Measurable g → Measure.map g ν = ENNReal.ofReal |r⁻¹| • ν →
      (∀ x, LinearMap.det (L (g x)) = LinearMap.det (L a) * LinearMap.det (L x)) →
      Measure.map g (ν.withDensity w) = ENNReal.ofReal |LinearMap.det (L a) / r| • ν.withDensity w := by
    intro g a r hg h1 h2
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    have hwx : ∀ x, w x = ENNReal.ofReal |LinearMap.det (L a)| * w (g x) := fun x => by
      simp only [hw]
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ (hL0 a), one_mul]
    rw [lintegral_map hf hg, lintegral_withDensity_eq_lintegral_mul _ hwm (g := fun x => f (g x)) (hf.comp hg),
      lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hwm hf]
    calc ∫⁻ x, (w * fun x => f (g x)) x ∂ν
        = ∫⁻ x, ENNReal.ofReal |LinearMap.det (L a)| * (w * f) (g x) ∂ν := by
          refine lintegral_congr fun x => ?_
          simp only [Pi.mul_apply]
          rw [hwx x, mul_assoc]
      _ = ENNReal.ofReal |LinearMap.det (L a)| * ∫⁻ x, (w * f) x ∂(Measure.map g ν) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_map (hwm.mul hf) hg]
      _ = _ := by
          rw [h1, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
            ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, div_eq_mul_inv]
  refine ⟨ν.withDensity w, SigmaFinite.withDensity_of_ne_top' fun x => ENNReal.ofReal_ne_top, ?_, ⟨fun a => ?_⟩,
    fun b => ?_⟩
  · intro h
    have := withDensity_absolutelyContinuous' (μ := ν) hwm.aemeasurable
      (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (hL0 x)))).ne')
    rw [h] at this
    exact hν0 (Measure.absolutelyContinuous_zero_iff.1 this)
  · rw [hsub _ a _ (measurable_const_mul a) (hleft a) (hdL a), div_self (hL0 a)]
    simp
  · rw [hsub _ b _ (measurable_mul_const b) (hright b) (fun x => by rw [hdL, mul_comm]), smul_smul,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, div_mul_div_cancel₀ (hL0 b), div_self (hR0 b)]
    simp

/- English proof (translation)
Introduce `n p _ b hlo hpos`. Establish `hre : ∀ l, b l l = ((‖b l l‖ : ℝ) : ℂ)` using `fun l => (Complex.norm_of_nonneg' (hpos l).le).symm`. Establish `hre1 : ∀ l, (b l l).re = ‖b l l‖` using `fun l => by rw [hre l]; simp`. Establish `him : ∀ l, (b l l).im = 0` using `fun l => by rw [hre l]; simp`. Establish `hemb : ∀ s : {t // p t}, emb p (Pi.single s 1) = Matrix.single s.1.1 s.1.2.1 (if s.1.2.2 then Complex.I else 1)`.

Introduce and unpack `⟨⟨i, j, s⟩, h⟩`. Use extensionality with `a c`. Distinguish the cases in `hac : i = a ∧ j = c`. Take `⟨rfl, rfl⟩` from `hac`. Apply the tactic sequence `cases s <;> apply Complex.ext <;> simp [emb, h, Pi.single_apply]`.

Rewrite using `[Matrix.single_apply_of_ne _ _ _ _ _ hac]`. Apply the tactic sequence `apply Complex.ext <;> simp [emb, Pi.single_apply] <;> grind`. Prove the components needed by the constructor for the conclusion. Use `letI : LinearOrder {t // p t} := LinearOrder.lift' (fun t => (toLex (t.1.1, toLex (t.1.2.1, t.1.2.2)) : Fin n ×ₗ Fin n ×ₗ Bool)) (fun s t h => Subtype.ext (by`. Use `toLex.injective h` as an intermediate fact.

Simplify using `only [Prod.mk.injEq, toLex_inj] at this`. Conclude with `Prod.ext this.1 (Prod.ext this.2.1 this.2.2)))`. Establish `hent : ∀ t s : {t // p t}, LinearMap.toMatrix' (Lc p b) t s = crd p (b * Matrix.single s.1.1 s.1.2.1 (if s.1.2.2 then Complex.I else 1)) t` using `fun t s => by`. Rewrite using `[LinearMap.toMatrix'_apply, ← hemb]`. Both sides reduce to the same expression.

Rewrite using `[← LinearMap.det_toMatrix', Matrix.det_of_lowerTriangular]`. Use `Finset.prod_congr rfl ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨i, j, s⟩, h⟩ -`. Rewrite using `[hent]`. Apply the tactic sequence `cases s <;> simp [crd, hre1]`.

Introduce and unpack `⟨⟨i, j, s⟩, h⟩ ⟨⟨i', j', s'⟩, h'⟩ hlt`. Establish `hlt' : (toLex (i, toLex (j, s)) : Fin n ×ₗ Fin n ×ₗ Bool) < toLex (i', toLex (j', s'))` using `hlt`. Rewrite using `[hent]`. Simplify using `only [Prod.Lex.toLex_lt_toLex] at hlt'`. Distinguish the cases in `hj : j = j'`.

Substitute `hj` using the available equality. Break down `hlt' with h1 | ⟨rfl, h1 | ⟨-, h1⟩⟩` into its components or cases. Simplify using `[crd, hlo i i' h1]`. Conclude with `absurd h1 (lt_irrefl _)`. Apply the tactic sequence `cases s <;> cases s' <;> simp [crd, him] at h1 ⊢`.

Simplify using `[crd, Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]`. Use `letI : LinearOrder {t // p t} := LinearOrder.lift' (fun t => (toLex (t.1.2.1, toLex (t.1.1, t.1.2.2)) : Fin n ×ₗ Fin n ×ₗ Bool)) (fun s t h => Subtype.ext (by`. Use `toLex.injective h` as an intermediate fact. Simplify using `only [Prod.mk.injEq, toLex_inj] at this`. Conclude with `Prod.ext this.2.1 (Prod.ext this.1 this.2.2)))`.

Establish `hent : ∀ t s : {t // p t}, LinearMap.toMatrix' (Rc p b) t s = crd p (Matrix.single s.1.1 s.1.2.1 (if s.1.2.2 then Complex.I else 1) * b) t` using `fun t s => by`. Rewrite using `[LinearMap.toMatrix'_apply, ← hemb]`. Both sides reduce to the same expression. Rewrite using `[← LinearMap.det_toMatrix', Matrix.det_of_upperTriangular]`. Use `Finset.prod_congr rfl ?_` and prove the remaining obligations.

Introduce and unpack `⟨⟨i, j, s⟩, h⟩ -`. Rewrite using `[hent]`. Apply the tactic sequence `cases s <;> simp [crd, hre1]`. Introduce and unpack `⟨⟨i, j, s⟩, h⟩ ⟨⟨i', j', s'⟩, h'⟩ hlt`. Establish `hlt' : (toLex (j', toLex (i', s')) : Fin n ×ₗ Fin n ×ₗ Bool) < toLex (j, toLex (i, s))` using `hlt`.

Rewrite using `[hent]`. Simplify using `only [Prod.Lex.toLex_lt_toLex] at hlt'`. Distinguish the cases in `hi : i = i'`. Substitute `hi` using the available equality. Break down `hlt' with h1 | ⟨rfl, h1 | ⟨-, h1⟩⟩` into its components or cases.

Simplify using `[crd, hlo j' j h1]`. Conclude with `absurd h1 (lt_irrefl _)`. Apply the tactic sequence `cases s <;> cases s' <;> simp [crd, him] at h1 ⊢`. Simplify using `[crd, Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]`.
-/
theorem det_Lc_Rc : ∀ (n : ℕ) (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (b : Matrix (Fin n) (Fin n) ℂ),
    IsLo b → (∀ l, 0 < b l l) →
    LinearMap.det (Lc p b) = ∏ t : {t // p t}, ‖b t.1.1 t.1.1‖ ∧
    LinearMap.det (Rc p b) = ∏ t : {t // p t}, ‖b t.1.2.1 t.1.2.1‖ := by
  intro n p _ b hlo hpos
  classical
  have hre : ∀ l, b l l = ((‖b l l‖ : ℝ) : ℂ) := fun l => (Complex.norm_of_nonneg' (hpos l).le).symm
  have hre1 : ∀ l, (b l l).re = ‖b l l‖ := fun l => by rw [hre l]; simp
  have him : ∀ l, (b l l).im = 0 := fun l => by rw [hre l]; simp
  have hemb : ∀ s : {t // p t}, emb p (Pi.single s 1) =
      Matrix.single s.1.1 s.1.2.1 (if s.1.2.2 then Complex.I else 1) := by
    rintro ⟨⟨i, j, s⟩, h⟩
    ext a c
    by_cases hac : i = a ∧ j = c
    · obtain ⟨rfl, rfl⟩ := hac
      cases s <;> apply Complex.ext <;> simp [emb, h, Pi.single_apply]
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ hac]
      apply Complex.ext <;> simp [emb, Pi.single_apply] <;> grind
  constructor
  · letI : LinearOrder {t // p t} := LinearOrder.lift'
      (fun t => (toLex (t.1.1, toLex (t.1.2.1, t.1.2.2)) : Fin n ×ₗ Fin n ×ₗ Bool))
      (fun s t h => Subtype.ext (by
        have := toLex.injective h
        simp only [Prod.mk.injEq, toLex_inj] at this
        exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2)))
    have hent : ∀ t s : {t // p t}, LinearMap.toMatrix' (Lc p b) t s =
        crd p (b * Matrix.single s.1.1 s.1.2.1 (if s.1.2.2 then Complex.I else 1)) t := fun t s => by
      rw [LinearMap.toMatrix'_apply, ← hemb]; rfl
    rw [← LinearMap.det_toMatrix', Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl ?_
      rintro ⟨⟨i, j, s⟩, h⟩ -
      rw [hent]
      cases s <;> simp [crd, hre1]
    · rintro ⟨⟨i, j, s⟩, h⟩ ⟨⟨i', j', s'⟩, h'⟩ hlt
      have hlt' : (toLex (i, toLex (j, s)) : Fin n ×ₗ Fin n ×ₗ Bool) < toLex (i', toLex (j', s')) := hlt
      rw [hent]
      simp only [Prod.Lex.toLex_lt_toLex] at hlt'
      by_cases hj : j = j'
      · subst hj
        rcases hlt' with h1 | ⟨rfl, h1 | ⟨-, h1⟩⟩
        · simp [crd, hlo i i' h1]
        · exact absurd h1 (lt_irrefl _)
        · cases s <;> cases s' <;> simp [crd, him] at h1 ⊢
      · simp [crd, Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]
  · letI : LinearOrder {t // p t} := LinearOrder.lift'
      (fun t => (toLex (t.1.2.1, toLex (t.1.1, t.1.2.2)) : Fin n ×ₗ Fin n ×ₗ Bool))
      (fun s t h => Subtype.ext (by
        have := toLex.injective h
        simp only [Prod.mk.injEq, toLex_inj] at this
        exact Prod.ext this.2.1 (Prod.ext this.1 this.2.2)))
    have hent : ∀ t s : {t // p t}, LinearMap.toMatrix' (Rc p b) t s =
        crd p (Matrix.single s.1.1 s.1.2.1 (if s.1.2.2 then Complex.I else 1) * b) t := fun t s => by
      rw [LinearMap.toMatrix'_apply, ← hemb]; rfl
    rw [← LinearMap.det_toMatrix', Matrix.det_of_upperTriangular]
    · refine Finset.prod_congr rfl ?_
      rintro ⟨⟨i, j, s⟩, h⟩ -
      rw [hent]
      cases s <;> simp [crd, hre1]
    · rintro ⟨⟨i, j, s⟩, h⟩ ⟨⟨i', j', s'⟩, h'⟩ hlt
      have hlt' : (toLex (j', toLex (i', s')) : Fin n ×ₗ Fin n ×ₗ Bool) < toLex (j, toLex (i, s)) := hlt
      rw [hent]
      simp only [Prod.Lex.toLex_lt_toLex] at hlt'
      by_cases hi : i = i'
      · subst hi
        rcases hlt' with h1 | ⟨rfl, h1 | ⟨-, h1⟩⟩
        · simp [crd, hlo j' j h1]
        · exact absurd h1 (lt_irrefl _)
        · cases s <;> cases s' <;> simp [crd, him] at h1 ⊢
      · simp [crd, Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]

/- English proof (translation)
Introduce `n ε x hx`. Prove the components needed by the constructor for the conclusion. Set `e : {t // pV ε t} ≃ {t // pV ε t}` to `{ toFun := fun t => ⟨(t.1.2.1, t.1.1, t.1.2.2), t.2.symm⟩ invFun := fun t => ⟨(t.1.2.1, t.1.1, t.1.2.2), t.2.symm⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Conclude with `Fintype.prod_equiv e _ _ fun _ => rfl`. Establish `hs : ∀ g : Fin n × Fin n × Bool → ℝ, (∏ t : {t // pW ε t}, g t.1) = ∏ i, ∏ j, ((if pW ε (i, j, true) then g (i, j, true) else 1) * (if pW ε (i, j, false) then g (i, j, false) else 1))` using `fun g => by`.

Rewrite using `[← Finset.prod_subtype (Finset.univ.filter (pW ε)) (by simp) g, Finset.prod_filter, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Simplify using `only [Fintype.prod_bool]`. Rewrite using `[hs fun t => x t.2.1, hs fun t => x t.1, Finset.prod_comm, ← Finset.prod_div_distrib]`.

Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `h1 : ∀ i, ((if pW ε (i, l, true) then x l else 1) * (if pW ε (i, l, false) then x l else 1)) = (if l < i ∧ ε i = ε l then x l ^ 2 else 1) * (if i = l then x l else 1)` using `fun i => by`. Break down `lt_trichotomy i l with h | h | h` into its components or cases. Simplify using `[pW, h.ne, h.le, h.not_gt]`. Substitute `h` using the available equality.

Simplify using `[pW]`. Apply the tactic sequence `by_cases he : ε i = ε l <;> simp [pW, h, h.ne', he, sq]`. Establish `h2 : ∀ j, ((if pW ε (l, j, true) then x l else 1) * (if pW ε (l, j, false) then x l else 1)) = (if j < l ∧ ε j = ε l then x l ^ 2 else 1) * (if j = l then x l else 1)` using `fun i => by`. Break down `lt_trichotomy i l with h | h | h` into its components or cases. Distinguish the cases in `he : ε l = ε i`.

Simplify using `[pW, h, h.ne, he, sq]`. Establish `he' : ¬ ε i = ε l` using `fun a => he a.symm`. Simplify using `[pW, h, h.ne, he, he']`. Substitute `h` using the available equality. Simplify using `[pW]`.

Simplify using `[pW, h.ne, h.ne', h.le, h.not_gt]`. Simplify using `only [h1, h2, Finset.prod_mul_distrib, ← Finset.prod_filter, Finset.prod_const]`. Establish `hl` using `hx l`. Simplify using `only [Formalism.REAL.rhoC]`. Rewrite using `[mul_div_mul_right _ _ (by positivity), ← pow_mul, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hl]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_coordinates : ∀ (n : ℕ) (ε : Fin n → Bool) (x : Fin n → ℝ), (∀ l, 0 < x l) →
    (∏ t : {t // pV ε t}, x t.1.2.1) = (∏ t : {t // pV ε t}, x t.1.1) ∧
    (∏ t : {t // pW ε t}, x t.1.2.1) / (∏ t : {t // pW ε t}, x t.1.1) = ∏ l, x l ^ (4 * Formalism.REAL.rhoC ε l) := by
  intro n ε x hx
  classical
  constructor
  · let e : {t // pV ε t} ≃ {t // pV ε t} :=
      { toFun := fun t => ⟨(t.1.2.1, t.1.1, t.1.2.2), t.2.symm⟩
        invFun := fun t => ⟨(t.1.2.1, t.1.1, t.1.2.2), t.2.symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.prod_equiv e _ _ fun _ => rfl
  · have hs : ∀ g : Fin n × Fin n × Bool → ℝ, (∏ t : {t // pW ε t}, g t.1) =
        ∏ i, ∏ j, ((if pW ε (i, j, true) then g (i, j, true) else 1) *
          (if pW ε (i, j, false) then g (i, j, false) else 1)) := fun g => by
      rw [← Finset.prod_subtype (Finset.univ.filter (pW ε)) (by simp) g, Finset.prod_filter,
        Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fintype.prod_prod_type]
      simp only [Fintype.prod_bool]
    rw [hs fun t => x t.2.1, hs fun t => x t.1, Finset.prod_comm, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    have h1 : ∀ i, ((if pW ε (i, l, true) then x l else 1) * (if pW ε (i, l, false) then x l else 1)) =
        (if l < i ∧ ε i = ε l then x l ^ 2 else 1) * (if i = l then x l else 1) := fun i => by
      rcases lt_trichotomy i l with h | h | h
      · simp [pW, h.ne, h.le, h.not_gt]
      · subst h; simp [pW]
      · by_cases he : ε i = ε l <;> simp [pW, h, h.ne', he, sq]
    have h2 : ∀ j, ((if pW ε (l, j, true) then x l else 1) * (if pW ε (l, j, false) then x l else 1)) =
        (if j < l ∧ ε j = ε l then x l ^ 2 else 1) * (if j = l then x l else 1) := fun i => by
      rcases lt_trichotomy i l with h | h | h
      · by_cases he : ε l = ε i
        · simp [pW, h, h.ne, he, sq]
        · have he' : ¬ ε i = ε l := fun a => he a.symm
          simp [pW, h, h.ne, he, he']
      · subst h; simp [pW]
      · simp [pW, h.ne, h.ne', h.le, h.not_gt]
    simp only [h1, h2, Finset.prod_mul_distrib, ← Finset.prod_filter, Finset.prod_const]
    have hl := hx l
    simp only [Formalism.REAL.rhoC]
    rw [mul_div_mul_right _ _ (by positivity), ← pow_mul, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_sub hl]
    congr 1
    push_cast
    ring

variable {n : ℕ}

/- English proof (translation)
Establish `hcc : Continuous (crd p)` using `LinearMap.continuous_of_finiteDimensional _`. Establish `hce : Continuous (emb p)` using `LinearMap.continuous_of_finiteDimensional _`. Establish `hval : Topology.IsEmbedding (fun g : Γ => g.1.1)` using `isEmbedding_val.comp Topology.IsEmbedding.subtypeVal`. Establish `hA : ∀ v, emb p (crd p (emb p v)) = emb p v` using `fun v => by rw [crd_emb]`. Use `exists_measure_of_linear_chart Γ {t // p t} (fun g => crd p g.1.1) (fun g => Lc p g.1.1) (fun g => Rc p g.1.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Use `⟨Topology.IsEmbedding.of_comp (hcc.comp hval.continuous) hce ?_, ?_⟩` and prove the remaining obligations. Use `hval using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `hΓ g`. Use `hopen using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨g, (hΓ g).symm⟩`. Introduce and unpack `⟨g, hg⟩`.

Conclude with `⟨g, by simp only [hg, crd_emb]⟩`. Introduce `x y`. Simplify using `[Lc, hΓ]`. Introduce `x y`. Simplify using `[Rc, hΓ]`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[Lc, crd_emb]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[Rc, crd_emb]`. Introduce `x y`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[Lc, hmul _ _ (hΓ y) (hA v), mul_assoc]`. Introduce `x y`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[Rc, hmul _ _ (hA v) (hΓ x), mul_assoc]`.

Simplify using `only [← LinearMap.det_toMatrix']`. Use `Continuous.matrix_det (continuous_matrix fun s t => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.toMatrix'_apply, Lc, LinearMap.comp_apply, LinearMap.mulLeft_apply]`. Conclude with `(continuous_apply s).comp (hcc.comp (hval.continuous.mul continuous_const))`.
-/
lemma haarSub (p : Fin n × Fin n × Bool → Prop) [DecidablePred p] (Γ : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ)
    [MeasurableSpace Γ] [BorelSpace Γ]
    (hΓ : ∀ g : Γ, emb p (crd p g.1.1) = g.1.1)
    (hmul : ∀ x y, emb p (crd p x) = x → emb p (crd p y) = y → emb p (crd p (x * y)) = x * y)
    (hopen : IsOpen {v | ∃ g : Γ, g.1.1 = emb p v}) :
    ∃ μ : Measure Γ, SigmaFinite μ ∧ μ ≠ 0 ∧ μ.IsMulLeftInvariant ∧
      ∀ b : Γ, μ = ENNReal.ofReal |LinearMap.det (Rc p b.1.1) / LinearMap.det (Lc p b.1.1)| •
        Measure.map (fun x => x * b) μ := by
  have hcc : Continuous (crd p) := LinearMap.continuous_of_finiteDimensional _
  have hce : Continuous (emb p) := LinearMap.continuous_of_finiteDimensional _
  have hval : Topology.IsEmbedding (fun g : Γ => g.1.1) :=
    isEmbedding_val.comp Topology.IsEmbedding.subtypeVal
  have hA : ∀ v, emb p (crd p (emb p v)) = emb p v := fun v => by rw [crd_emb]
  refine exists_measure_of_linear_chart Γ {t // p t} (fun g => crd p g.1.1) (fun g => Lc p g.1.1) (fun g => Rc p g.1.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨Topology.IsEmbedding.of_comp (hcc.comp hval.continuous) hce ?_, ?_⟩
    · convert hval using 1
      funext g
      exact hΓ g
    · convert hopen using 1
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, (hΓ g).symm⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, by simp only [hg, crd_emb]⟩
  · intro x y
    simp [Lc, hΓ]
  · intro x y
    simp [Rc, hΓ]
  · refine LinearMap.ext fun v => ?_
    simp [Lc, crd_emb]
  · refine LinearMap.ext fun v => ?_
    simp [Rc, crd_emb]
  · intro x y
    refine LinearMap.ext fun v => ?_
    simp [Lc, hmul _ _ (hΓ y) (hA v), mul_assoc]
  · intro x y
    refine LinearMap.ext fun v => ?_
    simp [Rc, hmul _ _ (hA v) (hΓ x), mul_assoc]
  · classical
    simp only [← LinearMap.det_toMatrix']
    refine Continuous.matrix_det (continuous_matrix fun s t => ?_)
    simp only [LinearMap.toMatrix'_apply, Lc, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    exact (continuous_apply s).comp (hcc.comp (hval.continuous.mul continuous_const))

/- English proof (translation)
Rewrite using `[emb_crd_iff, comm_J_iff]`. Use `forall₂_congr fun i j => ⟨fun h hij => Complex.ext (h.1 hij) (h.2 hij), fun h => ⟨fun hij => ?_, fun hij => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[h hij]`. Both sides reduce to the same expression. Rewrite using `[h hij]`.

Both sides reduce to the same expression.
-/
lemma inV_iff (ε : Fin n → Bool) (x : Matrix (Fin n) (Fin n) ℂ) :
    emb (pV ε) (crd (pV ε) x) = x ↔ x * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * x := by
  rw [emb_crd_iff, comm_J_iff]
  refine forall₂_congr fun i j => ⟨fun h hij => Complex.ext (h.1 hij) (h.2 hij), fun h => ⟨fun hij => ?_, fun hij => ?_⟩⟩
  · rw [h hij]; rfl
  · rw [h hij]; rfl

/- English proof (translation)
Rewrite using `[emb_crd_iff, comm_J_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i j hij => Complex.ext ((h i j).1 fun hp => hij hp.1) ((h i j).2 fun hp => hij hp.1), fun i j hij => Complex.ext ((h i j).1 ?_) ((h i j).2 ?_), fun l => (h l l).2 (by simp [pW])⟩` and prove the remaining obligations. Simplify using `[pW, hij.ne, hij.le]`.

Simplify using `[pW, hij.le]`. Introduce and unpack `⟨h1, h2, h3⟩ i j`. Distinguish the cases in `hij : ε i = ε j`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[h2 i j h]`.

Simplify using the standard rewrite rules. Substitute `h` using the available equality. Simplify using `[pW, h3]`. Simplify using `[pW, hij, h]`. Rewrite using `[h1 i j hij]`.

Simplify using the standard rewrite rules.
-/
lemma inW_iff (ε : Fin n → Bool) (x : Matrix (Fin n) (Fin n) ℂ) :
    emb (pW ε) (crd (pW ε) x) = x ↔
      x * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * x ∧ IsLo x ∧ ∀ l, (x l l).im = 0 := by
  rw [emb_crd_iff, comm_J_iff]
  constructor
  · intro h
    refine ⟨fun i j hij => Complex.ext ((h i j).1 fun hp => hij hp.1) ((h i j).2 fun hp => hij hp.1),
      fun i j hij => Complex.ext ((h i j).1 ?_) ((h i j).2 ?_), fun l => (h l l).2 (by simp [pW])⟩
    · simp [pW, hij.ne, hij.le]
    · simp [pW, hij.le]
  · rintro ⟨h1, h2, h3⟩ i j
    by_cases hij : ε i = ε j
    · rcases lt_trichotomy i j with h | h | h
      · rw [h2 i j h]; simp
      · subst h; simp [pW, h3]
      · simp [pW, hij, h]
    · rw [h1 i j hij]; simp

/- English proof (translation)
Take `⟨μ, h1, h2, h3, h4⟩` from `haarSub (pV ε) (GC ε) (fun g => (inV_iff ε _).2 g.2) (fun x y hx hy => by`. Rewrite `*` using `[inV_iff]`. Conclude with `Commute.mul_left hx hy)`. Use the proof step `(by`. Establish `hce : Continuous (emb (pV ε))` using `LinearMap.continuous_of_finiteDimensional _`.

Establish `: IsOpen {v | (emb (pV ε) v).det ≠ 0}` using `isOpen_ne_fun hce.matrix_det continuous_const`. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`.

Rewrite using `[Set.mem_setOf_eq, ← hg]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit).ne_zero`. Introduce `hv`. Establish `hu : IsUnit (emb (pV ε) v)` using `(Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hv)`. Conclude with `⟨⟨hu.unit, (inV_iff ε _).1 (by rw [hu.unit_spec, crd_emb])⟩, rfl⟩)`.

Use `⟨μ, h1, h2, h3, fun b hb => ?_⟩` and prove the remaining obligations. Establish `hd` using `det_Lc_Rc n (pV ε) b.1.1 hb.2.1 hb.2.2`. Establish `hpos : ∀ l, 0 < ‖b.1.1 l l‖` using `fun l => norm_pos_iff.2 (hb.2.2 l).ne'`. Establish `hp` using `(prod_coordinates n ε (fun l => ‖b.1.1 l l‖) hpos).1`. Establish `h5` using `h4 b`.

Rewrite `h5` using `[hd.1, hd.2, hp, div_self (Finset.prod_pos fun t _ => hpos _).ne']`. Simplify using `using h5.symm`.
-/
lemma haarGC (ε : Fin n → Bool) :
    ∃ μ : Measure (GC ε), SigmaFinite μ ∧ μ ≠ 0 ∧ μ.IsMulLeftInvariant ∧
      ∀ b : GC ε, b.1 ∈ BC ε → Measure.map (fun x => x * b) μ = μ := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := haarSub (pV ε) (GC ε) (fun g => (inV_iff ε _).2 g.2)
    (fun x y hx hy => by
      rw [inV_iff] at *
      exact Commute.mul_left hx hy)
    (by
      have hce : Continuous (emb (pV ε)) := LinearMap.continuous_of_finiteDimensional _
      have : IsOpen {v | (emb (pV ε) v).det ≠ 0} := isOpen_ne_fun hce.matrix_det continuous_const
      convert this using 1
      ext v
      constructor
      · rintro ⟨g, hg⟩
        rw [Set.mem_setOf_eq, ← hg]
        exact ((Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit).ne_zero
      · intro hv
        have hu : IsUnit (emb (pV ε) v) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hv)
        exact ⟨⟨hu.unit, (inV_iff ε _).1 (by rw [hu.unit_spec, crd_emb])⟩, rfl⟩)
  refine ⟨μ, h1, h2, h3, fun b hb => ?_⟩
  have hd := det_Lc_Rc n (pV ε) b.1.1 hb.2.1 hb.2.2
  have hpos : ∀ l, 0 < ‖b.1.1 l l‖ := fun l => norm_pos_iff.2 (hb.2.2 l).ne'
  have hp := (prod_coordinates n ε (fun l => ‖b.1.1 l l‖) hpos).1
  have h5 := h4 b
  rw [hd.1, hd.2, hp, div_self (Finset.prod_pos fun t _ => hpos _).ne'] at h5
  simpa using h5.symm

/- English proof (translation)
Take `⟨μ, h1, h2, h3, h4⟩` from `haarSub (pW ε) (BC ε) (fun g => (inW_iff ε _).2 ⟨g.2.1, g.2.2.1, fun l => (Complex.pos_iff.1 (g.2.2.2 l)).2.symm⟩) (fun x y hx hy => by`. Rewrite `*` using `[inW_iff]`. Use `⟨Commute.mul_left hx.1 hy.1, isLo_mul hx.2.1 hy.2.1, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[isLo_mul_diag hx.2.1 hy.2.1]`. Simplify using `[hx.2.2 l, hy.2.2 l])`.

Use the proof step `(by`. Establish `hce : Continuous (emb (pW ε))` using `LinearMap.continuous_of_finiteDimensional _`. Establish `: IsOpen (⋂ l, {v | 0 < (emb (pW ε) v l l).re})` using `isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (Complex.continuous_re.comp (hce.matrix_elem l l))`. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `v`.

Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩ l`. Rewrite using `[← hg]`. Conclude with `(Complex.pos_iff.1 (g.2.2.2 l)).1`.

Introduce `hv`. Establish `hW` using `(inW_iff ε (emb (pW ε) v)).1 (by rw [crd_emb])`. Establish `hp : ∀ l, 0 < emb (pW ε) v l l` using `fun l => Complex.pos_iff.2 ⟨hv l, (hW.2.2 l).symm⟩`. Establish `hu : IsUnit (emb (pW ε) v)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular _ (fun i j h => hW.2.1 i j h)]`.

Conclude with `Ne.isUnit (Finset.prod_ne_zero_iff.2 fun l _ => (hp l).ne')`. Conclude with `⟨⟨hu.unit, hW.1, hW.2.1, hp⟩, rfl⟩)`. Use `⟨μ, h1, h2, h3, fun b => ?_⟩` and prove the remaining obligations. Establish `hd` using `det_Lc_Rc n (pW ε) b.1.1 b.2.2.1 b.2.2.2`. Establish `hpos : ∀ l, 0 < ‖b.1.1 l l‖` using `fun l => norm_pos_iff.2 (b.2.2.2 l).ne'`.

Establish `hp` using `(prod_coordinates n ε (fun l => ‖b.1.1 l l‖) hpos).2`. Establish `h5` using `h4 b`. Rewrite `h5` using `[hd.1, hd.2, hp, abs_of_pos (Finset.prod_pos fun t _ => Real.rpow_pos_of_pos (hpos _) _)]`. Conclude with `h5`.
-/
lemma haarBC (ε : Fin n → Bool) :
    ∃ μ : Measure (BC ε), SigmaFinite μ ∧ μ ≠ 0 ∧ μ.IsMulLeftInvariant ∧
      ∀ b : BC ε, μ = ENNReal.ofReal (∏ l, ‖b.1.1 l l‖ ^ (4 * rhoC ε l)) • Measure.map (fun x => x * b) μ := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := haarSub (pW ε) (BC ε)
    (fun g => (inW_iff ε _).2 ⟨g.2.1, g.2.2.1, fun l => (Complex.pos_iff.1 (g.2.2.2 l)).2.symm⟩)
    (fun x y hx hy => by
      rw [inW_iff] at *
      refine ⟨Commute.mul_left hx.1 hy.1, isLo_mul hx.2.1 hy.2.1, fun l => ?_⟩
      rw [isLo_mul_diag hx.2.1 hy.2.1]
      simp [hx.2.2 l, hy.2.2 l])
    (by
      have hce : Continuous (emb (pW ε)) := LinearMap.continuous_of_finiteDimensional _
      have : IsOpen (⋂ l, {v | 0 < (emb (pW ε) v l l).re}) :=
        isOpen_iInter_of_finite fun l => isOpen_lt continuous_const
          (Complex.continuous_re.comp (hce.matrix_elem l l))
      convert this using 1
      ext v
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨g, hg⟩ l
        rw [← hg]
        exact (Complex.pos_iff.1 (g.2.2.2 l)).1
      · intro hv
        have hW := (inW_iff ε (emb (pW ε) v)).1 (by rw [crd_emb])
        have hp : ∀ l, 0 < emb (pW ε) v l l := fun l => Complex.pos_iff.2 ⟨hv l, (hW.2.2 l).symm⟩
        have hu : IsUnit (emb (pW ε) v) := by
          rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular _ (fun i j h => hW.2.1 i j h)]
          exact Ne.isUnit (Finset.prod_ne_zero_iff.2 fun l _ => (hp l).ne')
        exact ⟨⟨hu.unit, hW.1, hW.2.1, hp⟩, rfl⟩)
  refine ⟨μ, h1, h2, h3, fun b => ?_⟩
  have hd := det_Lc_Rc n (pW ε) b.1.1 b.2.2.1 b.2.2.2
  have hpos : ∀ l, 0 < ‖b.1.1 l l‖ := fun l => norm_pos_iff.2 (b.2.2.2 l).ne'
  have hp := (prod_coordinates n ε (fun l => ‖b.1.1 l l‖) hpos).2
  have h5 := h4 b
  rw [hd.1, hd.2, hp, abs_of_pos (Finset.prod_pos fun t _ => Real.rpow_pos_of_pos (hpos _) _)] at h5
  exact h5

def iK (ε : Fin n → Bool) : KG ε →* GC ε where
  toFun k := ⟨k.1.1, k.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def jB (ε : Fin n → Bool) : BC ε →* GC ε := Subgroup.inclusion fun _ h => h.1

/- English proof (translation)
Take `⟨κ₀, β₀, h1, hκ, hβ, h2⟩` from `hI n ε`. Establish `hKC : ∀ x : GC ε, x.1.1 ∈ KC ε` using `fun x => ⟨x.1.isUnit, x.2⟩`. Establish `hval : Continuous (fun g : GC ε => g.1.1)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hk : ∀ x : GC ε, ∃ k : KG ε, toMK k = κ₀ x.1.1` using `fun x => by`. Use `(h1 _ (hKC x)).1` as an intermediate fact.

Rewrite `this` using `[← range_toMK]`. Conclude with `this`. Use `choose κ hκ' using hk`. Establish `hb : ∀ x : GC ε, ∃ b : BC ε, b.1.1 = β₀ x.1.1` using `fun x => by`. Take `⟨-, a, b, c, -⟩` from `h1 _ (hKC x)`.

Conclude with `⟨⟨a.1.unit, a.2, b, c⟩, rfl⟩`. Use `choose β hβ' using hb`. Establish `hemb : Topology.IsEmbedding (fun k : KG ε => toMK k)` using `(isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal`. Establish `hembB : Topology.IsEmbedding (fun g : BC ε => g.1.1)` using `isEmbedding_val.comp Topology.IsEmbedding.subtypeVal`. Use `⟨κ, β, ?_, ?_, fun x => ?_, fun x k b hk hb hlo hpos hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[hemb.continuous_iff]`. Establish `: (fun k : KG ε => toMK k) ∘ κ = κ₀ ∘ fun g : GC ε => g.1.1` using `funext hκ'`. Rewrite using `[this]`. Conclude with `hκ.comp_continuous hval hKC`. Rewrite using `[hembB.continuous_iff]`.

Establish `: (fun g : BC ε => g.1.1) ∘ β = β₀ ∘ fun g : GC ε => g.1.1` using `funext hβ'`. Rewrite using `[this]`. Conclude with `hβ.comp_continuous hval hKC`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `show x.1.1 = toMK (κ x) * (β x).1.1`. Rewrite using `[hκ', hβ']`. Conclude with `(h1 _ (hKC x)).2.2.2.2`. Rewrite using `[hκ', hβ', hx]`. Conclude with `h2 k hk b hb hlo hpos`.
-/
lemma exists_kappa_beta (hI : IwasawaKC) (ε : Fin n → Bool) :
    ∃ (κ : GC ε → KG ε) (β : GC ε → BC ε), Continuous κ ∧ Continuous β ∧
      (∀ x, x = iK ε (κ x) * jB ε (β x)) ∧
      ∀ (x : GC ε) (k b : Matrix (Fin n) (Fin n) ℂ), k ∈ Kset ε → b ∈ KC ε → IsLo b → (∀ l, 0 < b l l) →
        x.1.1 = k * b → toMK (κ x) = k ∧ (β x).1.1 = b := by
  obtain ⟨κ₀, β₀, h1, hκ, hβ, h2⟩ := hI n ε
  have hKC : ∀ x : GC ε, x.1.1 ∈ KC ε := fun x => ⟨x.1.isUnit, x.2⟩
  have hval : Continuous (fun g : GC ε => g.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hk : ∀ x : GC ε, ∃ k : KG ε, toMK k = κ₀ x.1.1 := fun x => by
    have := (h1 _ (hKC x)).1
    rw [← range_toMK] at this
    exact this
  choose κ hκ' using hk
  have hb : ∀ x : GC ε, ∃ b : BC ε, b.1.1 = β₀ x.1.1 := fun x => by
    obtain ⟨-, a, b, c, -⟩ := h1 _ (hKC x)
    exact ⟨⟨a.1.unit, a.2, b, c⟩, rfl⟩
  choose β hβ' using hb
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hembB : Topology.IsEmbedding (fun g : BC ε => g.1.1) :=
    isEmbedding_val.comp Topology.IsEmbedding.subtypeVal
  refine ⟨κ, β, ?_, ?_, fun x => ?_, fun x k b hk hb hlo hpos hx => ?_⟩
  · rw [hemb.continuous_iff]
    have : (fun k : KG ε => toMK k) ∘ κ = κ₀ ∘ fun g : GC ε => g.1.1 := funext hκ'
    rw [this]
    exact hκ.comp_continuous hval hKC
  · rw [hembB.continuous_iff]
    have : (fun g : BC ε => g.1.1) ∘ β = β₀ ∘ fun g : GC ε => g.1.1 := funext hβ'
    rw [this]
    exact hβ.comp_continuous hval hKC
  · apply Subtype.ext
    apply Units.ext
    show x.1.1 = toMK (κ x) * (β x).1.1
    rw [hκ', hβ']
    exact (h1 _ (hKC x)).2.2.2.2
  · rw [hκ', hβ', hx]
    exact h2 k hk b hb hlo hpos

/- English proof (translation)
Introduce `n ε y κ₁ β₁ hy h F hF`. Take `⟨κ, β, hκ, hβ, hdec, huniq⟩` from `exists_kappa_beta hI ε`. Take `⟨lam, l1, l2, l3, l4⟩` from `haarGC ε`. Take `⟨μ, m1, m2, m3, m4⟩` from `haarBC ε`. Establish `hu : ∀ (k : KG ε) (b : BC ε), κ (iK ε k * jB ε b) = k ∧ β (iK ε k * jB ε b) = b` using `fun k b => by`.

Take `⟨e1, e2⟩` from `huniq (iK ε k * jB ε b) (toMK k) b.1.1 k.2 ⟨b.1.isUnit, b.2.1⟩ b.2.2.1 b.2.2.2 rfl`. Conclude with `⟨Subtype.ext (Subtype.ext (Units.ext e1)), Subtype.ext (Units.ext e2)⟩`. Establish `hr : ∀ x b, κ (x * jB ε b) = κ x ∧ β (x * jB ε b) = β x * b` using `fun x b => by`. Use `hu (κ x) (β x * b)` as an intermediate fact. Rewrite `this` using `[map_mul, ← mul_assoc, ← hdec x]`. Then use the resulting hypothesis.

Establish `hl : ∀ k x, β (iK ε k * x) = β x` using `fun k x => by`. Use `(hu (k * κ x) (β x)).2` as an intermediate fact. Rewrite `this` using `[map_mul, mul_assoc, ← hdec x]`. Then use the resulting hypothesis. Establish `h1 : ∀ k, κ (iK ε k) = k ∧ β (iK ε k) = 1` using `fun k => by`. Use `hu k 1` as an intermediate fact.

Rewrite `this` using `[map_one, mul_one]`. Then use the resulting hypothesis. Establish `hvalB : Continuous (fun g : BC ε => g.1.1)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hpos : ∀ (b : BC ε) l, 0 < ‖b.1.1 l l‖` using `fun b l => norm_pos_iff.2 (b.2.2.2 l).ne'`. Use `set d : BC ε → ℝ := fun b => ∏ l, ‖b.1.1 l l‖ ^ (4 * rhoC ε l) with hd`. Establish `dpos : ∀ b, 0 < d b` using `fun b => Finset.prod_pos fun t _ => Real.rpow_pos_of_pos (hpos _ _) _`.

Establish `dcont : Continuous d` using `continuous_finset_prod _ fun l _ => (hvalB.matrix_elem l l).norm.rpow_const fun b => Or.inl (hpos b l).ne'`. Establish `dmul : ∀ a b, d (a * b) = d a * d b` using `fun a b => by`. Simplify using `only [hd, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul, ← isLo_mul_diag a.2.2.1 b.2.2.1]`.

Both sides reduce to the same expression. Establish `done : d 1 = 1` using `by simp [hd]`. Establish `hi : Continuous (iK ε)` using `(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _`. Establish `hj : Continuous (jB ε)` using `continuous_subtype_val.subtype_mk _`. Establish `Dm : Measurable fun b => ENNReal.ofReal (d b)` using `dcont.measurable.ennreal_ofReal`.

Establish `key` using `lintegral_equivariant_left_invariant (GC ε) (KG ε) (BC ε) (iK ε) (jB ε) β (muK ε) lam μ (fun b => ENNReal.ofReal (d b)) hi.measurable hj.measurable hβ.measurable (fun x => ⟨_, hdec x⟩) (fun x b => (hr x b).2) hl inferInstance inferInstance l1 l2 l3 (fun b => l4 (jB ε b) b.2) m1 m …`. Set `Y : GC ε` to `⟨hy.1.unit, hy.2⟩`. Establish `hYc : Continuous fun k => Y * iK ε k` using `continuous_const.mul hi`. Establish `hm : Measurable fun k => κ (Y * iK ε k)` using `(hκ.comp hYc).measurable`. Establish `hm2 : Measurable fun k => ENNReal.ofReal (d (β (Y * iK ε k)))` using `Dm.comp (hβ.comp hYc).measurable`.

Establish `hmap : Measure.map (fun k => κ (Y * iK ε k)) ((muK ε).withDensity fun k => ENNReal.ofReal (d (β (Y * iK ε k)))) = muK ε`. Use `Measure.ext_of_lintegral _ fun f hf => ?_` and prove the remaining obligations. Rewrite using `[lintegral_map hf hm, lintegral_withDensity_eq_lintegral_mul _ hm2 (g := fun k => f (κ (Y * iK ε k))) (hf.comp hm)]`. Use `key (fun x => ENNReal.ofReal (d (β x)) * f (κ x)) ((Dm.comp hβ.measurable).mul (hf.comp hκ.measurable)) (fun x b => by` as an intermediate fact. Rewrite using `[(hr x b).1, (hr x b).2, dmul, ENNReal.ofReal_mul (dpos _).le]`.

Use the proof step `ring) Y`. Simplify `this` using `[h1, done]`. Establish `hFc : Continuous fun k : KG ε => F (toMK k)` using `hF.comp_continuous (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)) fun k => k.2`. Use `conv_rhs => rw [← hmap]`. Rewrite using `[integral_map hm.aemeasurable hFc.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hm2 (by simp)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, a5⟩` from `h k`. Take `⟨e1, e2⟩` from `huniq (Y * iK ε k) (κ₁ k) (β₁ k) a1 a2 a3 a4 a5`. Simplify using `only [ENNReal.toReal_ofReal (dpos _).le, e1, Complex.real_smul]`. Rewrite using `[mul_comm]`.

Simplify using `only [hd, e2]`.
-/
theorem iwasawaInt_of (hI : IwasawaKC) : IwasawaInt := by
  intro n ε y κ₁ β₁ hy h F hF
  obtain ⟨κ, β, hκ, hβ, hdec, huniq⟩ := exists_kappa_beta hI ε
  obtain ⟨lam, l1, l2, l3, l4⟩ := haarGC ε
  obtain ⟨μ, m1, m2, m3, m4⟩ := haarBC ε
  have hu : ∀ (k : KG ε) (b : BC ε), κ (iK ε k * jB ε b) = k ∧ β (iK ε k * jB ε b) = b := fun k b => by
    obtain ⟨e1, e2⟩ := huniq (iK ε k * jB ε b) (toMK k) b.1.1 k.2 ⟨b.1.isUnit, b.2.1⟩ b.2.2.1 b.2.2.2 rfl
    exact ⟨Subtype.ext (Subtype.ext (Units.ext e1)), Subtype.ext (Units.ext e2)⟩
  have hr : ∀ x b, κ (x * jB ε b) = κ x ∧ β (x * jB ε b) = β x * b := fun x b => by
    have := hu (κ x) (β x * b)
    rwa [map_mul, ← mul_assoc, ← hdec x] at this
  have hl : ∀ k x, β (iK ε k * x) = β x := fun k x => by
    have := (hu (k * κ x) (β x)).2
    rwa [map_mul, mul_assoc, ← hdec x] at this
  have h1 : ∀ k, κ (iK ε k) = k ∧ β (iK ε k) = 1 := fun k => by
    have := hu k 1
    rwa [map_one, mul_one] at this
  have hvalB : Continuous (fun g : BC ε => g.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hpos : ∀ (b : BC ε) l, 0 < ‖b.1.1 l l‖ := fun b l => norm_pos_iff.2 (b.2.2.2 l).ne'
  set d : BC ε → ℝ := fun b => ∏ l, ‖b.1.1 l l‖ ^ (4 * rhoC ε l) with hd
  have dpos : ∀ b, 0 < d b := fun b => Finset.prod_pos fun t _ => Real.rpow_pos_of_pos (hpos _ _) _
  have dcont : Continuous d := continuous_finset_prod _ fun l _ =>
    (hvalB.matrix_elem l l).norm.rpow_const fun b => Or.inl (hpos b l).ne'
  have dmul : ∀ a b, d (a * b) = d a * d b := fun a b => by
    simp only [hd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul, ← isLo_mul_diag a.2.2.1 b.2.2.1]
    rfl
  have done : d 1 = 1 := by simp [hd]
  have hi : Continuous (iK ε) := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hj : Continuous (jB ε) := continuous_subtype_val.subtype_mk _
  have Dm : Measurable fun b => ENNReal.ofReal (d b) := dcont.measurable.ennreal_ofReal
  have key := lintegral_equivariant_left_invariant (GC ε) (KG ε) (BC ε) (iK ε) (jB ε) β (muK ε) lam μ (fun b => ENNReal.ofReal (d b))
    hi.measurable hj.measurable hβ.measurable (fun x => ⟨_, hdec x⟩) (fun x b => (hr x b).2) hl
    inferInstance inferInstance l1 l2 l3 (fun b => l4 (jB ε b) b.2) m1 m2 m3 Dm
    (fun b => ⟨(ENNReal.ofReal_pos.2 (dpos b)).ne', ENNReal.ofReal_ne_top⟩)
    (fun a b => by rw [dmul, ENNReal.ofReal_mul (dpos a).le]) m4
  let Y : GC ε := ⟨hy.1.unit, hy.2⟩
  have hYc : Continuous fun k => Y * iK ε k := continuous_const.mul hi
  have hm : Measurable fun k => κ (Y * iK ε k) := (hκ.comp hYc).measurable
  have hm2 : Measurable fun k => ENNReal.ofReal (d (β (Y * iK ε k))) := Dm.comp (hβ.comp hYc).measurable
  have hmap : Measure.map (fun k => κ (Y * iK ε k))
      ((muK ε).withDensity fun k => ENNReal.ofReal (d (β (Y * iK ε k)))) = muK ε := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf hm, lintegral_withDensity_eq_lintegral_mul _ hm2 (g := fun k => f (κ (Y * iK ε k))) (hf.comp hm)]
    have := key (fun x => ENNReal.ofReal (d (β x)) * f (κ x))
      ((Dm.comp hβ.measurable).mul (hf.comp hκ.measurable))
      (fun x b => by
        rw [(hr x b).1, (hr x b).2, dmul, ENNReal.ofReal_mul (dpos _).le]; ring) Y
    simpa [h1, done] using this
  have hFc : Continuous fun k : KG ε => F (toMK k) :=
    hF.comp_continuous (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))
      fun k => k.2
  conv_rhs => rw [← hmap]
  rw [integral_map hm.aemeasurable hFc.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hm2 (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  obtain ⟨a1, a2, a3, a4, a5⟩ := h k
  obtain ⟨e1, e2⟩ := huniq (Y * iK ε k) (κ₁ k) (β₁ k) a1 a2 a3 a4 a5
  simp only [ENNReal.toReal_ofReal (dpos _).le, e1, Complex.real_smul]
  rw [mul_comm]
  simp only [hd, e2]

end GlobalTheory.IwaInt
