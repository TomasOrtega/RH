import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.CV.VolumeFunction

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

/- English proof (translation)
The claim follows from `|gam y a| ≤ (Fintype.card (Finset (Fin m → SignType)) : ℝ) := by classical unfold gam gamOn refine (Finset.abs_sum_le_sum_abs _ _).trans ?_ refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans ?_ · intro s _ rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Finset.abs_prod] e …`.
-/
theorem gam_abs_le {m : ℕ} (y : (Fin m → SignType) → ℝ) (a : Fin m → ℝ) :
    |gam y a| ≤ (Fintype.card (Finset (Fin m → SignType)) : ℝ) := by
  classical
  unfold gam gamOn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans ?_
  · intro s _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun e _ => by split_ifs <;> simp)
  · rw [nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_univ _

/- English proof (translation)
Use extensionality with `s hs`. Rewrite using `[Measure.map_apply (measurable_of_countable _) hs]`. Establish `h : e ⁻¹' s = e.symm '' s` using `Set.ext fun x => ⟨fun hx => ⟨e x, hx, e.symm_apply_apply x⟩, by`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `show e (e.symm y) ∈ s`.

Rewrite using `[e.apply_symm_apply]`. Conclude with `hy⟩`. Rewrite using `[h, Measure.count_injective_image e.symm.injective]`.
-/
theorem map_count_equiv {H : Type*} [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]
    (e : H ≃ H) : Measure.map e (Measure.count : Measure H) = Measure.count := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs]
  have h : e ⁻¹' s = e.symm '' s := Set.ext fun x => ⟨fun hx => ⟨e x, hx, e.symm_apply_apply x⟩, by
    rintro ⟨y, hy, rfl⟩
    show e (e.symm y) ∈ s
    rw [e.apply_symm_apply]; exact hy⟩
  rw [h, Measure.count_injective_image e.symm.injective]

/- English proof (translation)
Introduce `_ hK` and use `Measure.count_apply_lt_top.2 hK.finite_of_discrete map_mul_left_eq_self := fun g => map_count_equiv (Equiv.mulLeft g) open_pos := fun _ _ hU => by rw [Ne, Measure.count_eq_zero_iff]; exact hU.ne_empty`.
-/
theorem count_isHaar {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Countable H] : (Measure.count : Measure H).IsHaarMeasure where
  lt_top_of_isCompact := fun _ hK => Measure.count_apply_lt_top.2 hK.finite_of_discrete
  map_mul_left_eq_self := fun g => map_count_equiv (Equiv.mulLeft g)
  open_pos := fun _ _ hU => by rw [Ne, Measure.count_eq_zero_iff]; exact hU.ne_empty

/- English proof (translation)
Assemble the required witnesses or components as `⟨map_count_equiv (Equiv.inv H)⟩`.
-/
theorem count_isInv {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Countable H] : (Measure.count : Measure H).IsInvInvariant :=
  ⟨map_count_equiv (Equiv.inv H)⟩

/- English proof (translation)
Unfold `quotIntegral`. Distinguish the cases in `hρ : ∃ ρ, IsQuotNormaliser Γ μΓ ρ`. Rewrite using `[dif_pos hρ, dif_pos hρ]`. Establish `hρn` using `hρ.choose_spec`. Establish `: ν.IsMulRightInvariant` using `⟨fun g => by`.

Establish `h : (fun x => x * g) = (fun x => g * x)` using `funext fun x => hcomm x g`. Rewrite using `[h]`. Conclude with `map_mul_left_eq_self ν g⟩`. Establish `hρ' : IsQuotNormaliser Γ μΓ (fun t => hρ.choose (t * s⁻¹))`. Use `⟨hρn.1.comp (measurable_mul_const _), fun g => ?_⟩` and prove the remaining obligations.

Use `show ∫⁻ h, hρ.choose ((h : T) * g * s⁻¹) ∂μΓ = 1`. Simplify using `only [mul_assoc]`. Conclude with `hρn.2 _`. Establish `h1` using `integral_mul_right_eq_self (μ := ν) (fun t => F t * ((hρ.choose (t * s⁻¹)).toReal : ℂ)) s`. Simplify using `only [mul_inv_cancel_right] at h1`.

Rewrite using `[h1]`. Conclude with `hNE T ν Γ μΓ F _ _ hF hinv hρ' hρn`. Rewrite using `[dif_neg hρ, dif_neg hρ]`.
-/
theorem quotIntegral_mul_right (hNE : NormEq) {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [ν.IsHaarMeasure] (hcomm : ∀ s t : T, s * t = t * s) (Γ : Subgroup T) (μΓ : Measure Γ)
    [SFinite μΓ] [μΓ.IsInvInvariant] (F : T → ℂ) (hF : Measurable F) (hinv : ∀ g ∈ Γ, ∀ t, F (g * t) = F t)
    (s : T) : quotIntegral ν Γ μΓ (fun t => F (t * s)) = quotIntegral ν Γ μΓ F := by
  unfold quotIntegral
  by_cases hρ : ∃ ρ, IsQuotNormaliser Γ μΓ ρ
  · rw [dif_pos hρ, dif_pos hρ]
    have hρn := hρ.choose_spec
    have : ν.IsMulRightInvariant := ⟨fun g => by
      have h : (fun x => x * g) = (fun x => g * x) := funext fun x => hcomm x g
      rw [h]; exact map_mul_left_eq_self ν g⟩
    have hρ' : IsQuotNormaliser Γ μΓ (fun t => hρ.choose (t * s⁻¹)) := by
      refine ⟨hρn.1.comp (measurable_mul_const _), fun g => ?_⟩
      show ∫⁻ h, hρ.choose ((h : T) * g * s⁻¹) ∂μΓ = 1
      simp only [mul_assoc]
      exact hρn.2 _
    have h1 := integral_mul_right_eq_self (μ := ν) (fun t => F t * ((hρ.choose (t * s⁻¹)).toReal : ℂ)) s
    simp only [mul_inv_cancel_right] at h1
    rw [h1]
    exact hNE T ν Γ μΓ F _ _ hF hinv hρ' hρn
  · rw [dif_neg hρ, dif_neg hρ]

end PositivityTheory.Rg.BcB.CV.VolumeFunction

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.VolumeFunction

/- English proof (translation)
Introduce `hCS hRD hNE hQI hQA T _ _ _ _ _ _ _ _ ν _ Γ m a hcomm hdisc hac hadd hΓ hprop`. Use `hdisc` as an intermediate fact. Establish `: Countable Γ` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `hcl : IsClosed (Γ : Set T)` using `Subgroup.isClosed_of_discrete`. Establish `: (Measure.count : Measure Γ).IsHaarMeasure` using `count_isHaar`.

Establish `: (Measure.count : Measure Γ).IsInvInvariant` using `count_isInv`. Establish `hmeasF : ∀ y : (Fin m → SignType) → ℝ, Measurable fun t => (gam y (a t) : ℂ)` using `fun y => Complex.measurable_ofReal.comp (((hCS m).2.2.1 y).comp hac.measurable)`. Establish `hinv : ∀ y : (Fin m → SignType) → ℝ, ∀ g ∈ Γ, ∀ t, (gam y (a (g * t)) : ℂ) = (gam y (a t) : ℂ)`. Introduce `y g hg t`. Rewrite using `[hadd, hΓ g hg, zero_add]`.

Use `set K : ℝ := (Fintype.card (Finset (Fin m → SignType)) : ℝ) with hKdef`. Establish `hK0 : 0 ≤ K` using `Nat.cast_nonneg _`. Establish `key : ∀ M : ℝ, ∃ B : ℝ, ∀ y : (Fin m → SignType) → ℝ, (∀ e, |y e| ≤ M) → quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤ ∧ ‖quotIntegral ν Γ Measure.count (fun t => (gam y (a t) : ℂ))‖ ≤ B`. Introduce `M`. Take `⟨C, hC, hCm⟩` from `hprop (2 * M)`.

Take `⟨A, _, hA⟩` from `hQI T ν Γ Measure.count C hcl hC`. Use `⟨A * K, fun y hy => hA _ K hK0 (hmeasF y) (hinv y) ?_ ?_⟩` and prove the remaining obligations. Introduce `t ht`. Apply `hCm` to reduce the goal to its premises. Introduce `i`.

Conclude with `(hCS m).2.1 y M (a t) hy (fun h => ht (by rw [h, Complex.ofReal_zero])) i`. Introduce `x _`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Conclude with `gam_abs_le _ _`. Establish `hfin : ∀ y : (Fin m → SignType) → ℝ, quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤`.

Introduce `y`. Take `⟨B, hB⟩` from `key (∑ e, |y e|)`. Conclude with `(hB y fun e => Finset.single_le_sum (f := fun e => |y e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)).1`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hρ : ∃ ρ, IsQuotNormaliser Γ (Measure.count : Measure Γ) ρ`.

Simplify using `only [quotIntegral, dif_pos hρ]`. Establish `h2 : Measurable fun p : ((Fin m → SignType) → ℝ) × T => (p.1, a p.2)` using `measurable_fst.prodMk (hac.measurable.comp measurable_snd)`. Establish `hj : Measurable fun p : ((Fin m → SignType) → ℝ) × T => (gam p.1 (a p.2) : ℂ) * ((hρ.choose p.2).toReal : ℂ)` using `(Complex.measurable_ofReal.comp ((hRD.2 m).comp h2)).mul (Complex.measurable_ofReal.comp ((hρ.choose_spec.1.ennreal_toReal).comp measurable_snd))`. Conclude with `(hj.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable`. Simplify using `only [quotIntegral, dif_neg hρ]`.

Conclude with `measurable_const`. Introduce `M`. Take `⟨B, hB⟩` from `key M`. Conclude with `⟨B, fun y hy => (hB y hy).2⟩`. Introduce `y y' e s t h`.

Establish `hsub : ∀ u v : (Fin m → SignType) → ℝ, quotIntegral ν Γ Measure.count (fun x => (gam u (a x) : ℂ)) - quotIntegral ν Γ Measure.count (fun x => (gam v (a x) : ℂ)) = quotIntegral ν Γ Measure.count (fun x => ((gam u (a x) - gam v (a x) : ℝ) : ℂ))`. Introduce `u v`. Rewrite using `[← (hQA T ν Γ Measure.count).2.1 _ _ (hmeasF u) (hmeasF v) (hfin u) (hfin v)]`. Simplify using `only [Complex.ofReal_sub]`. Rewrite using `[hsub, hsub]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[(hCS m).2.2.2.2 y y' e s t (a x) h]`. Introduce `y s`. Establish `hrew : ∀ t, (gam (fun e => y e - sdot e (a s)) (a t) : ℂ) = (gam y (a (t * s)) : ℂ)`.

Introduce `t`. Establish `h` using `(hCS m).2.2.2.1 (fun e => y e - sdot e (a s)) (a t) (a s)`. Simplify using `only [sub_add_cancel] at h`. Rewrite using `[hadd, h]`. Simplify using `only [hrew]`.

Conclude with `quotIntegral_mul_right hNE ν hcomm Γ Measure.count _ (hmeasF y) (hinv y) s`.
-/
theorem pf_Vfun : PositivityTheory.Rg.BcB.ChainSum → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.CV.QInt →
    PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.Vfun := by
  intro hCS hRD hNE hQI hQA T _ _ _ _ _ _ _ _ ν _ Γ m a hcomm hdisc hac hadd hΓ hprop
  have := hdisc
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcl : IsClosed (Γ : Set T) := Subgroup.isClosed_of_discrete
  have : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaar
  have : (Measure.count : Measure Γ).IsInvInvariant := count_isInv
  have hmeasF : ∀ y : (Fin m → SignType) → ℝ, Measurable fun t => (gam y (a t) : ℂ) := fun y =>
    Complex.measurable_ofReal.comp (((hCS m).2.2.1 y).comp hac.measurable)
  have hinv : ∀ y : (Fin m → SignType) → ℝ, ∀ g ∈ Γ, ∀ t, (gam y (a (g * t)) : ℂ) = (gam y (a t) : ℂ) := by
    intro y g hg t
    rw [hadd, hΓ g hg, zero_add]
  set K : ℝ := (Fintype.card (Finset (Fin m → SignType)) : ℝ) with hKdef
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have key : ∀ M : ℝ, ∃ B : ℝ, ∀ y : (Fin m → SignType) → ℝ, (∀ e, |y e| ≤ M) →
      quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤ ∧
        ‖quotIntegral ν Γ Measure.count (fun t => (gam y (a t) : ℂ))‖ ≤ B := by
    intro M
    obtain ⟨C, hC, hCm⟩ := hprop (2 * M)
    obtain ⟨A, _, hA⟩ := hQI T ν Γ Measure.count C hcl hC
    refine ⟨A * K, fun y hy => hA _ K hK0 (hmeasF y) (hinv y) ?_ ?_⟩
    · intro t ht
      apply hCm
      intro i
      exact (hCS m).2.1 y M (a t) hy (fun h => ht (by rw [h, Complex.ofReal_zero])) i
    · intro x _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact gam_abs_le _ _
  have hfin : ∀ y : (Fin m → SignType) → ℝ,
      quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤ := by
    intro y
    obtain ⟨B, hB⟩ := key (∑ e, |y e|)
    exact (hB y fun e => Finset.single_le_sum (f := fun e => |y e|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ e)).1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · by_cases hρ : ∃ ρ, IsQuotNormaliser Γ (Measure.count : Measure Γ) ρ
    · simp only [quotIntegral, dif_pos hρ]
      have h2 : Measurable fun p : ((Fin m → SignType) → ℝ) × T => (p.1, a p.2) :=
        measurable_fst.prodMk (hac.measurable.comp measurable_snd)
      have hj : Measurable fun p : ((Fin m → SignType) → ℝ) × T =>
          (gam p.1 (a p.2) : ℂ) * ((hρ.choose p.2).toReal : ℂ) :=
        (Complex.measurable_ofReal.comp ((hRD.2 m).comp h2)).mul
          (Complex.measurable_ofReal.comp ((hρ.choose_spec.1.ennreal_toReal).comp measurable_snd))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    · simp only [quotIntegral, dif_neg hρ]
      exact measurable_const
  · intro M
    obtain ⟨B, hB⟩ := key M
    exact ⟨B, fun y hy => (hB y hy).2⟩
  · intro y y' e s t h
    have hsub : ∀ u v : (Fin m → SignType) → ℝ,
        quotIntegral ν Γ Measure.count (fun x => (gam u (a x) : ℂ)) -
          quotIntegral ν Γ Measure.count (fun x => (gam v (a x) : ℂ)) =
        quotIntegral ν Γ Measure.count (fun x => ((gam u (a x) - gam v (a x) : ℝ) : ℂ)) := by
      intro u v
      rw [← (hQA T ν Γ Measure.count).2.1 _ _ (hmeasF u) (hmeasF v) (hfin u) (hfin v)]
      simp only [Complex.ofReal_sub]
    rw [hsub, hsub]
    congr 1
    funext x
    rw [(hCS m).2.2.2.2 y y' e s t (a x) h]
  · intro y s
    have hrew : ∀ t, (gam (fun e => y e - sdot e (a s)) (a t) : ℂ) = (gam y (a (t * s)) : ℂ) := by
      intro t
      have h := (hCS m).2.2.2.1 (fun e => y e - sdot e (a s)) (a t) (a s)
      simp only [sub_add_cancel] at h
      rw [hadd, h]
    simp only [hrew]
    exact quotIntegral_mul_right hNE ν hcomm Γ Measure.count _ (hmeasF y) (hinv y) s

end PositivityTheory.Rg.BcB.CV

end
