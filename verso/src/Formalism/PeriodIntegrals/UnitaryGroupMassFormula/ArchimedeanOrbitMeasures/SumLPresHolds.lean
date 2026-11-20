import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge

def CayDensG : Prop := ∀ (n : ℕ) (ε : Fin n → Bool), GaugeDens ε →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ f₀ : gLie ε → ℝ, Measurable f₀ ∧ ContinuousAt f₀ 0 ∧ f₀ 0 = gaugeU ε ∧
      ∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x)

def sumL {n : ℕ} (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))) (hmh : m ⊔ h = gLie ε)
    {ι η : Type} [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ η →ₗ[ℝ] gLie ε where
  toFun p := ⟨(L₀ p.1 : EuclideanSpace ℝ _) + (L₁ p.2 : EuclideanSpace ℝ _), by
    rw [← hmh]; exact Submodule.add_mem_sup (L₀ p.1).2 (L₁ p.2).2⟩
  map_add' p q := by ext1; simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]; abel
  map_smul' c p := by ext1; simp [smul_add]

def SumLPres : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))
    (hmh : m ⊔ h = gLie ε), (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    Function.Injective (sumL ε m h hmh L₀ L₁) ∧
    ∀ S : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η), MeasurableSet S →
      MeasurableSet (sumL ε m h hmh L₀ L₁ '' S) ∧ ∀ g : gLie ε → ENNReal, Measurable g →
        ∫⁻ x in sumL ε m h hmh L₀ L₁ '' S, g x = ∫⁻ p in S, g (sumL ε m h hmh L₀ L₁ p)

/- English proof (translation)
Introduce `n ε m h hmh horth ι η _ _ L₀ L₁ hG`. Take `⟨r₀, hr₀, f₀, hm, hc, h0, hS⟩` from `hC n ε hG`. Take `⟨_, hPS⟩` from `hP n ε m h hmh horth ι η L₀ L₁`. Use `set F := sumL ε m h hmh L₀ L₁ with hF`. Establish `hFc : Continuous F` using `LinearMap.continuous_of_finiteDimensional F`.

Use `⟨r₀ / 2, by positivity, fun p => f₀ (F p), hc.comp_of_eq hFc.continuousAt (map_zero F), ?_, hm.comp hFc.measurable, ?_⟩` and prove the remaining obligations. Use `show f₀ (F 0) = gaugeU ε`. Rewrite using `[map_zero]`. Conclude with `h0`. Introduce `S hSb hSm`.

Take `⟨hFSm, hint⟩` from `hPS S hSm`. Establish `hsub : F '' S ⊆ ball (0 : gLie ε) r₀`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `hp'` using `hSb hp`. Rewrite `hp'`, the goal using `[mem_ball_zero_iff]`.

Establish `h1 : ‖p.1‖ < r₀ / 2` using `lt_of_le_of_lt (norm_fst_le p) hp'`. Establish `h2 : ‖p.2‖ < r₀ / 2` using `lt_of_le_of_lt (norm_snd_le p) hp'`. Establish `e : ‖F p‖ = ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖` using `rfl`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[show ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.1‖ from L₀.norm_map p.1, show ‖(L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.2‖ from L₁.norm_map p.2]`. Use `_ < r₀ := by linarith`. Establish `himg : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S = (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' (F '' S)` using `(Set.image_image (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) F S).symm`. Rewrite using `[himg, hS _ hsub hFSm, hint (fun x => ENNReal.ofReal (f₀ x)) (ENNReal.measurable_ofReal.comp hm)]`.
-/
theorem cayProdU_of (hC : CayDensG) (hP : SumLPres) : CayProdU := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁ hG
  obtain ⟨r₀, hr₀, f₀, hm, hc, h0, hS⟩ := hC n ε hG
  obtain ⟨_, hPS⟩ := hP n ε m h hmh horth ι η L₀ L₁
  set F := sumL ε m h hmh L₀ L₁ with hF
  have hFc : Continuous F := LinearMap.continuous_of_finiteDimensional F
  refine ⟨r₀ / 2, by positivity, fun p => f₀ (F p), hc.comp_of_eq hFc.continuousAt (map_zero F), ?_,
    hm.comp hFc.measurable, ?_⟩
  · show f₀ (F 0) = gaugeU ε
    rw [map_zero]
    exact h0
  · intro S hSb hSm
    obtain ⟨hFSm, hint⟩ := hPS S hSm
    have hsub : F '' S ⊆ ball (0 : gLie ε) r₀ := by
      rintro _ ⟨p, hp, rfl⟩
      have hp' := hSb hp
      rw [mem_ball_zero_iff] at hp' ⊢
      have h1 : ‖p.1‖ < r₀ / 2 := lt_of_le_of_lt (norm_fst_le p) hp'
      have h2 : ‖p.2‖ < r₀ / 2 := lt_of_le_of_lt (norm_snd_le p) hp'
      have e : ‖F p‖ = ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ := rfl
      rw [e]
      calc _ ≤ ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ +
            ‖(L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ := norm_add_le _ _
        _ = ‖p.1‖ + ‖p.2‖ := by
          rw [show ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.1‖ from L₀.norm_map p.1,
            show ‖(L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.2‖ from L₁.norm_map p.2]
        _ < r₀ := by linarith
    have himg : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S =
        (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' (F '' S) :=
      (Set.image_image (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) F S).symm
    rw [himg, hS _ hsub hFSm,
      hint (fun x => ENNReal.ofReal (f₀ x)) (ENNReal.measurable_ofReal.comp hm)]

/- English proof (translation)
Introduce `n ε m h hmh horth ι η _ _ L₀ L₁`. Establish `mkE : ∀ (κ : Type) [Fintype κ], ∃ e : EuclideanSpace ℝ κ ≃ᵐ (κ → ℝ), MeasurePreserving e ∧ ∀ x, e x = WithLp.ofLp x`. Introduce `κ _`. Use `⟨{ toEquiv := WithLp.equiv 2 (κ → ℝ) measurable_toFun := (PiLp.volume_preserving_ofLp κ).measurable measurable_invFun := ?_ }, ?_, fun x => rfl⟩` and prove the remaining obligations. Use `first`.

Consider the case `exact (PiLp.volume_preserving_toLp κ).measurable`. Consider the case `exact WithLp.measurable_toLp 2 _`. Consider the case `fun_prop`. Consider the case `measurability`. Conclude with `PiLp.volume_preserving_ofLp κ`.

Take `⟨eι, heι, heιa⟩` from `mkE ι`. Take `⟨eη, heη, heηa⟩` from `mkE η`. Take `⟨eS, heS, heSa⟩` from `mkE (ι ⊕ η)`. Establish `heSs : ∀ f, (eS.symm f).ofLp = f` using `fun f => by rw [← heSa, eS.apply_symm_apply]`. Set `φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ EuclideanSpace ℝ (ι ⊕ η)` to `(eι.prodCongr eη).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm.trans eS.symm)`.

Establish `hsum : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ))` using `by first`. Consider the case `exact MeasureTheory.measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ η => (volume : Measure ℝ))`. Consider the case `exact MeasureTheory.volume_measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)`. Consider the case `exact MeasureTheory.Measure.volume_preserving_sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)`. Consider the case `exact MeasureTheory.measurePreserving_sumPiEquivProdPi_of_measurePreserving`.

Establish `hφ : MeasurePreserving φ` using `((MeasurePreserving.symm _ heS).comp (MeasurePreserving.symm _ hsum)).comp (heι.prod heη)`. Establish `hφl : ∀ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ∀ i, (φ q).ofLp (Sum.inl i) = q.1.ofLp i`. Introduce `q i`. Use `show (eS.symm ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm (eι q.1, eη q.2))).ofLp (Sum.inl i) = _`. Rewrite using `[heSs, heιa]`.

Use `first`. Consider the case `rfl`. Consider the case `simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]`. Establish `hφr : ∀ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ∀ j, (φ q).ofLp (Sum.inr j) = q.2.ofLp j`. Introduce `q j`.

Use `show (eS.symm ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm (eι q.1, eη q.2))).ofLp (Sum.inr j) = _`. Rewrite using `[heSs, heηa]`. Use `first`. Consider the case `rfl`. Consider the case `simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]`.

Establish `hφl' : ∀ u : EuclideanSpace ℝ (ι ⊕ η), ∀ i, (φ.symm u).1.ofLp i = u.ofLp (Sum.inl i)`. Introduce `u i`. Rewrite using `[← hφl, φ.apply_symm_apply]`. Establish `hφr' : ∀ u : EuclideanSpace ℝ (ι ⊕ η), ∀ j, (φ.symm u).2.ofLp j = u.ofLp (Sum.inr j)`. Introduce `u j`.

Rewrite using `[← hφr, φ.apply_symm_apply]`. Establish `key : ∀ q, ‖(sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖φ q‖`. Introduce `q`. Establish `e0 : (sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = (L₀ q.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ q.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))` using `rfl`. Establish `horth'` using `horth _ (L₀ q.1).2 _ (L₁ q.2).2`.

Establish `e1` using `norm_add_sq_eq_norm_sq_add_norm_sq_real horth'`. Establish `n0 : ‖(L₀ q.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖q.1‖` using `L₀.norm_map q.1`. Establish `n1 : ‖(L₁ q.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖q.2‖` using `L₁.norm_map q.2`. Establish `e2 : ‖φ q‖ ^ 2 = ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2`. Rewrite using `[EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]`.

Simplify using `only [hφl, hφr]`. Establish `e3 : ‖(sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ ^ 2 = ‖φ q‖ ^ 2`. Rewrite using `[e2, e0, sq, e1, n0, n1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Real.sqrt_sq (norm_nonneg (sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))), ← Real.sqrt_sq (norm_nonneg (φ q)), e3]`.

Set `sp : EuclideanSpace ℝ (ι ⊕ η) →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η` to `{ toFun := φ.symm map_add' := fun u w => by`. Use extensionality with `k`. Simplify using `[hφl']`. Simplify using `[hφr']`. Use the proof step `map_smul' := fun c u => by`.

Use extensionality with `k`. Simplify using `[hφl']`. Simplify using `[hφr'] }`. Set `ψi : EuclideanSpace ℝ (ι ⊕ η) →ₗᵢ[ℝ] gLie ε` to `{ (sumL ε m h hmh L₀ L₁).comp sp with norm_map' := fun v => by show ‖(sumL ε m h hmh L₀ L₁ (φ.symm v) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖v‖`. Rewrite using `[key, φ.apply_symm_apply] }`.

Establish `hsurj : Function.Surjective ψi`. Introduce `x`. Establish `hx : (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ m ⊔ h`. Rewrite using `[hmh]`. Conclude with `x.2`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hx`. Use `⟨φ (L₀.symm ⟨a, ha⟩, L₁.symm ⟨b, hb⟩), ?_⟩` and prove the remaining obligations. Use `show sumL ε m h hmh L₀ L₁ (φ.symm (φ (L₀.symm ⟨a, ha⟩, L₁.symm ⟨b, hb⟩))) = x`. Rewrite using `[φ.symm_apply_apply]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show (L₀ (L₀.symm ⟨a, ha⟩) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ (L₁.symm ⟨b, hb⟩) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = x`. Rewrite using `[L₀.apply_symm_apply, L₁.apply_symm_apply]`. Conclude with `hab`. Set `ψ : EuclideanSpace ℝ (ι ⊕ η) ≃ₗᵢ[ℝ] gLie ε` to `LinearIsometryEquiv.ofSurjective ψi hsurj`. Establish `hψ : MeasurePreserving ψ` using `ψ.measurePreserving`.

Set `T : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ gLie ε` to `φ.trans ψ.toHomeomorph.toMeasurableEquiv`. Establish `hT : MeasurePreserving T` using `hψ.comp hφ`. Establish `hFT : ∀ q, sumL ε m h hmh L₀ L₁ q = T q`. Introduce `q`. Use `show sumL ε m h hmh L₀ L₁ q = sumL ε m h hmh L₀ L₁ (φ.symm (φ q))`.

Rewrite using `[φ.symm_apply_apply]`. Establish `hFT' : ⇑(sumL ε m h hmh L₀ L₁) = ⇑T` using `funext hFT`. Use `⟨?_, fun S hS => ⟨?_, fun g _ => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hFT']`. Conclude with `T.injective`.

Rewrite using `[hFT']`. Conclude with `T.measurableSet_image.mpr hS`. Rewrite using `[hFT']`. Conclude with `(hT.setLIntegral_comp_emb T.measurableEmbedding g S).symm`.
-/
theorem sumLPres_holds : SumLPres := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁

  have mkE : ∀ (κ : Type) [Fintype κ], ∃ e : EuclideanSpace ℝ κ ≃ᵐ (κ → ℝ),
      MeasurePreserving e ∧ ∀ x, e x = WithLp.ofLp x := by
    intro κ _
    refine ⟨{ toEquiv := WithLp.equiv 2 (κ → ℝ)
              measurable_toFun := (PiLp.volume_preserving_ofLp κ).measurable
              measurable_invFun := ?_ }, ?_, fun x => rfl⟩
    · first
      | exact (PiLp.volume_preserving_toLp κ).measurable
      | exact WithLp.measurable_toLp 2 _
      | fun_prop
      | measurability
    · exact PiLp.volume_preserving_ofLp κ
  obtain ⟨eι, heι, heιa⟩ := mkE ι
  obtain ⟨eη, heη, heηa⟩ := mkE η
  obtain ⟨eS, heS, heSa⟩ := mkE (ι ⊕ η)
  have heSs : ∀ f, (eS.symm f).ofLp = f := fun f => by rw [← heSa, eS.apply_symm_apply]
  let φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ EuclideanSpace ℝ (ι ⊕ η) :=
    (eι.prodCongr eη).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm.trans eS.symm)
  have hsum : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)) := by
    first
    | exact MeasureTheory.measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ η => (volume : Measure ℝ))
    | exact MeasureTheory.volume_measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)
    | exact MeasureTheory.Measure.volume_preserving_sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)
    | exact MeasureTheory.measurePreserving_sumPiEquivProdPi_of_measurePreserving
  have hφ : MeasurePreserving φ :=
    ((MeasurePreserving.symm _ heS).comp (MeasurePreserving.symm _ hsum)).comp (heι.prod heη)
  have hφl : ∀ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ∀ i, (φ q).ofLp (Sum.inl i) = q.1.ofLp i := by
    intro q i
    show (eS.symm ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm (eι q.1, eη q.2))).ofLp
      (Sum.inl i) = _
    rw [heSs, heιa]
    first
    | rfl
    | simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have hφr : ∀ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ∀ j, (φ q).ofLp (Sum.inr j) = q.2.ofLp j := by
    intro q j
    show (eS.symm ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm (eι q.1, eη q.2))).ofLp
      (Sum.inr j) = _
    rw [heSs, heηa]
    first
    | rfl
    | simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have hφl' : ∀ u : EuclideanSpace ℝ (ι ⊕ η), ∀ i, (φ.symm u).1.ofLp i = u.ofLp (Sum.inl i) := by
    intro u i
    rw [← hφl, φ.apply_symm_apply]
  have hφr' : ∀ u : EuclideanSpace ℝ (ι ⊕ η), ∀ j, (φ.symm u).2.ofLp j = u.ofLp (Sum.inr j) := by
    intro u j
    rw [← hφr, φ.apply_symm_apply]

  have key : ∀ q, ‖(sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖φ q‖ := by
    intro q
    have e0 : (sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool)) =
        (L₀ q.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ q.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := rfl
    have horth' := horth _ (L₀ q.1).2 _ (L₁ q.2).2
    have e1 := norm_add_sq_eq_norm_sq_add_norm_sq_real horth'
    have n0 : ‖(L₀ q.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖q.1‖ := L₀.norm_map q.1
    have n1 : ‖(L₁ q.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖q.2‖ := L₁.norm_map q.2
    have e2 : ‖φ q‖ ^ 2 = ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_sum_type]
      simp only [hφl, hφr]
    have e3 : ‖(sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ ^ 2 =
        ‖φ q‖ ^ 2 := by
      rw [e2, e0, sq, e1, n0, n1]
      ring
    rw [← Real.sqrt_sq (norm_nonneg (sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))),
      ← Real.sqrt_sq (norm_nonneg (φ q)), e3]

  let sp : EuclideanSpace ℝ (ι ⊕ η) →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
    { toFun := φ.symm
      map_add' := fun u w => by
        ext k
        · simp [hφl']
        · simp [hφr']
      map_smul' := fun c u => by
        ext k
        · simp [hφl']
        · simp [hφr'] }
  let ψi : EuclideanSpace ℝ (ι ⊕ η) →ₗᵢ[ℝ] gLie ε :=
    { (sumL ε m h hmh L₀ L₁).comp sp with
      norm_map' := fun v => by
        show ‖(sumL ε m h hmh L₀ L₁ (φ.symm v) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖v‖
        rw [key, φ.apply_symm_apply] }
  have hsurj : Function.Surjective ψi := by
    intro x
    have hx : (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ m ⊔ h := by
      rw [hmh]
      exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    refine ⟨φ (L₀.symm ⟨a, ha⟩, L₁.symm ⟨b, hb⟩), ?_⟩
    show sumL ε m h hmh L₀ L₁ (φ.symm (φ (L₀.symm ⟨a, ha⟩, L₁.symm ⟨b, hb⟩))) = x
    rw [φ.symm_apply_apply]
    apply Subtype.ext
    show (L₀ (L₀.symm ⟨a, ha⟩) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
      (L₁ (L₁.symm ⟨b, hb⟩) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = x
    rw [L₀.apply_symm_apply, L₁.apply_symm_apply]
    exact hab
  let ψ : EuclideanSpace ℝ (ι ⊕ η) ≃ₗᵢ[ℝ] gLie ε := LinearIsometryEquiv.ofSurjective ψi hsurj
  have hψ : MeasurePreserving ψ := ψ.measurePreserving
  let T : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ gLie ε :=
    φ.trans ψ.toHomeomorph.toMeasurableEquiv
  have hT : MeasurePreserving T := hψ.comp hφ
  have hFT : ∀ q, sumL ε m h hmh L₀ L₁ q = T q := by
    intro q
    show sumL ε m h hmh L₀ L₁ q = sumL ε m h hmh L₀ L₁ (φ.symm (φ q))
    rw [φ.symm_apply_apply]
  have hFT' : ⇑(sumL ε m h hmh L₀ L₁) = ⇑T := funext hFT
  refine ⟨?_, fun S hS => ⟨?_, fun g _ => ?_⟩⟩
  · rw [hFT']
    exact T.injective
  · rw [hFT']
    exact T.measurableSet_image.mpr hS
  · rw [hFT']
    exact (hT.setLIntegral_comp_emb T.measurableEmbedding g S).symm

/- English proof (translation)
The claim follows from `cayProdU_of hC sumLPres_holds`.
-/
theorem cayProdU_of_G (hC : CayDensG) : CayProdU := cayProdU_of hC sumLPres_holds

def CayDensEx : Prop := ∀ (n : ℕ) (ε : Fin n → Bool),
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ f₀ : gLie ε → ℝ, Measurable f₀ ∧ ContinuousAt f₀ 0 ∧
      ∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x)

def CayValId : Prop := ∀ (n : ℕ) (ε : Fin n → Bool), GaugeDens ε → ∀ r₀ : ℝ, 0 < r₀ → ∀ f₀ : gLie ε → ℝ,
    Measurable f₀ → ContinuousAt f₀ 0 →
    (∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x)) → f₀ 0 = gaugeU ε

/- English proof (translation)
Introduce `n ε hG`. Take `⟨r₀, hr₀, f₀, hm, hc, hS⟩` from `h1 n ε`. Conclude with `⟨r₀, hr₀, f₀, hm, hc, h2 n ε hG r₀ hr₀ f₀ hm hc hS, hS⟩`.
-/
theorem cayDensG_of (h1 : CayDensEx) (h2 : CayValId) : CayDensG := by
  intro n ε hG
  obtain ⟨r₀, hr₀, f₀, hm, hc, hS⟩ := h1 n ε
  exact ⟨r₀, hr₀, f₀, hm, hc, h2 n ε hG r₀ hr₀ f₀ hm hc hS, hS⟩

end PI.AprimeInfW
