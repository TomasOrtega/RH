import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoMeas

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def RPAbs : Prop :=
  ∀ (ι : Type) [Countable ι] (W : ι → Type) [∀ i, MeasurableSpace (W i)]
    (m : ∀ i, Measure (W i)) [∀ i, SigmaFinite (m i)] (L : ∀ i, Set (W i)),
    (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ⊤) →
    (∀ S : Finset ι, ∃ c : ENNReal, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c) →
    ∃ ρ : Measure (∀ i, W i), SFinite ρ ∧
      ρ {x | ¬ ∀ᶠ i in Filter.cofinite, x i ∈ L i} = 0 ∧
      (∀ i (C : Set (W i)), MeasurableSet C → m i Cᶜ = 0 → ρ {x | x i ∉ C} = 0) ∧
      ∀ f : ∀ i, W i → ℂ, (∀ i, Integrable (f i) (m i)) →
        (∀ᶠ i in Filter.cofinite, f i = (L i).indicator 1) →
        Integrable (fun x => ∏ᶠ i, f i (x i)) ρ ∧
        HasProd (fun i => ∫ w, f i w ∂(m i)) (∫ x, ∏ᶠ i, f i (x i) ∂ρ)

def RPFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
      (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E)),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Ainf F) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
      (fib : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Fv F v) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Fv F v) σ (gramE σ J X0) hT))

def RPGlue : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (M a d : ℕ) (b : Module.Basis (Fin d) F E),
  ∃ Γ : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) →
      (Fin a → Fin M → AF F ⊗[F] E),
    Measurable Γ ∧ ∀ p, (∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v) →
      projInf (Γ p) = p.1 ∧ ∀ v, projV v (projFin (Γ p)) = p.2 v

def RPGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
  MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X ≠ T.map (inclR (AF F))} ∧
  MeasurableSet {X : Fin a → Fin M → Ainf F ⊗[F] E |
    gramR (Ainf F) σ J X = T.map (inclR (Ainf F))} ∧
  (∀ v : HeightOneSpectrum (𝓞 F), MeasurableSet {X : Fin a → Fin M → Fv F v ⊗[F] E |
    gramR (Fv F v) σ J X = T.map (inclR (Fv F v))}) ∧
  ∀ X : Fin a → Fin M → AF F ⊗[F] E, gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) →
    (∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) →
    gramR (AF F) σ J X = T.map (inclR (AF F))

def RPTail : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a →
      Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (d : ℕ) (b : Module.Basis (Fin d) F E),
    (∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) →
    (∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ →
      ∫ X, Φ X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} =>
        fibV v.1 (hermOf (Fv F v.1) σ (gramE σ J X0) hT) (latV b v.1)) c

def LatCofin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a M d d' : ℕ)
    (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E),
    ∀ᶠ v in Filter.cofinite, latV (M := M) (n := a) b v = latV b' v

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμi νinf hνi μv hμv νv hνv fibInf hfi fibV hfv hmult`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Establish `cF` using `hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet`. Take `⟨hsfI, hintI⟩` from `cF.1 μinf νinf fibInf hfi`. Establish `hFv` using `fun v => cF.2 v (μv v) (νv v) (fibV v) (hfv v)`.

Establish `hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ → Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))` using `fun v Φ h => (hFv v).2 Φ h.1.continuous h.2`. Set `b` to `Module.finBasis F E`. Break down `hTl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV _ b hSB (hmult _ b) with ⟨v0, hv0⟩ | hconv` into its components or cases. Use `⟨0, by simp, fun d' b' Φ Φinf Φf Φv _ _ hp _ => ⟨integrable_zero_measure, ?_⟩⟩` and prove the remaining obligations. Establish `h0 : HasProd (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) 0` using `hasProd_zero_of_exists_eq_zero ⟨v0, hv0 _ (hp.1 v0)⟩`.

Rewrite using `[integral_zero_measure, h0.tprod_eq, mul_zero]`. Set `W : HeightOneSpectrum (𝓞 F) → Type` to `fun v => Fin a → Fin M → Fv F v ⊗[F] E`. Set `m : ∀ v, Measure (W v)` to `fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)`. Establish `: ∀ v, SigmaFinite (m v)` using `fun v => (hFv v).1`. Use `hsfI` as an intermediate fact.

Establish `hLm : ∀ v, MeasurableSet (latV (M` using `M) (n := a) b v) := fun v => (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet`. Establish `hLf : ∀ v, m v (latV b v) ≠ ⊤` using `fun v => by`. Establish `h` using `hSB v _ (PositiveNearLattice.isSB_latV b v a M)`. Rewrite `h` using `[integrable_indicator_iff (hLm v)]`. Conclude with `(((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne`.

Take `⟨ρ, hρsf, hρgood, hρmarg, hρint⟩` from `hA (HeightOneSpectrum (𝓞 F)) W m (fun v => latV b v) hLm hLf hconv`. Use `hρsf` as an intermediate fact. Take `⟨Γ, hΓm, hΓ⟩` from `hG F E M a _ b`. Establish `cG` using `hGr F E σ M J a (gramE σ J X0)`. Set `P : Measure ((Fin a → Fin M → Ainf F ⊗[F] E) × ∀ v, W v)` to `(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)).prod ρ`.

Establish `hgood : P (Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) = 0`. Rewrite using `[Measure.prod_prod, hρgood, mul_zero]`. Use `⟨P.map Γ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hΓm cG.1]`. Establish `h1 : (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) {y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ = 0` using `measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) (hfi.1 _)`.

Establish `h2 : ∀ v, m v {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0` using `fun v => measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hfv v).1 _)`. Establish `hbad : Γ ⁻¹' {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} ⊆ ({y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ ×ˢ Set.univ) ∪ ((Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) ∪ ⋃ v, Set.univ ×ˢ {x : ∀ v, W v | x v ∉ {x | gr …`. Introduce `p hp`. Assume the negation of the conclusion as `hn`. Establish `hi : gramR (Ainf F) σ J p.1 = (gramE σ J X0).map (inclR (Ainf F))`.

Assume the negation of the conclusion as `h`. Conclude with `hn (Or.inl ⟨h, Set.mem_univ _⟩)`. Establish `hg : ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v`. Assume the negation of the conclusion as `h`. Conclude with `hn (Or.inr (Or.inl ⟨Set.mem_univ _, h⟩))`.

Establish `hv : ∀ v, gramR (Fv F v) σ J (p.2 v) = (gramE σ J X0).map (inclR (Fv F v))`. Introduce `v`. Assume the negation of the conclusion as `h`. Conclude with `hn (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_univ _, h⟩)))`. Take `⟨e1, e2⟩` from `hΓ p hg`.

Apply `hp` to reduce the goal to its premises. Apply `cG.2.2.2 (Γ p)` to reduce the goal to its premises. Rewrite using `[e1]`. Conclude with `hi`. Introduce `v`.

Rewrite using `[e2 v]`. Conclude with `hv v`. Use `measure_mono_null hbad (measure_union_null ?_ (measure_union_null hgood (measure_iUnion_null fun v => ?_)))` and prove the remaining obligations. Rewrite using `[Measure.prod_prod, h1, zero_mul]`. Rewrite using `[Measure.prod_prod, hρmarg v _ (cG.2.2.1 v) (h2 v), mul_zero]`.

Introduce `d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr`. Establish `hΦm : Measurable Φ` using `TopoMeas.measurable_adm Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩`. Establish `hf : ∀ v, Integrable (Φv v) (m v)` using `fun v => hSB v _ (hp.1 v)`. Establish `hfc : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1` using `(hp.2.1.and (hL F E a M d' _ b' b)).mono fun v h => h.1.trans (by rw [h.2])`. Take `⟨hIρ, hHP⟩` from `hρint Φv hf hfc`.

Establish `hae' : ∀ᵐ p ∂P, ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v`. Rewrite using `[ae_iff]`. Conclude with `measure_mono_null (fun p hp => Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩) hgood`. Establish `hae : (fun p => Φ (Γ p)) =ᵐ[P] fun p => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)` using `by filter_upwards [hae'] with p hp'`. Take `⟨e1, e2⟩` from `hΓ p hp'`.

Rewrite using `[hpr (Γ p), hp.2.2 (projFin (Γ p)), e1]`. Use `congr 1`. Conclude with `finprod_congr fun v => by rw [e2 v]`. Establish `hPI : Integrable (fun p : _ × (∀ v, W v) => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)) P` using `(hintI Φinf hc1 hc2).mul_prod hIρ`. Use `⟨(integrable_map_measure hΦm.aestronglyMeasurable hΓm.aemeasurable).2 (hPI.congr hae.symm), ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_map hΓm.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae, integral_prod_mul (fun y => Φinf y) (fun x : ∀ v, W v => ∏ᶠ v, Φv v (x v)), ← hHP.tprod_eq]`.
-/
theorem restrProd_of (hA : RPAbs) (hF : RPFib) (hG : RPGlue) (hGr : RPGram) (hTl : RPTail)
    (hL : LatCofin) : RestrProd := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμi νinf hνi μv hμv νv hνv
    fibInf hfi fibV hfv hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have cF := hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨hsfI, hintI⟩ := cF.1 μinf νinf fibInf hfi
  have hFv := fun v => cF.2 v (μv v) (νv v) (fibV v) (hfv v)
  have hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    fun v Φ h => (hFv v).2 Φ h.1.continuous h.2
  let b := Module.finBasis F E
  rcases hTl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV _ b hSB (hmult _ b) with
    ⟨v0, hv0⟩ | hconv
  · refine ⟨0, by simp, fun d' b' Φ Φinf Φf Φv _ _ hp _ => ⟨integrable_zero_measure, ?_⟩⟩
    have h0 : HasProd (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) 0 :=
      hasProd_zero_of_exists_eq_zero ⟨v0, hv0 _ (hp.1 v0)⟩
    rw [integral_zero_measure, h0.tprod_eq, mul_zero]
  · let W : HeightOneSpectrum (𝓞 F) → Type := fun v => Fin a → Fin M → Fv F v ⊗[F] E
    let m : ∀ v, Measure (W v) := fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)
    have : ∀ v, SigmaFinite (m v) := fun v => (hFv v).1
    have := hsfI
    have hLm : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
      (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
    have hLf : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
      have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
      rw [integrable_indicator_iff (hLm v)] at h
      exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
    obtain ⟨ρ, hρsf, hρgood, hρmarg, hρint⟩ :=
      hA (HeightOneSpectrum (𝓞 F)) W m (fun v => latV b v) hLm hLf hconv
    have := hρsf
    obtain ⟨Γ, hΓm, hΓ⟩ := hG F E M a _ b
    have cG := hGr F E σ M J a (gramE σ J X0)
    let P : Measure ((Fin a → Fin M → Ainf F ⊗[F] E) × ∀ v, W v) :=
      (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)).prod ρ
    have hgood : P (Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) = 0 := by
      rw [Measure.prod_prod, hρgood, mul_zero]
    refine ⟨P.map Γ, ?_, ?_⟩
    · rw [Measure.map_apply hΓm cG.1]
      have h1 : (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))
          {y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) (hfi.1 _)
      have h2 : ∀ v, m v {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        fun v => measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hfv v).1 _)
      have hbad : Γ ⁻¹' {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} ⊆
          ({y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ ×ˢ Set.univ) ∪
          ((Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) ∪
            ⋃ v, Set.univ ×ˢ {x : ∀ v, W v | x v ∉
              {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}}) := by
        intro p hp
        by_contra hn
        have hi : gramR (Ainf F) σ J p.1 = (gramE σ J X0).map (inclR (Ainf F)) := by
          by_contra h; exact hn (Or.inl ⟨h, Set.mem_univ _⟩)
        have hg : ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
          by_contra h; exact hn (Or.inr (Or.inl ⟨Set.mem_univ _, h⟩))
        have hv : ∀ v, gramR (Fv F v) σ J (p.2 v) = (gramE σ J X0).map (inclR (Fv F v)) := by
          intro v; by_contra h
          exact hn (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_univ _, h⟩)))
        obtain ⟨e1, e2⟩ := hΓ p hg
        apply hp
        apply cG.2.2.2 (Γ p)
        · rw [e1]; exact hi
        · intro v; rw [e2 v]; exact hv v
      refine measure_mono_null hbad (measure_union_null ?_ (measure_union_null hgood
        (measure_iUnion_null fun v => ?_)))
      · rw [Measure.prod_prod, h1, zero_mul]
      · rw [Measure.prod_prod, hρmarg v _ (cG.2.2.1 v) (h2 v), mul_zero]
    · intro d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr
      have hΦm : Measurable Φ :=
        TopoMeas.measurable_adm Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      have hf : ∀ v, Integrable (Φv v) (m v) := fun v => hSB v _ (hp.1 v)
      have hfc : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 :=
        (hp.2.1.and (hL F E a M d' _ b' b)).mono fun v h => h.1.trans (by rw [h.2])
      obtain ⟨hIρ, hHP⟩ := hρint Φv hf hfc
      have hae' : ∀ᵐ p ∂P, ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
        rw [ae_iff]
        exact measure_mono_null (fun p hp => Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩) hgood
      have hae : (fun p => Φ (Γ p)) =ᵐ[P] fun p => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v) := by
        filter_upwards [hae'] with p hp'
        obtain ⟨e1, e2⟩ := hΓ p hp'
        rw [hpr (Γ p), hp.2.2 (projFin (Γ p)), e1]
        congr 1
        exact finprod_congr fun v => by rw [e2 v]
      have hPI : Integrable (fun p : _ × (∀ v, W v) => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)) P :=
        (hintI Φinf hc1 hc2).mul_prod hIρ
      refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hΓm.aemeasurable).2
        (hPI.congr hae.symm), ?_⟩
      rw [integral_map hΓm.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae,
        integral_prod_mul (fun y => Φinf y) (fun x : ∀ v, W v => ∏ᶠ v, Φv v (x v)),
        ← hHP.tprod_eq]

end PI.VolStabSW
