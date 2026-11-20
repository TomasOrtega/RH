import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

/- English proof (translation)
Use `show Continuous fun x : GL (Fin n) ℂ => x⁻¹ * d * thetaR (starRingEnd ℂ) n x`. Conclude with `(continuous_inv.mul continuous_const).mul hθ`.
-/
theorem termof_twConj_cont {n : ℕ} (hθ : Continuous (thetaR (starRingEnd ℂ) n)) (d : GL (Fin n) ℂ) :
    Continuous fun x : GL (Fin n) ℂ => twConj (thetaR (starRingEnd ℂ) n) x d := by
  show Continuous fun x : GL (Fin n) ℂ => x⁻¹ * d * thetaR (starRingEnd ℂ) n x
  exact (continuous_inv.mul continuous_const).mul hθ

/- English proof (translation)
Establish `hK` using `(hEP a d₁ h₁ _ (hψ.isCompact.image continuous_fst)).prod (hEP b d₂ h₂ _ (hψ.isCompact.image continuous_snd))`. Use `HasCompactSupport.intro hK fun y hy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hy` to reduce the goal to its premises. Establish `hm : (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) ∈ tsupport ψ` using `subset_tsupport _ hne`.

Conclude with `⟨⟨_, hm, rfl⟩, ⟨_, hm, rfl⟩⟩`.
-/
theorem termof_hcs {a b : ℕ} (hEP : EllProper) (ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (hψ : HasCompactSupport ψ)
    (d₁ : GL (Fin a) ℂ) (d₂ : GL (Fin b) ℂ) (h₁ : EllC d₁) (h₂ : EllC d₂) :
    HasCompactSupport fun y : GL (Fin a) ℂ × GL (Fin b) ℂ =>
      ψ (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) := by
  have hK := (hEP a d₁ h₁ _ (hψ.isCompact.image continuous_fst)).prod
    (hEP b d₂ h₂ _ (hψ.isCompact.image continuous_snd))
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  apply hy
  have hm : (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) ∈ tsupport ψ :=
    subset_tsupport _ hne
  exact ⟨⟨_, hm, rfl⟩, ⟨_, hm, rfl⟩⟩

/- English proof (translation)
Introduce `hQS hHS hTopo hCI hKf hFL hFH hAE hCE hPE hEP`. Introduce `E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _`. Take `⟨⟨hlcA, hscA, ht2A⟩, ⟨hlcfA, hscfA, ht2fA⟩, ⟨hlcCA, hscCA⟩, hcntA, -, hθA⟩` from `hTopo E a`. Take `⟨⟨hlcB, hscB, ht2B⟩, ⟨hlcfB, hscfB, ht2fB⟩, ⟨hlcCB, hscCB⟩, hcntB, -, hθB⟩` from `hTopo E b`. Use `letI mB : MeasurableSpace (Gf E a b) := borel _`.

Use `haveI : BorelSpace (Gf E a b) := ⟨rfl⟩`. Take `⟨e, he⟩` from `hCI E a b`. Set `e' : (GA E a × GA E b) →* (Gi E a b × Gf E a b)` to `e.toMulEquiv.toMonoidHom`. Establish `he' : ∀ x, e' x = comps x` using `he`. Establish `hνH : (ν₁.prod ν₂).IsHaarMeasure` using `inferInstance`.

Establish `hνS : SigmaFinite (ν₁.prod ν₂)` using `inferInstance`. Establish `hαH : (Measure.pi fun _ : InfinitePlace E => ν₁.prod ν₂).IsHaarMeasure` using `inferInstance`. Set `α : Measure (Gi E a b)` to `Measure.pi fun _ => ν₁.prod ν₂`. Take `⟨β, hβ, hmap⟩` from `hHS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α e`. Use `haveI := hβ`.

Take `⟨hKo₁, hKc₁⟩` from `hKf E a`. Take `⟨hKo₂, hKc₂⟩` from `hKf E b`. Establish `hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `hKo₁.prod hKo₂`.

Establish `hKc : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `hKc₁.prod hKc₂`. Use `⟨(β.real (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.ofReal_ne_zero, measureReal_def, ENNReal.toReal_ne_zero]`.

Conclude with `⟨hKo.measure_ne_zero β ⟨1, Subgroup.one_mem _⟩, hKc.measure_lt_top.ne⟩`. Introduce `S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hLef hφ₁ hφ₂ d₁ d₂ hd₁ hd₂`. Take `⟨hP₁, hPv₁⟩` from `hPE E a u₁ hu₁ d₁`. Take `⟨hP₂, hPv₂⟩` from `hPE E b u₂ hu₂ d₂`. Establish `hCE'` using `hCE E a b u₁ u₂ hu₁ hu₂ d₁ d₂`.

Set `f : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ` to `fun v y => ψ v (twConj (thetaR (starRingEnd ℂ) a) y.1 (GeneralLinearGroup.map v.embedding d₁), twConj (thetaR (starRingEnd ℂ) b) y.2 (GeneralLinearGroup.map v.embedding d₂))`. Set `F₁ : Gi E a b → ℂ` to `fun y => ∏ v, f v (y v)`. Set `F₂ : Gf E a b → ℂ` to `orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)`. Establish `hfc : ∀ v, Continuous (f v)` using `fun v => (hLef v).1.comp (((termof_twConj_cont hθA _).comp continuous_fst).prodMk ((termof_twConj_cont hθB _).comp continuous_snd))`. Establish `hfs : ∀ v, HasCompactSupport (f v)` using `fun v => termof_hcs hEP (ψ v) (hLef v).2.1 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂)`.

Establish `hint : ∀ v, Integrable (f v) (ν₁.prod ν₂)` using `fun v => (hfc v).integrable_of_hasCompactSupport (hfs v)`. Establish `hF₁i : Integrable F₁ α` using `Integrable.fintype_prod hint`. Establish `hF₁m : Measurable F₁` using `(continuous_finset_prod _ fun v _ => (hfc v).comp (continuous_apply v)).measurable`. Use `haveI : Countable ↥((ratCent d₁).prod (ratCent d₂)) := by`. Establish `hsub : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) : Set (GA E a × GA E b)) ⊆ Set.range (fun p : GL (Fin a) E × GL (Fin b) E => (ratGL E a p.1, ratGL E b p.2))`.

Introduce `x hx`. Rewrite `hx` using `[SetLike.mem_coe, Subgroup.mem_prod]`. Take `⟨g₁, -, hg₁⟩` from `Subgroup.mem_map.1 hx.1`. Take `⟨g₂, -, hg₂⟩` from `Subgroup.mem_map.1 hx.2`. Conclude with `⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩`.

Conclude with `((Set.countable_range _).mono hsub).to_subtype`. Establish `hΓ : ((ratCent d₁).prod (ratCent d₂)).map ((MonoidHom.snd _ _).comp e') = gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)`. Use extensionality with `y`. Rewrite using `[Subgroup.mem_map, hCE'.1 y]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, hγ, rfl⟩`. Conclude with `⟨γ, hγ, (congrArg Prod.snd (he' γ)).symm⟩`. Introduce and unpack `⟨γ, hγ, rfl⟩`. Conclude with `⟨γ, hγ, congrArg Prod.snd (he' γ)⟩`. Establish `hinj : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), (e' γ).2 = 1 → γ = 1`.

Introduce `γ hγ h1`. Rewrite `h1` using `[he']`. Conclude with `(hCE'.2 γ hγ).1 h1`. Establish `hF₁inv : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), ∀ x, F₁ ((e' γ).1 * x) = F₁ x`. Introduce `γ hγ x`.

Establish `hc` using `(hCE'.2 γ hγ).2`. Rewrite using `[he']`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [f, Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]`. Rewrite using `[PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).1, PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).2]`.

Establish `hF₂inv : ∀ γ ∈ gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹), ∀ y, F₂ (γ * y) = F₂ y`. Introduce `γ hγ y`. Establish `h : γ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b γ` using `(Subgroup.mem_inf.1 hγ).2`. Simplify using `only [F₂, orbFn]`. Use `congr 1`.

Generalize the expression as in `(ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ at h ⊢`. Rewrite using `[(thP E a b).map_mul γ y, show (γ * y)⁻¹ * δ * (thP E a b γ * thP E a b y) = y⁻¹ * (γ⁻¹ * (δ * thP E a b γ)) * thP E a b y by group, ← h]`. Use `group`. Take `⟨U, hUo, hUinv⟩` from `hFL E hU a b S φ₁ φ₂ hφ₁ hφ₂`. Establish `hF₂U : ∀ u ∈ U, ∀ y, F₂ (y * u) = F₂ y`.

Introduce `u hu y`. Simplify using `only [F₂, orbFn]`. Rewrite using `[← hUinv u hu (y⁻¹ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b y)]`. Use `congr 1`. Generalize the expression as in `(ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ`.

Rewrite using `[(thP E a b).map_mul y u]`. Use `group`. Take `⟨hfin, hstab, hdc⟩` from `hFH E hU a b S hS φ₁ φ₂ hφ₁ hφ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (hP₁.1 hd₁) (hP₂.1 hd₂)`. Establish `hQ` using `hQS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α β e' (map_continuous e).measurable hmap ((ratCent d₁).prod (ratCent d₂)) (gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) ((Kf E a).prod (Kf E b)) U hΓ hinj hKo hKc hUo F₁ F₂ hF₁m hF₁i hF₁inv hF₂inv hF₂U hfin hstab`. Establish `hEq : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) d₁ d₂ = quotIntegral (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂)) Measure.count (fun x => F₁ (e' x).1 * F₂ (e' x).2)`.

Unfold `orbTerm2`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[hAE E a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ d₁ d₂ x, he' x]`. Establish `hI : ∫ x, F₁ x ∂α = ∏ v, (val v * starRingEnd ℂ (chAt (l₁ v) ((polE (d₁ * u₁⁻¹)).map v.embedding)) * starRingEnd ℂ (chAt (l₂ v) ((polE (d₂ * u₂⁻¹)).map v.embedding)))`.

Rewrite using `[integral_fintype_prod_eq_prod]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[(hLef v).2.2 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂), (hPv₁ v).1, (hPv₂ v).1]`. Rewrite using `[hEq, hQ, hI, hdc, Finset.prod_mul_distrib, Finset.prod_mul_distrib]`. Simplify using `only [chW]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem termOf_holds : TermOf := by
  intro hQS hHS hTopo hCI hKf hFL hFH hAE hCE hPE hEP
  intro E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨⟨hlcA, hscA, ht2A⟩, ⟨hlcfA, hscfA, ht2fA⟩, ⟨hlcCA, hscCA⟩, hcntA, -, hθA⟩ := hTopo E a
  obtain ⟨⟨hlcB, hscB, ht2B⟩, ⟨hlcfB, hscfB, ht2fB⟩, ⟨hlcCB, hscCB⟩, hcntB, -, hθB⟩ := hTopo E b
  letI mB : MeasurableSpace (Gf E a b) := borel _
  haveI : BorelSpace (Gf E a b) := ⟨rfl⟩
  obtain ⟨e, he⟩ := hCI E a b
  let e' : (GA E a × GA E b) →* (Gi E a b × Gf E a b) := e.toMulEquiv.toMonoidHom
  have he' : ∀ x, e' x = comps x := he
  have hνH : (ν₁.prod ν₂).IsHaarMeasure := inferInstance
  have hνS : SigmaFinite (ν₁.prod ν₂) := inferInstance
  have hαH : (Measure.pi fun _ : InfinitePlace E => ν₁.prod ν₂).IsHaarMeasure := inferInstance
  let α : Measure (Gi E a b) := Measure.pi fun _ => ν₁.prod ν₂
  obtain ⟨β, hβ, hmap⟩ := hHS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α e
  haveI := hβ
  obtain ⟨hKo₁, hKc₁⟩ := hKf E a
  obtain ⟨hKo₂, hKc₂⟩ := hKf E b
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKo₁.prod hKo₂
  have hKc : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKc₁.prod hKc₂
  refine ⟨(β.real (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_ne_zero, measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hKo.measure_ne_zero β ⟨1, Subgroup.one_mem _⟩, hKc.measure_lt_top.ne⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hLef hφ₁ hφ₂ d₁ d₂ hd₁ hd₂
  obtain ⟨hP₁, hPv₁⟩ := hPE E a u₁ hu₁ d₁
  obtain ⟨hP₂, hPv₂⟩ := hPE E b u₂ hu₂ d₂
  have hCE' := hCE E a b u₁ u₂ hu₁ hu₂ d₁ d₂
  let f : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ := fun v y =>
    ψ v (twConj (thetaR (starRingEnd ℂ) a) y.1 (GeneralLinearGroup.map v.embedding d₁),
      twConj (thetaR (starRingEnd ℂ) b) y.2 (GeneralLinearGroup.map v.embedding d₂))
  let F₁ : Gi E a b → ℂ := fun y => ∏ v, f v (y v)
  let F₂ : Gf E a b → ℂ := orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)
  have hfc : ∀ v, Continuous (f v) := fun v =>
    (hLef v).1.comp (((termof_twConj_cont hθA _).comp continuous_fst).prodMk
      ((termof_twConj_cont hθB _).comp continuous_snd))
  have hfs : ∀ v, HasCompactSupport (f v) := fun v =>
    termof_hcs hEP (ψ v) (hLef v).2.1 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂)
  have hint : ∀ v, Integrable (f v) (ν₁.prod ν₂) := fun v => (hfc v).integrable_of_hasCompactSupport (hfs v)
  have hF₁i : Integrable F₁ α := Integrable.fintype_prod hint
  have hF₁m : Measurable F₁ :=
    (continuous_finset_prod _ fun v _ => (hfc v).comp (continuous_apply v)).measurable
  haveI : Countable ↥((ratCent d₁).prod (ratCent d₂)) := by
    have hsub : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) : Set (GA E a × GA E b)) ⊆
        Set.range (fun p : GL (Fin a) E × GL (Fin b) E => (ratGL E a p.1, ratGL E b p.2)) := by
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_prod] at hx
      obtain ⟨g₁, -, hg₁⟩ := Subgroup.mem_map.1 hx.1
      obtain ⟨g₂, -, hg₂⟩ := Subgroup.mem_map.1 hx.2
      exact ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩
    exact ((Set.countable_range _).mono hsub).to_subtype
  have hΓ : ((ratCent d₁).prod (ratCent d₂)).map ((MonoidHom.snd _ _).comp e') = gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) := by
    ext y
    rw [Subgroup.mem_map, hCE'.1 y]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, (congrArg Prod.snd (he' γ)).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, congrArg Prod.snd (he' γ)⟩
  have hinj : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), (e' γ).2 = 1 → γ = 1 := by
    intro γ hγ h1
    rw [he'] at h1
    exact (hCE'.2 γ hγ).1 h1
  have hF₁inv : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), ∀ x, F₁ ((e' γ).1 * x) = F₁ x := by
    intro γ hγ x
    have hc := (hCE'.2 γ hγ).2
    rw [he']
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [f, Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]
    rw [PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).1, PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).2]
  have hF₂inv : ∀ γ ∈ gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹), ∀ y, F₂ (γ * y) = F₂ y := by
    intro γ hγ y
    have h : γ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) =
        (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b γ := (Subgroup.mem_inf.1 hγ).2
    simp only [F₂, orbFn]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ at h ⊢
    rw [(thP E a b).map_mul γ y, show (γ * y)⁻¹ * δ * (thP E a b γ * thP E a b y) =
      y⁻¹ * (γ⁻¹ * (δ * thP E a b γ)) * thP E a b y by group, ← h]
    group
  obtain ⟨U, hUo, hUinv⟩ := hFL E hU a b S φ₁ φ₂ hφ₁ hφ₂
  have hF₂U : ∀ u ∈ U, ∀ y, F₂ (y * u) = F₂ y := by
    intro u hu y
    simp only [F₂, orbFn]
    rw [← hUinv u hu (y⁻¹ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b y)]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ
    rw [(thP E a b).map_mul y u]
    group
  obtain ⟨hfin, hstab, hdc⟩ :=
    hFH E hU a b S hS φ₁ φ₂ hφ₁ hφ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (hP₁.1 hd₁) (hP₂.1 hd₂)
  have hQ := hQS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α β e' (map_continuous e).measurable hmap
    ((ratCent d₁).prod (ratCent d₂)) (gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) ((Kf E a).prod (Kf E b)) U hΓ hinj hKo hKc hUo
    F₁ F₂ hF₁m hF₁i hF₁inv hF₂inv hF₂U hfin hstab
  have hEq : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) d₁ d₂ = quotIntegral (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
      Measure.count (fun x => F₁ (e' x).1 * F₂ (e' x).2) := by
    unfold orbTerm2
    congr 1
    funext x
    rw [hAE E a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ d₁ d₂ x, he' x]
  have hI : ∫ x, F₁ x ∂α = ∏ v, (val v * starRingEnd ℂ (chAt (l₁ v) ((polE (d₁ * u₁⁻¹)).map v.embedding)) *
      starRingEnd ℂ (chAt (l₂ v) ((polE (d₂ * u₂⁻¹)).map v.embedding))) := by
    rw [integral_fintype_prod_eq_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hLef v).2.2 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂), (hPv₁ v).1, (hPv₂ v).1]
  rw [hEq, hQ, hI, hdc, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [chW]
  ring

end PositivityTheory.Rg.BcB.G8

end
