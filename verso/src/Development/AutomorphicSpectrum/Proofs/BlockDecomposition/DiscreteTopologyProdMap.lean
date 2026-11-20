import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelNeTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMahlerBound

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Function
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TwUnfold

/- English proof (translation)
Establish `hr : ∀ x, TwConjugate θ x x` using `fun x => ⟨1, by simp [twConj]⟩`. Establish `hs : ∀ {x y}, TwConjugate θ x y → TwConjugate θ y x`. Introduce and unpack `x y ⟨g, rfl⟩`. Use `⟨g⁻¹, ?_⟩` and prove the remaining obligations. Simplify using `only [twConj, map_inv, inv_inv]`.

Use `group`. Establish `ht : ∀ {x y z}, TwConjugate θ x y → TwConjugate θ y z → TwConjugate θ x z`. Introduce and unpack `x y z ⟨g, rfl⟩ ⟨h, rfl⟩`. Use `⟨g * h, ?_⟩` and prove the remaining obligations. Simplify using `only [twConj, map_mul]`.

Use `group`. Establish `he : Equivalence (TwConjugate θ)` using `⟨hr, hs, ht⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : Quot.mk (TwConjugate θ) (Quot.out c) = Quot.mk _ d` using `by rw [Quot.out_eq, h]`.

Conclude with `he.eqvGen_iff.1 (Quot.eqvGen_exact h1)`. Introduce `h`. Rewrite using `[← Quot.sound h, Quot.out_eq]`.
-/
theorem mk_eq_iff_twConjugate {R : Type*} [Group R] (θ : Monoid.End R) (c : Quot (TwConjugate θ)) (d : R) :
    Quot.mk _ d = c ↔ TwConjugate θ (Quot.out c) d := by
  have hr : ∀ x, TwConjugate θ x x := fun x => ⟨1, by simp [twConj]⟩
  have hs : ∀ {x y}, TwConjugate θ x y → TwConjugate θ y x := by
    rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp only [twConj, map_inv, inv_inv]
    group
  have ht : ∀ {x y z}, TwConjugate θ x y → TwConjugate θ y z → TwConjugate θ x z := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    simp only [twConj, map_mul]
    group
  have he : Equivalence (TwConjugate θ) := ⟨hr, hs, ht⟩
  constructor
  · intro h
    have h1 : Quot.mk (TwConjugate θ) (Quot.out c) = Quot.mk _ d := by rw [Quot.out_eq, h]
    exact he.eqvGen_iff.1 (Quot.eqvGen_exact h1)
  · intro h
    rw [← Quot.sound h, Quot.out_eq]

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Rewrite using `[thetaR_val, ← map_inv]`. Conclude with `conjAd_algebraMap _`.
-/
theorem thetaA_ratGL (n : ℕ) (d : GL (Fin n) E) : thetaA E n (ratGL E n d) = ratGL E n (thetaE E n d) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaR_val, ← map_inv]
  exact conjAd_algebraMap _

/- English proof (translation)
Use `haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := a)`. Use `haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := b)`. Set `f : ((ratGL E a).prodMap (ratGL E b)).range → (ratGL E a).range × (ratGL E b).range` to `fun z => (⟨z.1.1, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.1, congrArg Prod.fst hw⟩⟩, ⟨z.1.2, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.2, congrArg Prod.snd hw⟩⟩)`. Establish `hf : Continuous f`. Use `Continuous.prodMk ?_ ?_` and prove the remaining obligations.

Conclude with `(continuous_fst.comp continuous_subtype_val).subtype_mk _`. Conclude with `(continuous_snd.comp continuous_subtype_val).subtype_mk _`. Establish `hi : Injective f`. Introduce `z w h`. Use `Subtype.ext (Prod.ext ?_ ?_)` and prove the remaining obligations.

Conclude with `congrArg (fun p => (p.1 : GA E a)) h`. Conclude with `congrArg (fun p => (p.2 : GA E b)) h`. Conclude with `DiscreteTopology.of_continuous_injective hf hi`.
-/
theorem discreteTopology_prodMap : DiscreteTopology ((ratGL E a).prodMap (ratGL E b)).range := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := a)
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := b)
  let f : ((ratGL E a).prodMap (ratGL E b)).range → (ratGL E a).range × (ratGL E b).range := fun z =>
    (⟨z.1.1, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.1, congrArg Prod.fst hw⟩⟩,
     ⟨z.1.2, by obtain ⟨w, hw⟩ := z.2; exact ⟨w.2, congrArg Prod.snd hw⟩⟩)
  have hf : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hi : Injective f := by
    intro z w h
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun p => (p.1 : GA E a)) h
    · exact congrArg (fun p => (p.2 : GA E b)) h
  exact DiscreteTopology.of_continuous_injective hf hi

/- English proof (translation)
Establish `hθ₁` using `GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := a)`. Establish `hθ₂` using `GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := b)`. Establish `hL₁ : IsCompact (Prod.fst '' L)` using `hL.image continuous_fst`. Establish `hL₂ : IsCompact (Prod.snd '' L)` using `hL.image continuous_snd`. Establish `hS₁ : IsCompact (Prod.fst '' tsupport φ)` using `IsCompact.image hφ continuous_fst`.

Establish `hS₂ : IsCompact (Prod.snd '' tsupport φ)` using `IsCompact.image hφ continuous_snd`. Establish `hK₁` using `(hL₁.mul hS₁).mul (hL₁.image hθ₁).inv`. Establish `hK₂` using `(hL₂.mul hS₂).mul (hL₂.image hθ₂).inv`. Use `((GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₁).prod (GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₂)).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨d₁, d₂⟩ ⟨x, hx, h⟩`.

Establish `hs` using `subset_tsupport _ h`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `ratGL E a d₁ ∈ Prod.fst '' L * Prod.fst '' tsupport φ * (thetaA E a '' (Prod.fst '' L))⁻¹`. Establish `hd : ratGL E a d₁ = x.1 * twConj (thetaA E a) x.1 (ratGL E a d₁) * (thetaA E a x.1)⁻¹`. Simplify using `only [twConj]`.

Use `group`. Rewrite using `[hd]`. Conclude with `Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩) (Set.inv_mem_inv.2 ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)`. Express the relevant statement in the definitionally equal form `ratGL E b d₂ ∈ Prod.snd '' L * Prod.snd '' tsupport φ * (thetaA E b '' (Prod.snd '' L))⁻¹`. Establish `hd : ratGL E b d₂ = x.2 * twConj (thetaA E b) x.2 (ratGL E b d₂) * (thetaA E b x.2)⁻¹`.

Simplify using `only [twConj]`. Use `group`. Rewrite using `[hd]`. Conclude with `Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩) (Set.inv_mem_inv.2 ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩)`.
-/
theorem finite_pair {φ : GA E a × GA E b → ℂ} (hφ : HasCompactSupport φ) {L : Set (GA E a × GA E b)} (hL : IsCompact L) :
    {d : GL (Fin a) E × GL (Fin b) E | ∃ x ∈ L,
      φ (twConj (thetaA E a) x.1 (ratGL E a d.1), twConj (thetaA E b) x.2 (ratGL E b d.2)) ≠ 0}.Finite := by
  have hθ₁ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := a)
  have hθ₂ := GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA (E := E) (n := b)
  have hL₁ : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  have hL₂ : IsCompact (Prod.snd '' L) := hL.image continuous_snd
  have hS₁ : IsCompact (Prod.fst '' tsupport φ) := IsCompact.image hφ continuous_fst
  have hS₂ : IsCompact (Prod.snd '' tsupport φ) := IsCompact.image hφ continuous_snd
  have hK₁ := (hL₁.mul hS₁).mul (hL₁.image hθ₁).inv
  have hK₂ := (hL₂.mul hS₂).mul (hL₂.image hθ₂).inv
  refine ((GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₁).prod (GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hK₂)).subset ?_
  rintro ⟨d₁, d₂⟩ ⟨x, hx, h⟩
  have hs := subset_tsupport _ h
  constructor
  · change ratGL E a d₁ ∈ Prod.fst '' L * Prod.fst '' tsupport φ * (thetaA E a '' (Prod.fst '' L))⁻¹
    have hd : ratGL E a d₁ = x.1 * twConj (thetaA E a) x.1 (ratGL E a d₁) * (thetaA E a x.1)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩)
  · change ratGL E b d₂ ∈ Prod.snd '' L * Prod.snd '' tsupport φ * (thetaA E b '' (Prod.snd '' L))⁻¹
    have hd : ratGL E b d₂ = x.2 * twConj (thetaA E b) x.2 (ratGL E b d₂) * (thetaA E b x.2)⁻¹ := by
      simp only [twConj]
      group
    rw [hd]
    exact Set.mul_mem_mul (Set.mul_mem_mul ⟨x, hx, rfl⟩ ⟨_, hs, rfl⟩)
      (Set.inv_mem_inv.2 ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩)

/- English proof (translation)
Apply the tactic sequence `by_cases h : x ∈ cutSet E n τ <;> simp [chiT, h]`.
-/
theorem chiT_norm_le (τ : ℝ) {n : ℕ} (x : GA E n) : ‖(chiT τ x : ℂ)‖ ≤ 1 := by
  by_cases h : x ∈ cutSet E n τ <;> simp [chiT, h]

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Conclude with `h (by simp [chiT, hx])`.
-/
theorem mem_cutSet_of_chiT_ne_zero {τ : ℝ} {n : ℕ} {x : GA E n} (h : (chiT τ x : ℂ) ≠ 0) : x ∈ cutSet E n τ := by
  by_contra hx
  exact h (by simp [chiT, hx])

end Adelic

/- English proof (translation)
Introduce `E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ τ r φ hF₁ hF₂ hφ`. Use `haveI := CuspidalL2GL.locallyCompactSpace_GA E a`. Use `haveI := CuspidalL2GL.locallyCompactSpace_GA E b`. Use `haveI := CuspidalL2GL.secondCountableTopology_GA E a`. Use `haveI := CuspidalL2GL.secondCountableTopology_GA E b`.

Use `haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite`. Use `haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite`. Take `⟨hc₁, hi₁, C₁, hC₁, hs₁⟩` from `hM E a τ`. Take `⟨hc₂, hi₂, C₂, hC₂, hs₂⟩` from `hM E b τ`. Set `ι : GL (Fin a) E × GL (Fin b) E →* GA E a × GA E b` to `(ratGL E a).prodMap (ratGL E b)`.

Set `θ : Monoid.End (GA E a × GA E b)` to `(thetaA E a).prodMap (thetaA E b)`. Set `θR : Monoid.End (GL (Fin a) E × GL (Fin b) E)` to `(thetaE E a).prodMap (thetaE E b)`. Use `haveI : DiscreteTopology ι.range := discreteTopology_prodMap`. Use `haveI : Countable ι.range := by haveI : SecondCountableTopology ι.range := inferInstance`. Conclude with `(TopologicalSpace.separableSpace_iff_countable).1 inferInstance`.

Establish `hι : Injective ι` using `GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL.prodMap GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL`. Use `haveI : Countable (GL (Fin a) E × GL (Fin b) E) := Injective.countable (f := ι.rangeRestrict) (fun x y h => hι (congrArg Subtype.val h))`. Establish `hθ : ∀ r, ι (θR r) = θ (ι r)` using `fun r => Prod.ext (thetaA_ratGL a r.1).symm (thetaA_ratGL b r.2).symm`. Establish `hFd : IsFundamentalDomain ι.range (F₁ ×ˢ F₂) (μ₁.prod μ₂)` using `GlobalTheory.CompanionTheory.PairDom.isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ hF₁ hF₂`. Set `cls : GL (Fin a) E × GL (Fin b) E → TwClass E a × TwClass E b` to `fun d => (Quot.mk _ d.1, Quot.mk _ d.2)`.

Set `rep : TwClass E a × TwClass E b → GL (Fin a) E × GL (Fin b) E` to `fun c => (Quot.out c.1, Quot.out c.2)`. Establish `hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d`. Introduce and unpack `⟨c₁, c₂⟩ ⟨d₁, d₂⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨g₁, h₁⟩` from `(mk_eq_iff_twConjugate _ c₁ d₁).1 (congrArg Prod.fst h)`. Take `⟨g₂, h₂⟩` from `(mk_eq_iff_twConjugate _ c₂ d₂).1 (congrArg Prod.snd h)`. Conclude with `⟨(g₁, g₂), Prod.ext h₁ h₂⟩`. Introduce and unpack `⟨g, hg⟩`. Conclude with `Prod.ext ((mk_eq_iff_twConjugate _ c₁ d₁).2 ⟨g.1, congrArg Prod.fst hg⟩) ((mk_eq_iff_twConjugate _ c₂ d₂).2 ⟨g.2, congrArg Prod.snd hg⟩)`.

Set `H : TwClass E a × TwClass E b → Subgroup (GA E a × GA E b)` to `fun c => (ratCent (Quot.out c.1)).prod (ratCent (Quot.out c.2))`. Establish `hH : ∀ c g, g ∈ H c ↔ ∃ t, ι t = g ∧ twConj θR t (rep c) = rep c`. Introduce and unpack `c ⟨g₁, g₂⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨t₁, h₁, rfl⟩, ⟨t₂, h₂, rfl⟩⟩`.

Conclude with `⟨(t₁, t₂), rfl, Prod.ext h₁ h₂⟩`. Introduce and unpack `⟨t, ht, hc⟩`. Conclude with `⟨⟨t.1, congrArg Prod.fst hc, congrArg Prod.fst ht⟩, ⟨t.2, congrArg Prod.snd hc, congrArg Prod.snd ht⟩⟩`. Establish `hmχ : ∀ (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)], IsClosed (cutSet E n τ) → Measurable (chiT τ : GA E n → ℂ)` using `fun n _ _ h => measurable_one.indicator h.measurableSet`. Establish `hχm : Measurable fun x : GA E a × GA E b => (chiT τ x.1 * chiT τ x.2 : ℂ)` using `((hmχ a hc₁).comp measurable_fst).mul ((hmχ b hc₂).comp measurable_snd)`.

Establish `hχb : ∀ x : GA E a × GA E b, ‖(chiT τ x.1 * chiT τ x.2 : ℂ)‖ ≤ 1` using `fun x => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (chiT_norm_le τ _) (norm_nonneg _) (chiT_norm_le τ _)`. Establish `hinv : ∀ (n : ℕ), (∀ g x, ratGL E n g * x ∈ cutSet E n τ ↔ x ∈ cutSet E n τ) → ∀ g (x : GA E n), (chiT τ (ratGL E n g * x) : ℂ) = chiT τ x` using `fun n h g x => by`. Distinguish the cases in `hx : x ∈ cutSet E n τ`.

Simplify using `[chiT, hx, (h g x).2 hx]`. Simplify using `[chiT, hx, mt (h g x).1 hx]`. Establish `hχi : ∀ (r : GL (Fin a) E × GL (Fin b) E) (x : GA E a × GA E b), (chiT τ (ι r * x).1 * chiT τ (ι r * x).2 : ℂ) = chiT τ x.1 * chiT τ x.2` using `fun r x => by`. Express the relevant statement in the definitionally equal form `(chiT τ (ratGL E a r.1 * x.1) * chiT τ (ratGL E b r.2 * x.2) : ℂ) = _`. Rewrite using `[hinv a hi₁, hinv b hi₂]`.

Establish `hχK : ∀ x : GA E a × GA E b, (chiT τ x.1 * chiT τ x.2 : ℂ) ≠ 0 → ∃ r, ∃ k ∈ C₁ ×ˢ C₂, x = ι r * k`. Introduce `x hx`. Take `⟨_, ⟨r₁, rfl⟩, k₁, hk₁, e₁⟩` from `Set.mem_mul.1 (hs₁ (mem_cutSet_of_chiT_ne_zero (left_ne_zero_of_mul hx)))`. Take `⟨_, ⟨r₂, rfl⟩, k₂, hk₂, e₂⟩` from `Set.mem_mul.1 (hs₂ (mem_cutSet_of_chiT_ne_zero (right_ne_zero_of_mul hx)))`. Conclude with `⟨(r₁, r₂), (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁.symm e₂.symm⟩`.

Establish `hθc : Continuous θ` using `(GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_fst).prodMk (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_snd)`. Establish `hφm : ∀ d, Measurable fun x => φ (twConj θ x (ι d))` using `fun d => (hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθc)).measurable`. Take `⟨B, hB⟩` from `hφ.supp.exists_bound_of_continuous hφ.cont`. Establish `key` using `unfold_abs (μ := μ₁.prod μ₂) (ι := ι) (θ := θ) (θR := θR) (cls := cls) (rep := rep) (H := H) (χ := fun x => chiT τ x.1 * chiT τ x.2) (φ := φ) hι hθ hFd hcls hH hχm hχb hχi (hC₁.prod hC₂) hχK hφm hB (fun L hL => finite_pair hφ.supp hL)`. Conclude with `key`.
-/
theorem unfold2_of (hM : Mahler) : Unfold2 := by
  intro E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ τ r φ hF₁ hF₂ hφ
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨hc₁, hi₁, C₁, hC₁, hs₁⟩ := hM E a τ
  obtain ⟨hc₂, hi₂, C₂, hC₂, hs₂⟩ := hM E b τ
  let ι : GL (Fin a) E × GL (Fin b) E →* GA E a × GA E b := (ratGL E a).prodMap (ratGL E b)
  let θ : Monoid.End (GA E a × GA E b) := (thetaA E a).prodMap (thetaA E b)
  let θR : Monoid.End (GL (Fin a) E × GL (Fin b) E) := (thetaE E a).prodMap (thetaE E b)
  haveI : DiscreteTopology ι.range := discreteTopology_prodMap
  haveI : Countable ι.range := by
    haveI : SecondCountableTopology ι.range := inferInstance
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  have hι : Injective ι :=
    GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL.prodMap GlobalTheory.CompanionTheory.KerTwFin.injective_ratGL
  haveI : Countable (GL (Fin a) E × GL (Fin b) E) :=
    Injective.countable (f := ι.rangeRestrict) (fun x y h => hι (congrArg Subtype.val h))
  have hθ : ∀ r, ι (θR r) = θ (ι r) := fun r => Prod.ext (thetaA_ratGL a r.1).symm (thetaA_ratGL b r.2).symm
  have hFd : IsFundamentalDomain ι.range (F₁ ×ˢ F₂) (μ₁.prod μ₂) :=
    GlobalTheory.CompanionTheory.PairDom.isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ hF₁ hF₂
  let cls : GL (Fin a) E × GL (Fin b) E → TwClass E a × TwClass E b := fun d => (Quot.mk _ d.1, Quot.mk _ d.2)
  let rep : TwClass E a × TwClass E b → GL (Fin a) E × GL (Fin b) E := fun c => (Quot.out c.1, Quot.out c.2)
  have hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d := by
    rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩
    constructor
    · intro h
      obtain ⟨g₁, h₁⟩ := (mk_eq_iff_twConjugate _ c₁ d₁).1 (congrArg Prod.fst h)
      obtain ⟨g₂, h₂⟩ := (mk_eq_iff_twConjugate _ c₂ d₂).1 (congrArg Prod.snd h)
      exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩
    · rintro ⟨g, hg⟩
      exact Prod.ext ((mk_eq_iff_twConjugate _ c₁ d₁).2 ⟨g.1, congrArg Prod.fst hg⟩)
        ((mk_eq_iff_twConjugate _ c₂ d₂).2 ⟨g.2, congrArg Prod.snd hg⟩)
  let H : TwClass E a × TwClass E b → Subgroup (GA E a × GA E b) := fun c =>
    (ratCent (Quot.out c.1)).prod (ratCent (Quot.out c.2))
  have hH : ∀ c g, g ∈ H c ↔ ∃ t, ι t = g ∧ twConj θR t (rep c) = rep c := by
    rintro c ⟨g₁, g₂⟩
    constructor
    · rintro ⟨⟨t₁, h₁, rfl⟩, ⟨t₂, h₂, rfl⟩⟩
      exact ⟨(t₁, t₂), rfl, Prod.ext h₁ h₂⟩
    · rintro ⟨t, ht, hc⟩
      exact ⟨⟨t.1, congrArg Prod.fst hc, congrArg Prod.fst ht⟩, ⟨t.2, congrArg Prod.snd hc, congrArg Prod.snd ht⟩⟩
  have hmχ : ∀ (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)], IsClosed (cutSet E n τ) →
      Measurable (chiT τ : GA E n → ℂ) := fun n _ _ h => measurable_one.indicator h.measurableSet
  have hχm : Measurable fun x : GA E a × GA E b => (chiT τ x.1 * chiT τ x.2 : ℂ) :=
    ((hmχ a hc₁).comp measurable_fst).mul ((hmχ b hc₂).comp measurable_snd)
  have hχb : ∀ x : GA E a × GA E b, ‖(chiT τ x.1 * chiT τ x.2 : ℂ)‖ ≤ 1 := fun x => by
    rw [norm_mul]
    exact mul_le_one₀ (chiT_norm_le τ _) (norm_nonneg _) (chiT_norm_le τ _)
  have hinv : ∀ (n : ℕ), (∀ g x, ratGL E n g * x ∈ cutSet E n τ ↔ x ∈ cutSet E n τ) → ∀ g (x : GA E n),
      (chiT τ (ratGL E n g * x) : ℂ) = chiT τ x := fun n h g x => by
    by_cases hx : x ∈ cutSet E n τ
    · simp [chiT, hx, (h g x).2 hx]
    · simp [chiT, hx, mt (h g x).1 hx]
  have hχi : ∀ (r : GL (Fin a) E × GL (Fin b) E) (x : GA E a × GA E b),
      (chiT τ (ι r * x).1 * chiT τ (ι r * x).2 : ℂ) = chiT τ x.1 * chiT τ x.2 := fun r x => by
    change (chiT τ (ratGL E a r.1 * x.1) * chiT τ (ratGL E b r.2 * x.2) : ℂ) = _
    rw [hinv a hi₁, hinv b hi₂]
  have hχK : ∀ x : GA E a × GA E b, (chiT τ x.1 * chiT τ x.2 : ℂ) ≠ 0 → ∃ r, ∃ k ∈ C₁ ×ˢ C₂, x = ι r * k := by
    intro x hx
    obtain ⟨_, ⟨r₁, rfl⟩, k₁, hk₁, e₁⟩ := Set.mem_mul.1 (hs₁ (mem_cutSet_of_chiT_ne_zero (left_ne_zero_of_mul hx)))
    obtain ⟨_, ⟨r₂, rfl⟩, k₂, hk₂, e₂⟩ := Set.mem_mul.1 (hs₂ (mem_cutSet_of_chiT_ne_zero (right_ne_zero_of_mul hx)))
    exact ⟨(r₁, r₂), (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁.symm e₂.symm⟩
  have hθc : Continuous θ := (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_fst).prodMk
    (GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA.comp continuous_snd)
  have hφm : ∀ d, Measurable fun x => φ (twConj θ x (ι d)) := fun d =>
    (hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθc)).measurable
  obtain ⟨B, hB⟩ := hφ.supp.exists_bound_of_continuous hφ.cont
  have key := unfold_abs (μ := μ₁.prod μ₂) (ι := ι) (θ := θ) (θR := θR) (cls := cls) (rep := rep) (H := H)
    (χ := fun x => chiT τ x.1 * chiT τ x.2) (φ := φ) hι hθ hFd hcls hH hχm hχb hχi (hC₁.prod hC₂) hχK hφm hB
    (fun L hL => finite_pair hφ.supp hL)
  exact key

/- English proof (translation)
The claim follows from `unfold2_of GlobalTheory.CompanionTheory.MahlerAdelic.mahler`.
-/
theorem unfold2 : Unfold2 := unfold2_of GlobalTheory.CompanionTheory.MahlerAdelic.mahler

end GlobalTheory.CompanionTheory.TwUnfold

end
