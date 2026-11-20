import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ConjIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.P_SSatEx
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PBasic
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSGalAdEx

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T UpperTheory.ConvolutionTheory.Dp
open GlobalTheory.CuspRep Formalism.ConjugateSelfDual Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `exCusp K n μ V hV`. Use `choose Λ hΛ _ using sInfEx K n μ V hV`. Establish `h : ∀ᶠ w : Pl K in cofinite, ∃ B, SSat μ V w B` using `(SatakeParameterExistence.cx UpperTheory.V.Af.formsFiniteGL n π).mono fun w ⟨B, hB⟩ => ⟨_, (sSatIff K n μ π V hπ w _).2 ⟨B, rfl, hB⟩⟩`. Use `⟨Λ, fun w => if h : ∃ B, SSat μ V w B then h.choose else 0, _, h, hΛ, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw' : ∃ B, SSat μ V w B` using `not_not.1 hw`.

Simplify using `only [dif_pos hw']`. Conclude with `hw'.choose_spec`.
-/
private theorem atEx (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) : ∃ Λ t, AtAE μ V Λ t := by
  classical
  obtain ⟨π, hπ, -⟩ := exCusp K n μ V hV
  choose Λ hΛ _ using sInfEx K n μ V hV
  have h : ∀ᶠ w : Pl K in cofinite, ∃ B, SSat μ V w B :=
    (SatakeParameterExistence.cx UpperTheory.V.Af.formsFiniteGL n π).mono fun w ⟨B, hB⟩ => ⟨_, (sSatIff K n μ π V hπ w _).2 ⟨B, rfl, hB⟩⟩
  refine ⟨Λ, fun w => if h : ∃ B, SSat μ V w B then h.choose else 0, _, h, hΛ, fun w hw => ?_⟩
  have hw' : ∃ B, SSat μ V w B := not_not.1 hw
  simp only [dif_pos hw']
  exact hw'.choose_spec

/- English proof (translation)
Take `⟨S, hS, -, H⟩` from `H`. Conclude with `hS.eventually_cofinite_notMem.mono fun w hw => (sSatIff K n μ π V h w _).1 (H w hw)`.
-/
private theorem satOf {π : CuspSub K n} {V : Submodule ℂ (LL μ)} {Λ t} (h : Carries μ π V) (H : AtAE μ V Λ t) :
    ∀ᶠ w : Pl K in cofinite, ∃ B : Multiset ℂˣ, t w = B.map (fun b : ℂˣ => (b : ℂ)) ∧ (CG.mk π).HasSat w B := by
  obtain ⟨S, hS, -, H⟩ := H
  exact hS.eventually_cofinite_notMem.mono fun w hw => (sSatIff K n μ π V h w _).1 (H w hw)

/- English proof (translation)
Take `⟨S, -, H, -⟩` from `H`. Rewrite using `[← sInfIff K n μ π V h]`. Conclude with `⟨fun h1 => (sInfEx K n μ V h.summand τ).unique h1 (H τ), fun h1 => h1 ▸ H τ⟩`.
-/
private theorem infOf {π : CuspSub K n} {V : Submodule ℂ (LL μ)} {Λ t} (h : Carries μ π V) (H : AtAE μ V Λ t) (τ m) :
    (Cusp.cx π).inf τ m ↔ m = Λ τ := by
  obtain ⟨S, -, H, -⟩ := H
  rw [← sInfIff K n μ π V h]
  exact ⟨fun h1 => (sInfEx K n μ V h.summand τ).unique h1 (H τ), fun h1 => h1 ▸ H τ⟩

private noncomputable def pull (n : ℕ) (g : K ≃+* K) (f : GA K n → ℂ) : GA K n → ℂ :=
  fun x => f (Matrix.GeneralLinearGroup.map (CT.adMap g) x)

/- English proof (translation)
Establish `hs : ∀ s : Ad K ≃+* Ad K, IsGalAd g s → s.toRingHom = CT.adMap g` using `fun s h => UpperTheory.ConvolutionTheory.K.adUnique K g s.toRingHom h.1 h.2.1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨s, h1⟩` from `SGalAdEx_holds K g`. Take `⟨P', hsp, hiso⟩` from `h s h1`.

Consider the cases of `P' with`. Consider the case `cx π'`. Take `rfl : π' = P` from `(isoEq K n π' P).1 hiso`. Rewrite `hsp` using `[hs s h1]`. Conclude with `hsp`.

Consider the case `re π' => exact hiso.elim`. Introduce `h s h1`. Use `⟨.cx P, ?_, (isoEq K n P P).2 rfl⟩` and prove the remaining obligations. Rewrite using `[hs s h1]`. Conclude with `h`.
-/
private theorem conj_iff (P : CuspSub K n) (g : K ≃+* K) :
    (Cusp.cx P).ConjIso g ↔ (Cusp.cx P).space = pull n g '' (Cusp.cx P).space := by
  have hs : ∀ s : Ad K ≃+* Ad K, IsGalAd g s → s.toRingHom = CT.adMap g := fun s h => UpperTheory.ConvolutionTheory.K.adUnique K g s.toRingHom h.1 h.2.1
  constructor
  · intro h
    obtain ⟨s, h1⟩ := SGalAdEx_holds K g
    obtain ⟨P', hsp, hiso⟩ := h s h1
    cases P' with
    | cx π' =>
      obtain rfl : π' = P := (isoEq K n π' P).1 hiso
      rw [hs s h1] at hsp
      exact hsp
    | re π' => exact hiso.elim
  · intro h s h1
    refine ⟨.cx P, ?_, (isoEq K n P P).2 rfl⟩
    rw [hs s h1]
    exact h

omit [IsTotallyComplex K] in
/- English proof (translation)
Use function extensionality and compare the values at `f x`. Use `congrArg f (Matrix.GeneralLinearGroup.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `(UpperTheory.ConvolutionTheory.K.adBasic K).2.1 _`.
-/
private theorem pull_refl : pull n (RingEquiv.refl K) = id := by
  funext f x
  refine congrArg f (Matrix.GeneralLinearGroup.ext fun i j => ?_)
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.1 _

omit [IsTotallyComplex K] in
/- English proof (translation)
Use function extensionality and compare the values at `f x`. Use `congrArg f (Matrix.GeneralLinearGroup.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `(UpperTheory.ConvolutionTheory.K.adBasic K).2.2 g g' _`.
-/
private theorem pull_trans (g g' : K ≃+* K) : pull n (g.trans g') = pull n g ∘ pull n g' := by
  funext f x
  refine congrArg f (Matrix.GeneralLinearGroup.ext fun i j => ?_)
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.2 g g' _

end SlopeTestRemainingChoices

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `Tendsto.cofinite_of_finite_preimage_singleton fun v => by refine Set.Finite.to_subtype ((Ideal.finite_factors (I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) ?_).subset fun w hw => ?_) · exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).not.2 v.ne_bo …`.
-/
private theorem tend : Tendsto (fun w : Pl E => w.under (𝓞 F)) cofinite cofinite :=
  Tendsto.cofinite_of_finite_preimage_singleton fun v => by
    refine Set.Finite.to_subtype ((Ideal.finite_factors (I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) ?_).subset fun w hw => ?_)
    · exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).not.2 v.ne_bot
    · obtain rfl : w.under (𝓞 F) = v := hw
      exact Ideal.dvd_iff_le.2 Ideal.map_comap_le

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
private theorem nv (K : Type) [Field K] [NumberField K] (w : Pl K) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

/- English proof (translation)
Use `filter_upwards [(tend (F := F) (E := E)).eventually h, h'] with w ⟨B, e, hB⟩ ⟨B', e', hB'⟩ f hf`. Establish `h1` using `(places F E hp).2.2.2.2.1 w`. Rewrite `hf` using `[nv, nv, h1]`. Establish `h2 : 2 ≤ Ideal.absNorm (w.under (𝓞 F)).asIdeal`. Establish `a` using `Ideal.absNorm_eq_zero_iff.not.2 (w.under (𝓞 F)).ne_bot`.

Establish `b` using `Ideal.absNorm_eq_one_iff.not.2 (w.under (𝓞 F)).isPrime.ne_top`. Use linear arithmetic over natural numbers and integers. Take `rfl` from `Nat.pow_right_injective h2 hf`. Use `⟨B, hB, ?_⟩` and prove the remaining obligations. Establish `: B.map (· ^ resDeg F w) = B'`.

Use `Multiset.map_injective Units.val_injective ?_` and prove the remaining obligations. Rewrite using `[← e', bcSat, e, Multiset.map_map, Multiset.map_map]`. Conclude with `Multiset.map_congr rfl fun b _ => by simp`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
private theorem weak [IsGalois F E] (hp : (Module.finrank F E).Prime) {sat : Pl F → Multiset ℂˣ → Prop} {sat' : Pl E → Multiset ℂˣ → Prop}
    {t : Pl F → Multiset ℂ} (h : ∀ᶠ v : Pl F in cofinite, ∃ B : Multiset ℂˣ, t v = B.map (fun b : ℂˣ => (b : ℂ)) ∧ sat v B)
    (h' : ∀ᶠ w : Pl E in cofinite, ∃ B : Multiset ℂˣ, bcSat t w = B.map (fun b : ℂˣ => (b : ℂ)) ∧ sat' w B) : WeakBC sat sat' := by
  filter_upwards [(tend (F := F) (E := E)).eventually h, h'] with w ⟨B, e, hB⟩ ⟨B', e', hB'⟩ f hf
  have h1 := (places F E hp).2.2.2.2.1 w
  rw [nv, nv, h1] at hf
  have h2 : 2 ≤ Ideal.absNorm (w.under (𝓞 F)).asIdeal := by
    have a := Ideal.absNorm_eq_zero_iff.not.2 (w.under (𝓞 F)).ne_bot
    have b := Ideal.absNorm_eq_one_iff.not.2 (w.under (𝓞 F)).isPrime.ne_top
    omega
  obtain rfl := Nat.pow_right_injective h2 hf
  refine ⟨B, hB, ?_⟩
  have : B.map (· ^ resDeg F w) = B' := by
    refine Multiset.map_injective Units.val_injective ?_
    rw [← e', bcSat, e, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun b _ => by simp
  rwa [this]

end Two

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _`. Use `⟨atEx, atEx, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `π P V V' Λ t Λ' t' h h' H H' rfl e`. Use `⟨weak hp (satOf h H) ?_, fun τ m => ?_⟩` and prove the remaining obligations. Use `filter_upwards [satOf h' H', e] with w hw e'`.

Conclude with `e' ▸ hw`. Rewrite using `[infOf h H, infOf h' H']`. Both sides reduce to the same expression. Introduce and unpack `π V Λ t h H ⟨ι, _, m, Q, h1, h2, h3⟩`. Conclude with `⟨ι, inferInstance, m, Q, h1, h2, weak hp (satOf h H) (h3.mono fun w ⟨B, a, b⟩ => ⟨B, b, a⟩)⟩`.

Introduce and unpack `P V Λ t h H ⟨ι, _, m, Q, h1, h2, h3⟩`. Take `⟨s, -⟩` from `PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => CG.mk P) Q (fun _ => hn) h1 (by filter_upwards [satOf h H, h3] with w ⟨C, e, hC⟩ ⟨B, ⟨B', a, b⟩, e'⟩`. Establish `: C = B` using `Multiset.map_injective Units.val_injective (e.symm.trans e')`. Conclude with `⟨fun _ => C, B', fun _ => hC, a, by simp [this, b]⟩)`. Use `Fintype.card_congr s` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Take `⟨θ, hθ⟩` from `K.galTwistEx E n μE σ.toRingEquiv`. Use `⟨θ, fun g => by rw [K.galAdEq]; exact hθ g, fun P V h => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `SGalAdEx_holds E σ.toRingEquiv`.

Establish `hc` using `conjIff E n μE θ σ.toRingEquiv s hs (fun g => by rw [K.adUnique E _ s.toRingHom hs.1 hs.2.1]; exact hθ g) P V h`. Use `⟨fun H => hc.1 (H σ), fun H g => ?_⟩` and prove the remaining obligations. Establish `h0` using `(conj_iff P _).1 (hc.2 H)`. Take `⟨k, rfl⟩` from `(mem_powers_iff_mem_zpowers.2 (hσ g) : g ∈ Submonoid.powers σ)`. Rewrite using `[conj_iff]`.

Proceed by induction on `k with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `_ = pull n (RingEquiv.refl E) '' _`. Rewrite using `[pull_refl, Set.image_id]`. Consider the case `succ k ih`.

Establish `e : (σ ^ (k + 1)).toRingEquiv = σ.toRingEquiv.trans (σ ^ k).toRingEquiv`. Rewrite using `[pow_succ]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `_ = pull n (σ ^ (k + 1)).toRingEquiv '' _`. Rewrite using `[e, pull_trans, Set.image_comp]`.

Conclude with `h0.trans (congrArg _ ih)`.
-/
theorem UpperTheory.ConvolutionTheory.T.carryLift :
    UpperTheory.ConvolutionTheory.T.CarryLift := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _
  refine ⟨atEx, atEx, ?_, ?_, ?_, ?_⟩
  · rintro π P V V' Λ t Λ' t' h h' H H' rfl e
    refine ⟨weak hp (satOf h H) ?_, fun τ m => ?_⟩
    · filter_upwards [satOf h' H', e] with w hw e'
      exact e' ▸ hw
    · rw [infOf h H, infOf h' H']
      rfl
  · rintro π V Λ t h H ⟨ι, _, m, Q, h1, h2, h3⟩
    exact ⟨ι, inferInstance, m, Q, h1, h2, weak hp (satOf h H) (h3.mono fun w ⟨B, a, b⟩ => ⟨B, b, a⟩)⟩
  · rintro P V Λ t h H ⟨ι, _, m, Q, h1, h2, h3⟩
    obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => CG.mk P) Q (fun _ => hn) h1 (by
      filter_upwards [satOf h H, h3] with w ⟨C, e, hC⟩ ⟨B, ⟨B', a, b⟩, e'⟩
      have : C = B := Multiset.map_injective Units.val_injective (e.symm.trans e')
      exact ⟨fun _ => C, B', fun _ => hC, a, by simp [this, b]⟩)
    have := Fintype.card_congr s
    simp at this
    omega
  · obtain ⟨θ, hθ⟩ := K.galTwistEx E n μE σ.toRingEquiv
    refine ⟨θ, fun g => by rw [K.galAdEq]; exact hθ g, fun P V h => ?_⟩
    obtain ⟨s, hs⟩ := SGalAdEx_holds E σ.toRingEquiv
    have hc := conjIff E n μE θ σ.toRingEquiv s hs
      (fun g => by rw [K.adUnique E _ s.toRingHom hs.1 hs.2.1]; exact hθ g) P V h
    refine ⟨fun H => hc.1 (H σ), fun H g => ?_⟩
    have h0 := (conj_iff P _).1 (hc.2 H)
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hσ g) : g ∈ Submonoid.powers σ)
    rw [conj_iff]
    induction k with
    | zero =>
      change _ = pull n (RingEquiv.refl E) '' _
      rw [pull_refl, Set.image_id]
    | succ k ih =>
      have e : (σ ^ (k + 1)).toRingEquiv = σ.toRingEquiv.trans (σ ^ k).toRingEquiv := by
        rw [pow_succ]; rfl
      change _ = pull n (σ ^ (k + 1)).toRingEquiv '' _
      rw [e, pull_trans, Set.image_comp]
      exact h0.trans (congrArg _ ih)
