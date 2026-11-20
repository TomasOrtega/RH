import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDualTamePart

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.LabTransport

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc, map_eq_zero_iff _ c.injective]`.
-/
theorem val_lt_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A'.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc,
    map_eq_zero_iff _ c.injective]

omit [NumberField E] in

/- English proof (translation)
Set `t : 𝓞 E ≃+* 𝓞 E` to `RingOfIntegers.mapRingEquiv s`. Establish `h1 : w.asIdeal = w'.asIdeal.comap t`. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, ← h x, ← h' (t x), ← val_lt_iff c hc, hs]`. Both sides reduce to the same expression.

Establish `h2 : w'.asIdeal = w.asIdeal.map (t : 𝓞 E →+* 𝓞 E)`. Rewrite using `[h1]`. Conclude with `(Ideal.map_comap_of_surjective (t : 𝓞 E →+* 𝓞 E) t.surjective _).symm`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv w.asIdeal w'.asIdeal t h2).toEquiv).symm`.
-/
theorem normV_eq (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A')
    (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') : normV w' = normV w := by
  let t : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv s
  have h1 : w.asIdeal = w'.asIdeal.comap t := by
    ext x
    rw [Ideal.mem_comap, ← h x, ← h' (t x), ← val_lt_iff c hc, hs]
    rfl
  have h2 : w'.asIdeal = w.asIdeal.map (t : 𝓞 E →+* 𝓞 E) := by
    rw [h1]
    exact (Ideal.map_comap_of_surjective (t : 𝓞 E →+* 𝓞 E) t.surjective _).symm
  exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal w'.asIdeal t h2).toEquiv).symm

open Pointwise in

/- English proof (translation)
Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `γ' • A' = A'`. Use extensionality with `x`. Take `⟨x, rfl⟩` from `γ'.surjective x`. Take `⟨x, rfl⟩` from `c.surjective x`.

Rewrite using `[← AlgEquiv.smul_def, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, hγ, ← hc, ← hc, apply_mem_iff_of_mem_Dec h.1]`. Take `⟨x, rfl⟩` from `c.surjective x`. Rewrite using `[hγ, ← map_sub, val_lt_iff c hc]`. Use `h.2 x ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[ValuationSubring.valuation_le_one_iff]`.

Conclude with `(hc x).mpr hx`.
-/
theorem mem_Ine_of (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) (h : γ ∈ Ine (F := E) A) : γ' ∈ Ine (F := E) A' := by
  refine ⟨?_, fun x hx => ?_⟩
  · change γ' • A' = A'
    ext x
    obtain ⟨x, rfl⟩ := γ'.surjective x
    obtain ⟨x, rfl⟩ := c.surjective x
    rw [← AlgEquiv.smul_def, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, hγ,
      ← hc, ← hc, apply_mem_iff_of_mem_Dec h.1]
  · obtain ⟨x, rfl⟩ := c.surjective x
    rw [hγ, ← map_sub, val_lt_iff c hc]
    refine h.2 x ?_
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact (hc x).mpr hx

/- English proof (translation)
Assemble the required witnesses or components as `⟨mem_Ine_of c.symm (fun y => by rw [hc, c.apply_symm_apply]) (fun y => by rw [eq_comm, c.symm_apply_eq, ← hγ, c.apply_symm_apply]), mem_Ine_of c hc hγ⟩`.
-/
theorem mem_Ine_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) : γ' ∈ Ine (F := E) A' ↔ γ ∈ Ine (F := E) A :=
  ⟨mem_Ine_of c.symm (fun y => by rw [hc, c.apply_symm_apply])
    (fun y => by rw [eq_comm, c.symm_apply_eq, ← hγ, c.apply_symm_apply]), mem_Ine_of c hc hγ⟩

omit [NumberField E] in

/- English proof (translation)
Rewrite using `[mem_Wild, mem_Wild, c.surjective.forall]`. Use `forall_congr' fun y => ?_` and prove the remaining obligations. Rewrite using `[map_ne_zero_iff _ c.injective, hγ, ← val_lt_iff c hc, map_sub c, map_div₀ c, map_one c]`.
-/
theorem mem_Wild_iff (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) : γ' ∈ Wild E A' ↔ γ ∈ Wild E A := by
  rw [mem_Wild, mem_Wild, c.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [map_ne_zero_iff _ c.injective, hγ, ← val_lt_iff c hc, map_sub c,
    map_div₀ c, map_one c]

omit [NumberField E] in

/- English proof (translation)
Use `⟨AlgEquiv.ofRingEquiv (f := (c.symm.trans γ.toRingEquiv).trans c) fun x => ?_, fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `s.surjective x show c (γ (c.symm _)) = _`. Rewrite using `[← hs, c.symm_apply_apply, AlgEquiv.commutes]`. Use `show c (γ (c.symm _)) = _`. Rewrite using `[c.symm_apply_apply]`.
-/
theorem exists_conj (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (γ : G E Ω) :
    ∃ γ' : G E Ω, ∀ y, γ' (c y) = c (γ y) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (c.symm.trans γ.toRingEquiv).trans c) fun x => ?_,
    fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective x
    show c (γ (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, AlgEquiv.commutes]
  · show c (γ (c.symm _)) = _
    rw [c.symm_apply_apply]

omit [NumberField E] in

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_conj s.symm c.symm (fun x => by rw [c.symm_apply_eq, hs, s.apply_symm_apply]) γ'`. Use `⟨γ, fun y => ?_⟩` and prove the remaining obligations. Use `hγ (c y)` as an intermediate fact. Rewrite `this` using `[c.symm_apply_apply]`. Rewrite using `[this, c.apply_symm_apply]`.
-/
theorem exists_conj' (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (γ' : G E Ω) :
    ∃ γ : G E Ω, ∀ y, γ' (c y) = c (γ y) := by
  obtain ⟨γ, hγ⟩ := exists_conj s.symm c.symm
    (fun x => by rw [c.symm_apply_eq, hs, s.apply_symm_apply]) γ'
  refine ⟨γ, fun y => ?_⟩
  have := hγ (c y)
  rw [c.symm_apply_apply] at this
  rw [this, c.apply_symm_apply]

variable [IsAlgClosure E Ω]

/- English proof (translation)
Establish `hiff : TeichmullerInertiaLabelCondition A' w' t γ' ↔ TeichmullerInertiaLabelCondition A w t γ`. Unfold `TeichmullerInertiaLabelCondition`. Rewrite using `[normV_eq s c hs hc h h', mem_Ine_iff c hc hγ]`. Distinguish the cases in `H : TeichmullerInertiaLabelCondition A w t γ`. Establish `H'` using `hiff.mpr H`.

Establish `hsp : b.tameSpace = b'.tameSpace`. Use extensionality with `v`. Rewrite using `[WDRep.mem_tameSpace, WDRep.mem_tameSpace]`. Prove the components needed by the constructor for the conclusion. Introduce `hv σ' hσ'`.

Take `⟨σ, hσ⟩` from `exists_conj' s c hs (σ' : G E Ω)`. Establish `h1` using `(mem_Wild_iff c hc hσ).mp hσ'`. Rewrite using `[← hb ⟨σ, Ine_le_Weil h (Wild_le_Ine h1)⟩ σ' fun z => (hσ z).symm]`. Conclude with `hv _ h1`. Introduce `hv σ hσ1`.

Take `⟨σ', hσ⟩` from `exists_conj s c hs (σ : G E Ω)`. Establish `h1` using `(mem_Wild_iff c hc hσ).mpr hσ1`. Rewrite using `[hb σ ⟨σ', Ine_le_Weil h' (Wild_le_Ine h1)⟩ fun z => (hσ z).symm]`. Conclude with `hv _ h1`. Establish `he : WD.tameEig (WD.mk b') γ' = WD.tameEig (WD.mk b) γ`.

Rewrite using `[WD.tameEig_mk _ (Ine_le_Weil h' H'.2.1), WD.tameEig_mk _ (Ine_le_Weil h H.2.1), ← LinearEquiv.charpoly_conj (LinearEquiv.ofEq _ _ hsp)]`. Use `congr 2`. Use `LinearMap.ext fun v => Subtype.ext ?_` and prove the remaining obligations. Conclude with `(LinearMap.congr_fun (hb ⟨γ, Ine_le_Weil h H.2.1⟩ ⟨γ', Ine_le_Weil h' H'.2.1⟩ fun z => (hγ z).symm) v).symm`. Rewrite using `[WD.lab_eq_iff H', he]`.

Conclude with `⟨WD.lab_monic _ _ _, WD.map_rootsBar_lab H _⟩`. Rewrite using `[WD.lab_of_not H, WD.lab_of_not (mt hiff.mp H)]`.
-/
theorem lab_eq (s : E ≃+* E) (c : Ω ≃+* Ω)
    (hs : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A')
    {h : IsPlaceOver A w} {h' : IsPlaceOver A' w'}
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (b : WDRep h V) (b' : WDRep h' V)
    (hb : ∀ (τ : Weil h) (τ' : Weil h'),
      (∀ z, c ((τ : G E Ω) z) = (τ' : G E Ω) (c z)) → b.ρ τ = b'.ρ τ')
    {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) {γ γ' : G E Ω}
    (hγ : ∀ y, γ' (c y) = c (γ y)) :
    WD.lab t γ' (WD.mk b') = WD.lab t γ (WD.mk b) := by
  have hiff : TeichmullerInertiaLabelCondition A' w' t γ' ↔ TeichmullerInertiaLabelCondition A w t γ := by
    unfold TeichmullerInertiaLabelCondition
    rw [normV_eq s c hs hc h h', mem_Ine_iff c hc hγ]
  by_cases H : TeichmullerInertiaLabelCondition A w t γ
  · have H' := hiff.mpr H
    have hsp : b.tameSpace = b'.tameSpace := by
      ext v
      rw [WDRep.mem_tameSpace, WDRep.mem_tameSpace]
      constructor
      · intro hv σ' hσ'
        obtain ⟨σ, hσ⟩ := exists_conj' s c hs (σ' : G E Ω)
        have h1 := (mem_Wild_iff c hc hσ).mp hσ'
        rw [← hb ⟨σ, Ine_le_Weil h (Wild_le_Ine h1)⟩ σ' fun z => (hσ z).symm]
        exact hv _ h1
      · intro hv σ hσ1
        obtain ⟨σ', hσ⟩ := exists_conj s c hs (σ : G E Ω)
        have h1 := (mem_Wild_iff c hc hσ).mpr hσ1
        rw [hb σ ⟨σ', Ine_le_Weil h' (Wild_le_Ine h1)⟩ fun z => (hσ z).symm]
        exact hv _ h1
    have he : WD.tameEig (WD.mk b') γ' = WD.tameEig (WD.mk b) γ := by
      rw [WD.tameEig_mk _ (Ine_le_Weil h' H'.2.1), WD.tameEig_mk _ (Ine_le_Weil h H.2.1),
        ← LinearEquiv.charpoly_conj (LinearEquiv.ofEq _ _ hsp)]
      congr 2
      refine LinearMap.ext fun v => Subtype.ext ?_
      exact (LinearMap.congr_fun (hb ⟨γ, Ine_le_Weil h H.2.1⟩ ⟨γ', Ine_le_Weil h' H'.2.1⟩
        fun z => (hγ z).symm) v).symm
    rw [WD.lab_eq_iff H', he]
    exact ⟨WD.lab_monic _ _ _, WD.map_rootsBar_lab H _⟩
  · rw [WD.lab_of_not H, WD.lab_of_not (mt hiff.mp H)]

end General

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.host.g_prime k⟩ Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ' x') = (Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ x)).map (·⁻¹) := by intro D k w w' c hs hc x x' n b b' hx hx' _ hb γ γ' h …`.
-/
theorem main : ∀ (D : D7) (k : Fin 2) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    ∀ γ γ' : GE D.nd, (∀ y, γ' (c y) = c (γ y)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ' x') =
      (Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ x)).map (·⁻¹) := by
  intro D k w w' c hs hc x x' n b b' hx hx' _ hb γ γ' hγ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  subst hx'
  rw [lab_eq D.host.conj.toRingEquiv c hs hc b b' hb (D.ntypes.teichC k) hγ, hx]
  exact LabDual.rootsBar_lab_lpDual _ _ _ _ _ _ _ _ x

end GlobalTheory.WeilDeligne.LabTransport
