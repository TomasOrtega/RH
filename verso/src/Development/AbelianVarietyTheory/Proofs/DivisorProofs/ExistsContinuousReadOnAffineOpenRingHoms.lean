import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ContRead

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {U : X.Opens}

/- English proof (translation)
Establish `e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz`. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]`. Conclude with `CommRingCat.hom_ext e`. Establish `a` using `IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy`. Establish `a'` using `IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz`.

Rewrite `a` using `[e₁, a', IsAffineOpen.fromSpec_top]`. Conclude with `((cancel_epi _).1 a).symm`.
-/
theorem val_eq_of_evHom_eq (hU : IsAffineOpen U) {σ τ : k →+* ℂ} {y : CxPts p σ} {z : CxPts p τ}
    (hy : y ∈ ptsIn p σ U) (hz : z ∈ ptsIn p τ U) (e : evHom hy = evHom hz) : y.1 = z.1 := by
  have e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

/- English proof (translation)
Substitute `e` using the available equality. Rewrite using `[Subtype.ext h]`.
-/
theorem eq_of_val_eq (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) {σ τ : k →+* ℂ} (e : σ = τ)
    (y : CxPts p σ) (z : CxPts p τ) (h : y.1 = z.1) : u σ y = u τ z := by
  subst e
  rw [Subtype.ext h]

/- English proof (translation)
The claim follows from `RingHom.ext fun f => (ev_eq _ f).symm.trans (ev_ofHom hU φ h f)`.
-/
theorem evHom_ofHom (hU : IsAffineOpen U) {σ : k →+* ℂ} (φ : Γ(X, U) →+* ℂ)
    (h : ∀ a, φ (algX p U a) = σ a) : evHom (ofHom_mem hU φ h) = φ :=
  RingHom.ext fun f => (ev_eq _ f).symm.trans (ev_ofHom hU φ h f)

/- English proof (translation)
The claim follows from `RingHom.ext fun a => (ev_eq hy _).symm.trans (ev_algX hy a)`.
-/
theorem evHom_comp_algX {σ : k →+* ℂ} {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    (evHom hy).comp (algX p U) = σ :=
  RingHom.ext fun a => (ev_eq hy _).symm.trans (ev_algX hy a)

/- English proof (translation)
Introduce `k _ X _ p D hX U hU u hu`. Use `letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance`. Establish `hcf : ∀ f : Γ(X, U), Continuous fun x : Γ(X, U) →+* ℂ => x f` using `fun f => (continuous_apply f).comp continuous_induced_dom`. Use `⟨fun x => u (x.comp (algX p U)) (ofHom hU x fun _ => rfl), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hX.finite_emb classical` as an intermediate fact.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `x₀`. Take `⟨σ₀, hσ₀⟩ : ∃ σ₀, x₀.comp (algX p U) = σ₀` from `⟨_, rfl⟩`. Establish `hN : {x : Γ(X, U) →+* ℂ | x.comp (algX p U) = σ₀} ∈ 𝓝 x₀`. Establish `hex : ∀ τ : k →+* ℂ, τ ≠ σ₀ → ∃ a, τ a ≠ σ₀ a` using `fun τ h => by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (RingHom.ext hc)`. Use `choose! a ha using hex`. Establish `hopen : ∀ τ : k →+* ℂ, {x : Γ(X, U) →+* ℂ | τ ≠ σ₀ → x (algX p U (a τ)) ≠ τ (a τ)} ∈ 𝓝 x₀`.

Introduce `τ`. Distinguish the cases in `hτ : τ = σ₀`. Conclude with `Filter.Eventually.of_forall fun x h => (h hτ).elim`. Establish `ho : IsOpen {x : Γ(X, U) →+* ℂ | x (algX p U (a τ)) ≠ τ (a τ)}` using `isOpen_ne_fun (hcf _) continuous_const filter_upwards [ho.mem_nhds (show x₀ (algX p U (a τ)) ≠ τ (a τ) from fun h => ha τ hτ (h.symm.trans (RingHom.congr_fun hσ₀ (a τ))))] with x hx _ using hx`. Use `filter_upwards [(Filter.iInter_mem (f := 𝓝 x₀)).2 hopen] with x hx`.

Assume the negation of the conclusion as `hne`. Conclude with `(Set.mem_iInter.1 hx _) hne rfl`. Set `F : (Γ(X, U) →+* ℂ) → CxPts p σ₀` to `fun x => if h : x.comp (algX p U) = σ₀ then ofHom hU x (fun a => RingHom.congr_fun h a) else ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)`. Establish `hF0 : F x₀ = ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)` using `dif_pos hσ₀`. Establish `hFmem : ∀ x, F x ∈ ptsIn p σ₀ U` using `fun x => by`.

Distinguish the cases in `h : x.comp (algX p U) = σ₀`. Simplify using `only [F, dif_pos h]`. Conclude with `ofHom_mem _ _ _`. Simplify using `only [F, dif_neg h]`. Conclude with `ofHom_mem _ _ _`.

Establish `hF : ContinuousAt F x₀`. Use `tendsto_subtype_rng.2 ?_` and prove the remaining obligations. Rewrite using `[hF0]`. Use `GlobalTheory.Points.tendsto_of_isAffineOpen hU (ofHom_mem hU x₀ _) (Filter.Eventually.of_forall hFmem) fun f => ?_` and prove the remaining obligations. Establish `e : ∀ᶠ x in 𝓝 x₀, x f = valR (F x).1 U f` using `by filter_upwards [hN] with x hx`.

Simplify using `only [F, dif_pos hx]`. Conclude with `(ev_ofHom hU x _ f).symm`. Rewrite using `[show valR (ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)).1 U f = x₀ f from ev_ofHom hU x₀ _ f]`. Conclude with `((hcf f).tendsto x₀).congr' e`. Establish `hu0 : ContinuousAt (u σ₀) (F x₀)` using `(hu σ₀).continuousAt ((isOpen_ptsIn U).mem_nhds (hFmem x₀))`.

Use `(hu0.comp hF).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hN] with x hx`. Simplify using `only [Function.comp_apply, F, dif_pos hx]`. Conclude with `eq_of_val_eq u hx _ _ rfl`. Introduce `σ y hy`.

Conclude with `eq_of_val_eq u (evHom_comp_algX hy) _ _ (val_eq_of_evHom_eq hU (ofHom_mem hU _ _) hy (evHom_ofHom hU _ _))`. Introduce `x`. Conclude with `⟨x.comp (algX p U), ofHom hU x (fun _ => rfl), ofHom_mem hU x _, evHom_ofHom hU x _⟩`. Introduce `σ y hy W hW`. Rewrite `hW` using `[nhds_induced]`.

Take `⟨t, ht, hsub⟩` from `mem_comap.1 hW`. Establish `hc : ContinuousAt (fun z : CxPts p σ => fun f : Γ(X, U) => ev p σ U f z) y` using `continuousAt_pi.2 fun f => (continuousOn_ev f).continuousAt ((isOpen_ptsIn U).mem_nhds hy)`. Establish `hval : (fun f : Γ(X, U) => ev p σ U f y) = ⇑(evHom hy)` using `funext fun f => ev_eq hy f`. Rewrite `ht` using `[← hval]`. Use `filter_upwards [hc.preimage_mem_nhds ht, (isOpen_ptsIn U).mem_nhds hy] with z hz hzU`.

Use `⟨hzU, hsub ?_⟩` and prove the remaining obligations. Establish `hv : (fun f : Γ(X, U) => ev p σ U f z) = ⇑(evHom hzU)` using `funext fun f => ev_eq hzU f`. Use `show ⇑(evHom hzU) ∈ t`. Rewrite using `[← hv]`. Conclude with `hz`.
-/
theorem exists_continuous_read : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  intro k _ X _ p D hX U hU u hu
  letI : TopologicalSpace (Γ(X, U) →+* ℂ) :=
    TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance
  have hcf : ∀ f : Γ(X, U), Continuous fun x : Γ(X, U) →+* ℂ => x f := fun f =>
    (continuous_apply f).comp continuous_induced_dom
  refine ⟨fun x => u (x.comp (algX p U)) (ofHom hU x fun _ => rfl), ?_, ?_, ?_, ?_⟩
  · have := hX.finite_emb
    classical
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, x₀.comp (algX p U) = σ₀ := ⟨_, rfl⟩
    have hN : {x : Γ(X, U) →+* ℂ | x.comp (algX p U) = σ₀} ∈ 𝓝 x₀ := by
      have hex : ∀ τ : k →+* ℂ, τ ≠ σ₀ → ∃ a, τ a ≠ σ₀ a := fun τ h => by
        by_contra hc
        push_neg at hc
        exact h (RingHom.ext hc)
      choose! a ha using hex
      have hopen : ∀ τ : k →+* ℂ,
          {x : Γ(X, U) →+* ℂ | τ ≠ σ₀ → x (algX p U (a τ)) ≠ τ (a τ)} ∈ 𝓝 x₀ := by
        intro τ
        by_cases hτ : τ = σ₀
        · exact Filter.Eventually.of_forall fun x h => (h hτ).elim
        · have ho : IsOpen {x : Γ(X, U) →+* ℂ | x (algX p U (a τ)) ≠ τ (a τ)} :=
            isOpen_ne_fun (hcf _) continuous_const
          filter_upwards [ho.mem_nhds (show x₀ (algX p U (a τ)) ≠ τ (a τ) from
            fun h => ha τ hτ (h.symm.trans (RingHom.congr_fun hσ₀ (a τ))))] with x hx _ using hx
      filter_upwards [(Filter.iInter_mem (f := 𝓝 x₀)).2 hopen] with x hx
      by_contra hne
      exact (Set.mem_iInter.1 hx _) hne rfl
    let F : (Γ(X, U) →+* ℂ) → CxPts p σ₀ := fun x =>
      if h : x.comp (algX p U) = σ₀ then ofHom hU x (fun a => RingHom.congr_fun h a)
      else ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)
    have hF0 : F x₀ = ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a) := dif_pos hσ₀
    have hFmem : ∀ x, F x ∈ ptsIn p σ₀ U := fun x => by
      by_cases h : x.comp (algX p U) = σ₀
      · simp only [F, dif_pos h]; exact ofHom_mem _ _ _
      · simp only [F, dif_neg h]; exact ofHom_mem _ _ _
    have hF : ContinuousAt F x₀ := by
      refine tendsto_subtype_rng.2 ?_
      rw [hF0]
      refine GlobalTheory.Points.tendsto_of_isAffineOpen hU (ofHom_mem hU x₀ _) (Filter.Eventually.of_forall hFmem)
        fun f => ?_
      have e : ∀ᶠ x in 𝓝 x₀, x f = valR (F x).1 U f := by
        filter_upwards [hN] with x hx
        simp only [F, dif_pos hx]
        exact (ev_ofHom hU x _ f).symm
      rw [show valR (ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)).1 U f = x₀ f from
        ev_ofHom hU x₀ _ f]
      exact ((hcf f).tendsto x₀).congr' e
    have hu0 : ContinuousAt (u σ₀) (F x₀) :=
      (hu σ₀).continuousAt ((isOpen_ptsIn U).mem_nhds (hFmem x₀))
    refine (hu0.comp hF).congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    simp only [Function.comp_apply, F, dif_pos hx]
    exact eq_of_val_eq u hx _ _ rfl
  · intro σ y hy
    exact eq_of_val_eq u (evHom_comp_algX hy) _ _
      (val_eq_of_evHom_eq hU (ofHom_mem hU _ _) hy (evHom_ofHom hU _ _))
  · intro x
    exact ⟨x.comp (algX p U), ofHom hU x (fun _ => rfl), ofHom_mem hU x _, evHom_ofHom hU x _⟩
  · intro σ y hy W hW
    rw [nhds_induced] at hW
    obtain ⟨t, ht, hsub⟩ := mem_comap.1 hW
    have hc : ContinuousAt (fun z : CxPts p σ => fun f : Γ(X, U) => ev p σ U f z) y :=
      continuousAt_pi.2 fun f => (continuousOn_ev f).continuousAt ((isOpen_ptsIn U).mem_nhds hy)
    have hval : (fun f : Γ(X, U) => ev p σ U f y) = ⇑(evHom hy) := funext fun f => ev_eq hy f
    rw [← hval] at ht
    filter_upwards [hc.preimage_mem_nhds ht, (isOpen_ptsIn U).mem_nhds hy] with z hz hzU
    refine ⟨hzU, hsub ?_⟩
    have hv : (fun f : Γ(X, U) => ev p σ U f z) = ⇑(evHom hzU) := funext fun f => ev_eq hzU f
    show ⇑(evHom hzU) ∈ t
    rw [← hv]
    exact hz

end GlobalTheory.ContRead
