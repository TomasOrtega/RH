import Mathlib
open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `X _ Ω O _ _ ξ hgen s₀ gm hcomp x a ha`. Take `⟨t, ht⟩ : ∃ t, t = s₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)` from `⟨_, rfl⟩`. Establish `hnat` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom gm)`. Rewrite `hnat` using `[← hcomp, Scheme.Hom.comp_appTop]`. Establish `h1` using `RingHom.congr_fun (congrArg CommRingCat.Hom.hom hnat) a`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha, map_zero] at h1`. Establish `hξt : ξ.appTop.hom t = 0`. Rewrite using `[ht]`. Use `first`. Consider the case `exact h1.symm`.

Consider the case `exact h1`. Establish `hξt' : (ConcreteCategory.hom ξ.appTop) t = 0` using `hξt`. Establish `hpre` using `Scheme.preimage_basicOpen_top ξ t`. Rewrite `hpre` using `[hξt', Scheme.basicOpen_zero]`. Establish `hbot : X.basicOpen t = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `q hq`. Establish `hmem : ξ (IsLocalRing.closedPoint Ω) ∈ X.basicOpen t` using `(hgen q).mem_open (X.basicOpen t).isOpen hq`. Establish `hc` using `(Scheme.Hom.mem_preimage ξ (U := X.basicOpen t)).mpr hmem`. Rewrite `hc` using `[hpre]`.

Conclude with `(TopologicalSpace.Opens.mem_bot.mp hc).elim`. Establish `ht0 : t = 0` using `eq_zero_of_basicOpen_eq_bot t hbot`. Establish `hnat2` using `Scheme.ΓSpecIso_inv_naturality (Spec.preimage (X.fromSpecStalk x ≫ s₀))`. Rewrite `hnat2` using `[Spec.map_preimage, Iso.comp_inv_eq]`. Rewrite using `[hnat2, Scheme.Hom.comp_appTop]`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Rewrite using `[← ht, ht0, map_zero, map_zero]`.
-/
theorem germ_vanishes_of_generic_vanishing : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 := by
  intro X _ Ω O _ _ ξ hgen s₀ gm hcomp x a ha
  obtain ⟨t, ht⟩ : ∃ t, t = s₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) :=
    ⟨_, rfl⟩
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom gm)
  rw [← hcomp, Scheme.Hom.comp_appTop] at hnat
  have h1 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hnat) a
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha, map_zero] at h1
  have hξt : ξ.appTop.hom t = 0 := by
    rw [ht]
    first
    | exact h1.symm
    | exact h1
  have hξt' : (ConcreteCategory.hom ξ.appTop) t = 0 := hξt
  have hpre := Scheme.preimage_basicOpen_top ξ t
  rw [hξt', Scheme.basicOpen_zero] at hpre
  have hbot : X.basicOpen t = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hmem : ξ (IsLocalRing.closedPoint Ω) ∈ X.basicOpen t :=
      (hgen q).mem_open (X.basicOpen t).isOpen hq
    have hc := (Scheme.Hom.mem_preimage ξ (U := X.basicOpen t)).mpr hmem
    rw [hpre] at hc
    exact (TopologicalSpace.Opens.mem_bot.mp hc).elim
  have ht0 : t = 0 := eq_zero_of_basicOpen_eq_bot t hbot
  have hnat2 := Scheme.ΓSpecIso_inv_naturality (Spec.preimage (X.fromSpecStalk x ≫ s₀))
  rw [Spec.map_preimage, Iso.comp_inv_eq] at hnat2
  rw [hnat2, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← ht, ht0, map_zero, map_zero]

end PositivityTheory.UnitarySelfGeneration
