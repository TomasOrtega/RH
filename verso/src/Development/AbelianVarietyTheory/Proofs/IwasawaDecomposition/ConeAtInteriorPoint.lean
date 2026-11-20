import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteLocalEtaleNeighbourhoodStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarizedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformizationAbelianStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

section Empty

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hB : ∀ β : LinearMap.BilinForm ℤ X, β = 0` using `fun β => LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp`. Establish `hz : ∀ β : LinearMap.BilinForm ℤ X, φ.evalZ β = 0` using `fun β => φ.eval_of_subsingleton _`. Use `⟨fun i => i.elim0, fun i => i.elim0, ?_, fun c _ => ?_, ?_⟩` and prove the remaining obligations. Establish `: Subsingleton (balForms H.bar X)` using `⟨fun a b => Subtype.ext ((hB a).trans (hB b).symm)⟩`. Conclude with `⟨0, Module.Basis.empty _, fun i => i.elim0⟩`.

Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty]`. Conclude with `φ.eval_of_subsingleton _`. Use `⟨1, 0, one_pos, fun i => i.elim0, fun β _ _ => by simp [hz], fun β _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩` and prove the remaining obligations. Simplify using `[hB β]`.
-/
theorem isCone_empty (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Subsingleton X] : ConeO H φ X 0 Fin.elim0 := by
  have hB : ∀ β : LinearMap.BilinForm ℤ X, β = 0 := fun β =>
    LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  have hz : ∀ β : LinearMap.BilinForm ℤ X, φ.evalZ β = 0 := fun β => φ.eval_of_subsingleton _
  refine ⟨fun i => i.elim0, fun i => i.elim0, ?_, fun c _ => ?_, ?_⟩
  · have : Subsingleton (balForms H.bar X) := ⟨fun a b => Subtype.ext ((hB a).trans (hB b).symm)⟩
    exact ⟨0, Module.Basis.empty _, fun i => i.elim0⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact φ.eval_of_subsingleton _
  · refine ⟨1, 0, one_pos, fun i => i.elim0, fun β _ _ => by simp [hz], fun β _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩
    simp [hB β]

/- English proof (translation)
Introduce `W _ _ _ _ ϖ _ f be _ _`. Use `⟨Fin.elim0, fun i => i.elim0, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[Subsingleton.elim a 0]`. Simplify using the standard rewrite rules.
-/
theorem inCone_empty {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) [Subsingleton Dg.X] :
    InCone Dg (m := 0) Fin.elim0 := by
  intro W _ _ _ _ ϖ _ f be _ _
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  ext a b
  rw [Subsingleton.elim a 0]
  simp

end Empty

end GlobalTheory.GenFan

namespace GlobalTheory.GenFan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

/- English proof (translation)
Unfold `Model.j`. Establish `: IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))`. Establish `: IsIso (spMap (RingHom.id c.F))` using `by show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))`. Rewrite using `[show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]`. Use `infer_instance`.

Use `infer_instance`. Use `Y.jQ_open` as an intermediate fact. Use `infer_instance`.
-/
theorem isOpenImmersion_j (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  unfold Model.j
  have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
      infer_instance
    infer_instance
  have := Y.jQ_open
  infer_instance

/- English proof (translation)
Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `: IsProper Y.s` using `projProper _ _ _ Y.proj`. Take `⟨R, _, _, _, ξ, hR, hξ, he, hu, hsp⟩` from `GlobalTheory.T.exists_complete_local_etale_neighbourhood c.F Y.X Y.s inferInstance Y.normal (Y.j w)`. Establish `hj` using `isOpenImmersion_j Y`.

Establish `hr : Set.range ξ ⊆ Set.range Y.j` using `fun _ ⟨p, hp⟩ => hp ▸ (hsp p).mem_open Y.j.isOpenEmbedding.isOpen_range ⟨w, rfl⟩`. Take `⟨t, m, hpol, hth, hab⟩` from `GlobalTheory.T.exists_semi_abelian_polarized Y R ξ hR hr`. Take `⟨P, hP, hX⟩` from `GlobalTheory.T.exists_uniformization_abelian R t hR hpol hth hab`. Conclude with `⟨R, _, _, _, ξ, t, m, P, 0, Fin.elim0, hR, hξ, he, hu, hP, isCone_empty H φ _, inCone_empty _⟩`.
-/
theorem coneAt_j (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (w : Xo.XF c) :
    GlobalTheory.GenFan.ConeAt (ConeO H φ) Y (Y.j w) := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsProper Y.s := projProper _ _ _ Y.proj
  obtain ⟨R, _, _, _, ξ, hR, hξ, he, hu, hsp⟩ := GlobalTheory.T.exists_complete_local_etale_neighbourhood c.F Y.X Y.s inferInstance Y.normal (Y.j w)
  have hj := isOpenImmersion_j Y
  have hr : Set.range ξ ⊆ Set.range Y.j := fun _ ⟨p, hp⟩ =>
    hp ▸ (hsp p).mem_open Y.j.isOpenEmbedding.isOpen_range ⟨w, rfl⟩
  obtain ⟨t, m, hpol, hth, hab⟩ := GlobalTheory.T.exists_semi_abelian_polarized Y R ξ hR hr
  obtain ⟨P, hP, hX⟩ := GlobalTheory.T.exists_uniformization_abelian R t hR hpol hth hab
  exact ⟨R, _, _, _, ξ, t, m, P, 0, Fin.elim0, hR, hξ, he, hu, hP, isCone_empty H φ _, inCone_empty _⟩

end GlobalTheory.GenFan
