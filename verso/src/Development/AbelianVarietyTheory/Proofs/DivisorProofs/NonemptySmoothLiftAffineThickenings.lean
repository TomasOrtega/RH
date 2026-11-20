import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebraStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift.LiftEx

/- English proof (translation)
Take `⟨N, hN⟩` from `(isDPNilpotent_iff_exists_isLevel κ).1 hκ`. Use `(isDPNilpotent_iff_exists_isLevel δ).2 ⟨N, ?_⟩` and prove the remaining obligations. Use `fil_le_map_fil R I κ A _ δ f h rfl N` as an intermediate fact. Rewrite `this` using `[show fil κ N = ⊥ from hN, Ideal.map_bot]`. Conclude with `le_bot_iff.1 this`.
-/
theorem isPDNilpotent_map {R A : Type} [CommRing R] [CommRing A] {I : Ideal R} {κ : DividedPowers I} (f : R →+* A)
    {δ : DividedPowers (I.map f)} (h : IsDPMorphism κ δ f) (hκ : IsNilDP κ) : IsNilDP δ := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel κ).1 hκ
  refine (isDPNilpotent_iff_exists_isLevel δ).2 ⟨N, ?_⟩
  have := fil_le_map_fil R I κ A _ δ f h rfl N
  rw [show fil κ N = ⊥ from hN, Ideal.map_bot] at this
  exact le_bot_iff.1 this

/- English proof (translation)
Use `IsDPMorphism.on_span δ δ' (S := algebraMap R A '' I) rfl ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Rewrite using `[RingHom.coe_coe, φ.commutes]`. Conclude with `Ideal.mem_map_of_mem _ ha`. Introduce and unpack `n _ ⟨a, ha, rfl⟩`.

Rewrite using `[h.2 a ha, RingHom.coe_coe, φ.commutes, φ.commutes, h'.2 a ha]`.
-/
theorem isDPMorphism_algHom {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {I : Ideal R} {κ : DividedPowers I} {δ : DividedPowers (I.map (algebraMap R A))}
    {δ' : DividedPowers (I.map (algebraMap R A'))} (h : IsDPMorphism κ δ (algebraMap R A))
    (h' : IsDPMorphism κ δ' (algebraMap R A')) (φ : A →ₐ[R] A') : IsDPMorphism δ δ' (φ : A →+* A') := by
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R A '' I) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [RingHom.coe_coe, φ.commutes]
    exact Ideal.mem_map_of_mem _ ha
  · rintro n _ ⟨a, ha, rfl⟩
    rw [h.2 a ha, RingHom.coe_coe, φ.commutes, φ.commutes, h'.2 a ha]

abbrev ext (D : Data) (U : D.X.affineOpens) : Ideal (Sec D.s U.1) := D.I.map (algebraMap D.R (Sec D.s U.1))

/- English proof (translation)
Take `⟨s₀, hpb, ht⟩` from `D.red`. Set `q : D.R ⧸ D.I →+* Sec D.s U.1 ⧸ ext D U` to `Ideal.quotientMap (ext D U) (algebraMap D.R (Sec D.s U.1)) Ideal.le_comap_map`. Establish `hq : spMap q ≫ spMap (Ideal.Quotient.mk D.I) = spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1)))`. Rewrite using `[← Cris.spMap_comp]`. Both sides reduce to the same expression.

Use `⟨hpb.lift (spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U) (spMap q) ?_, hpb.lift_fst _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, Category.assoc, affPt_w, Cris.spMap_comp]`. Rewrite using `[ht, ← Category.assoc, hpb.lift_snd, hq]`.
-/
theorem exists_pt (D : Data) (U : D.X.affineOpens) : ∃ x : Sp (Sec D.s U.1 ⧸ ext D U) ⟶ D.X₀,
    x ≫ D.i = spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U ∧
    x ≫ D.t = spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  let q : D.R ⧸ D.I →+* Sec D.s U.1 ⧸ ext D U :=
    Ideal.quotientMap (ext D U) (algebraMap D.R (Sec D.s U.1)) Ideal.le_comap_map
  have hq : spMap q ≫ spMap (Ideal.Quotient.mk D.I) =
      spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
    rw [← Cris.spMap_comp]; rfl
  refine ⟨hpb.lift (spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U) (spMap q) ?_, hpb.lift_fst _ _ _, ?_⟩
  · rw [hq, Category.assoc, affPt_w, Cris.spMap_comp]
  · rw [ht, ← Category.assoc, hpb.lift_snd, hq]

/- English proof (translation)
Use `haveI := D.sec_smooth U`. Conclude with `GlobalTheory.T.exists_isDPMorphism_of_flat_algebra D.R (Sec D.s U.1) D.I D.κ`.
-/
theorem exists_dp (D : Data) (U : D.X.affineOpens) :
    ∃ δ : DividedPowers (ext D U), IsDPMorphism D.κ δ (algebraMap D.R (Sec D.s U.1)) := by
  haveI := D.sec_smooth U
  exact GlobalTheory.T.exists_isDPMorphism_of_flat_algebra D.R (Sec D.s U.1) D.I D.κ

/- English proof (translation)
Introduce `D`. Use `choose δ hδ using exists_dp D`. Use `choose x hx hw using exists_pt D`. Use `haveI := D.mono_i`. Set `T : D.X.affineOpens → Thick D.κ D.t` to `fun U ↦ { B := Sec D.s U.1 J := ext D U δ := δ U nil := isPDNilpotent_map _ (hδ U) D.nil dp := hδ U B₀ := Sec D.s U.1 ⧸ ext D U π := Ideal.Quotient.mk _ surj := Ideal.Quotient.mk_surjective ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem x := x U w := hw U }`.

Set `m : ∀ {U V : D.X.affineOpens}, V.1 ≤ U.1 → (T U ⟶ T V)` to `fun {U V} h ↦ { φ := Sec.res D.s h φ₀ := Ideal.quotientMap (ext D V) (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1) (Ideal.map_le_iff_le_comap.1 (isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)).1) comm := fun _ ↦ rfl dp := isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h) pt := …`. Rewrite using `[← cancel_mono D.i, Category.assoc]`. Express the relevant statement in the definitionally equal form `spMap _ ≫ x U ≫ D.i = x V ≫ D.i`. Rewrite using `[hx, hx, ← affPt_res D.s h, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]`. Use `rfl }`.

Use `⟨{ L := { obj := fun U ↦ T U.unop map := fun a ↦ m (leOfHom a.unop) map_id := fun U ↦ Thick.hom_ext fun b ↦ mp_id (OAff D.s) U b map_comp := fun a b ↦ Thick.hom_ext fun c ↦ mp_comp (OAff D.s) a b c } e := fun _ ↦ AlgEquiv.refl nat := fun _ _ ↦ rfl gen := fun _ ↦ rfl pt := fun U ↦ …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `⊤ ≤ (x U.unop ≫ D.i) ⁻¹ᵁ U.unop.1`. Rewrite using `[hx, Scheme.Hom.comp_preimage]`. Establish `: affPt D.s U.unop ⁻¹ᵁ U.unop.1 = ⊤` using `U.unop.2.fromSpec_preimage_self`. Rewrite using `[this]`.

Conclude with `le_rfl`.
-/
theorem nonempty_lift : ∀ D : Data, Nonempty (Lift D) := by
  intro D
  choose δ hδ using exists_dp D
  choose x hx hw using exists_pt D
  haveI := D.mono_i
  let T : D.X.affineOpens → Thick D.κ D.t := fun U ↦
    { B := Sec D.s U.1
      J := ext D U
      δ := δ U
      nil := isPDNilpotent_map _ (hδ U) D.nil
      dp := hδ U
      B₀ := Sec D.s U.1 ⧸ ext D U
      π := Ideal.Quotient.mk _
      surj := Ideal.Quotient.mk_surjective
      ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
      x := x U
      w := hw U }
  let m : ∀ {U V : D.X.affineOpens}, V.1 ≤ U.1 → (T U ⟶ T V) := fun {U V} h ↦
    { φ := Sec.res D.s h
      φ₀ := Ideal.quotientMap (ext D V) (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1)
        (Ideal.map_le_iff_le_comap.1 (isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)).1)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)
      pt := by
        rw [← cancel_mono D.i, Category.assoc]
        change spMap _ ≫ x U ≫ D.i = x V ≫ D.i
        rw [hx, hx, ← affPt_res D.s h, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
        rfl }
  refine ⟨{ L := { obj := fun U ↦ T U.unop
                   map := fun a ↦ m (leOfHom a.unop)
                   map_id := fun U ↦ Thick.hom_ext fun b ↦ mp_id (OAff D.s) U b
                   map_comp := fun a b ↦ Thick.hom_ext fun c ↦ mp_comp (OAff D.s) a b c }
            e := fun _ ↦ AlgEquiv.refl
            nat := fun _ _ ↦ rfl
            gen := fun _ ↦ rfl
            pt := fun U ↦ (hx U.unop).symm
            mem := fun U ↦ ?_ }⟩
  change ⊤ ≤ (x U.unop ≫ D.i) ⁻¹ᵁ U.unop.1
  rw [hx, Scheme.Hom.comp_preimage]
  have : affPt D.s U.unop ⁻¹ᵁ U.unop.1 = ⊤ := U.unop.2.fromSpec_preimage_self
  rw [this]
  exact le_rfl

end GlobalTheory.SmoothLift.LiftEx
