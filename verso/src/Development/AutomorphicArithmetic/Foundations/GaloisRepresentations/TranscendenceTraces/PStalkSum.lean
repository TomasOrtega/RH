import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `: RingHomSurjective (e : R →+* S)` using `⟨e.surjective⟩`. Set `f : R →ₛₗ[(e : R →+* S)] S` to `{ toFun := e map_add' := e.map_add map_smul' := fun a b => by simp [smul_eq_mul] }`. Rewrite using `[Module.length, Module.length, WithBot.unbot_inj]`. Conclude with `Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)`.
-/
private theorem length_congr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)

/- English proof (translation)
Introduce `hC hA V Ω _ _ r _`. Take `⟨B, _, _, v, hfin, hpb⟩` from `hC r Ω (𝟙 (gp Ω))`. Establish `hv : IsIso v` using `hpb.isIso_fst_of_isIso`. Establish `hr : r = inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B))`. Rewrite using `[IsIso.eq_inv_comp, hpb.w, Category.comp_id]`.

Establish `hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω B)))`. Rewrite using `[Flat.SpecMap_iff]`. Simplify `(inferInstance : Module.Flat Ω B)` using `[RingHom.flat_algebraMap_iff]`. Establish `hfi : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Ω B)))`. Rewrite using `[IsFinite.SpecMap_iff]`.

Simplify `hfin` using `[RingHom.finite_algebraMap]`. Establish `hR : Scheme.Hom.finrank r (IsLocalRing.closedPoint Ω) = Module.finrank Ω B`. Rewrite using `[hr, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]`. Both sides reduce to the same expression. Establish `hs : ∀ P : PrimeSpectrum B, IsIso (v.stalkMap P)` using `(IsOpenImmersion.iff_isIso_stalkMap (f := v)).mp inferInstance |>.2`.

Establish `e2 : ∀ P : PrimeSpectrum B, V.presheaf.stalk (v P) ≃+* Localization.AtPrime P.asIdeal` using `fun P => ((asIso (v.stalkMap P)) ≪≫ Spec.stalkIso (CommRingCat.of B) P).commRingCatIsoToRingEquiv`. Rewrite using `[hR, ← hA Ω B, ← finsum_comp_equiv v.homeomorph.toEquiv]`. Use `finsum_congr fun P => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Module.length (V.presheaf.stalk (v P)) (V.presheaf.stalk (v P))).toNat = _`. Rewrite using `[length_congr (e2 P)]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.stalkSum_of :
    Chart → ArtSum → StalkSum := by
  intro hC hA V Ω _ _ r _
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 (gp Ω))
  have hv : IsIso v := hpb.isIso_fst_of_isIso
  have hr : r = inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    rw [IsIso.eq_inv_comp, hpb.w, Category.comp_id]
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [Flat.SpecMap_iff]
    simpa [RingHom.flat_algebraMap_iff] using (inferInstance : Module.Flat Ω B)
  have hfi : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [IsFinite.SpecMap_iff]
    simpa [RingHom.finite_algebraMap] using hfin
  have hR : Scheme.Hom.finrank r (IsLocalRing.closedPoint Ω) = Module.finrank Ω B := by
    rw [hr, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hs : ∀ P : PrimeSpectrum B, IsIso (v.stalkMap P) :=
    (IsOpenImmersion.iff_isIso_stalkMap (f := v)).mp inferInstance |>.2
  have e2 : ∀ P : PrimeSpectrum B,
      V.presheaf.stalk (v P) ≃+* Localization.AtPrime P.asIdeal := fun P =>
    ((asIso (v.stalkMap P)) ≪≫ Spec.stalkIso (CommRingCat.of B) P).commRingCatIsoToRingEquiv
  rw [hR, ← hA Ω B, ← finsum_comp_equiv v.homeomorph.toEquiv]
  refine finsum_congr fun P => ?_
  change (Module.length (V.presheaf.stalk (v P)) (V.presheaf.stalk (v P))).toNat = _
  rw [length_congr (e2 P)]
