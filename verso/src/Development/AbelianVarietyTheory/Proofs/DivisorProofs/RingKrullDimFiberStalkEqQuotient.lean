import Mathlib

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibreStalk

/- English proof (translation)
Rewrite using `[← B.residueFieldCongr_fromSpecResidueField h, Spec.map_comp, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem fromSpecResidueField_eq {B : Scheme.{0}} {x b : B} (h : x = b) :
    B.fromSpecResidueField b =
      Spec.map (B.residue x ≫ (B.residueFieldCongr h).hom) ≫ B.fromSpecStalk x := by
  rw [← B.residueFieldCongr_fromSpecResidueField h, Spec.map_comp, Category.assoc]
  rfl

/- English proof (translation)
Use `(π.range_fiberι b).le ⟨z, rfl⟩` as an intermediate fact. Simplify using `using this`.
-/
theorem image_eq (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) : π (π.fiberι b z) = b := by
  have := (π.range_fiberι b).le ⟨z, rfl⟩
  simpa using this

/- English proof (translation)
Establish `h'` using `image_eq B Y π b z`. Establish `hA` using `fromSpecResidueField_eq h'`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Set `y` to `π.fiberι b z`.

Set `S` to `Y.presheaf.stalk y`. Set `I` to `(IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom`. Establish `hIm : I ≤ IsLocalRing.maximalIdeal S` using `Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (π.stalkMap y).hom r hr`. Establish `: Nontrivial (S ⧸ I)` using `Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hIm)`. Establish `: IsLocalRing (S ⧸ I)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`.

Establish `hl : IsLocalHom (Ideal.Quotient.mk I)` using `IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective`. Set `L : B.residueField (π y) ⟶ CommRingCat.of (S ⧸ I)` to `CommRingCat.ofHom (Ideal.Quotient.lift (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))) ((Ideal.Quotient.mk I).comp (π.stalkMap y).hom) (fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)))`. Establish `hres : B.residue (π y) ≫ L = π.stalkMap y ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)`. Use extensionality with `r`. Both sides reduce to the same expression.

Set `g : Spec (CommRingCat.of (S ⧸ I)) ⟶ Y` to `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Y.fromSpecStalk y`. Set `t : Spec (CommRingCat.of (S ⧸ I)) ⟶ Spec (B.residueField b)` to `Spec.map ((B.residueFieldCongr h').inv ≫ L)`. Establish `w : g ≫ π = t ≫ B.fromSpecResidueField b`. Rewrite using `[hA, ← Category.assoc, ← Spec.map_comp]`. Simplify using `only [Category.assoc, Iso.hom_inv_id_assoc, g]`.

Rewrite using `[hres]`. Use `first`. Consider the case `(rw [Spec.map_comp (π.stalkMap y) (CommRingCat.ofHom (Ideal.Quotient.mk I)), Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk])`. Consider the case `(erw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk])`. Apply the tactic sequence `all_goals rfl`.

Set `ℓ : Spec (CommRingCat.of (S ⧸ I)) ⟶ π.fiber b` to `Limits.pullback.lift g t w`. Establish `hℓ : ℓ ≫ π.fiberι b = g` using `Limits.pullback.lift_fst _ _ _`. Establish `e : ℓ (IsLocalRing.closedPoint _) = z`. Apply `(π.fiberι b).isEmbedding.injective` to reduce the goal to its premises. Use `(congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_` and prove the remaining obligations.

Conclude with `(congrArg (Y.fromSpecStalk y) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans Scheme.fromSpecStalk_closedPoint`. Set `ψ` to `(π.fiber b).presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ`. Establish `hψ : (π.fiberι b).stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono (Y.fromSpecStalk y)]`.

Express the relevant statement in the definitionally equal form `_ = g`. Rewrite using `[← hℓ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]`. Establish `hψ'` using `congrArg (fun q => q.hom a) hψ`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'`. Rewrite `hψ'` using `[RingHom.mem_ker.1 ha, map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm`. Take `⟨c, hc⟩` from `Spec.map_surjective ((π.fiber b).fromSpecStalk z ≫ π.fiberToSpecResidueField b)`. Establish `key : π.stalkMap (π.fiberι b z) ≫ (π.fiberι b).stalkMap z = B.residue _ ≫ (B.residueFieldCongr h').hom ≫ c`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono (B.fromSpecStalk (π (π.fiberι b z)))]`.

Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, Scheme.Hom.fiber_fac, ← Category.assoc, ← hc, hA]`. Simplify using `only [Spec.map_comp, Category.assoc]`. Use `Ideal.map_le_iff_le_comap.2 fun r hr => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Use `congrArg (fun q => q.hom r) key` as an intermediate fact.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Rewrite using `[this]`. Establish `: (B.residue (π (π.fiberι b z))).hom r = 0` using `(IsLocalRing.residue_eq_zero_iff r).2 hr`. Rewrite using `[this, map_zero, map_zero]`.
-/
theorem ker_stalkMap_fiberι (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    RingHom.ker ((π.fiberι b).stalkMap z).hom =
      (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
        (π.stalkMap (π.fiberι b z)).hom := by
  have h' := image_eq B Y π b z
  have hA := fromSpecResidueField_eq h'
  apply le_antisymm
  · intro a ha
    let y := π.fiberι b z
    let S := Y.presheaf.stalk y
    let I := (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom
    have hIm : I ≤ IsLocalRing.maximalIdeal S :=
      Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (π.stalkMap y).hom r hr
    have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hIm)
    have : IsLocalRing (S ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let L : B.residueField (π y) ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom
      (Ideal.Quotient.lift (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y)))
        ((Ideal.Quotient.mk I).comp (π.stalkMap y).hom)
        (fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)))
    have hres : B.residue (π y) ≫ L = π.stalkMap y ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      ext r; rfl
    let g : Spec (CommRingCat.of (S ⧸ I)) ⟶ Y := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Y.fromSpecStalk y
    let t : Spec (CommRingCat.of (S ⧸ I)) ⟶ Spec (B.residueField b) := Spec.map ((B.residueFieldCongr h').inv ≫ L)
    have w : g ≫ π = t ≫ B.fromSpecResidueField b := by
      rw [hA, ← Category.assoc, ← Spec.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, g]
      rw [hres]
      first
        | (rw [Spec.map_comp (π.stalkMap y) (CommRingCat.ofHom (Ideal.Quotient.mk I)), Category.assoc,
            Scheme.SpecMap_stalkMap_fromSpecStalk])
        | (erw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk])
      all_goals rfl
    let ℓ : Spec (CommRingCat.of (S ⧸ I)) ⟶ π.fiber b := Limits.pullback.lift g t w
    have hℓ : ℓ ≫ π.fiberι b = g := Limits.pullback.lift_fst _ _ _
    have e : ℓ (IsLocalRing.closedPoint _) = z := by
      apply (π.fiberι b).isEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
      exact (congrArg (Y.fromSpecStalk y) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := (π.fiber b).presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
    have hψ : (π.fiberι b).stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (Y.fromSpecStalk y)]
      change _ = g
      rw [← hℓ, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' := congrArg (fun q => q.hom a) hψ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
    rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
    exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm
  · obtain ⟨c, hc⟩ := Spec.map_surjective ((π.fiber b).fromSpecStalk z ≫ π.fiberToSpecResidueField b)
    have key : π.stalkMap (π.fiberι b z) ≫ (π.fiberι b).stalkMap z =
        B.residue _ ≫ (B.residueFieldCongr h').hom ≫ c := by
      apply Spec.map_injective
      rw [← cancel_mono (B.fromSpecStalk (π (π.fiberι b z)))]
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, Scheme.Hom.fiber_fac, ← Category.assoc, ← hc, hA]
      simp only [Spec.map_comp, Category.assoc]
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun q => q.hom r) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    have : (B.residue (π (π.fiberι b z))).hom r = 0 := (IsLocalRing.residue_eq_zero_iff r).2 hr
    rw [this, map_zero, map_zero]

/- English proof (translation)
Rewrite using `[← ker_stalkMap_fiberι]`. Conclude with `⟨RingHom.quotientKerEquivOfSurjective ((π.fiberι b).stalkMap_surjective z)⟩`.
-/
theorem nonempty_ringEquiv_stalk_fiber (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    Nonempty ((Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) ≃+* (π.fiber b).presheaf.stalk z) := by
  rw [← ker_stalkMap_fiberι]
  exact ⟨RingHom.quotientKerEquivOfSurjective ((π.fiberι b).stalkMap_surjective z)⟩

/- English proof (translation)
Introduce `B Y π b z`. Take `⟨e⟩` from `nonempty_ringEquiv_stalk_fiber B Y π b z`. Conclude with `(ringKrullDim_eq_of_ringEquiv e).symm`.
-/
theorem ringKrullDim_stalk_fiber : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b),
    ringKrullDim ((π.fiber b).presheaf.stalk z) =
      ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) := by
  intro B Y π b z
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_fiber B Y π b z
  exact (ringKrullDim_eq_of_ringEquiv e).symm

end GlobalTheory.FibreStalk
