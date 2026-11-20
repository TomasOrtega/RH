import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MemMaxUnramifiedOutsideOfMemLevelOfField
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal
  FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

omit [FiniteDimensional K.1 L] in

/- English proof (translation)
Take `⟨N, hKN, hgal, hNS, hyN⟩` from `exists_galois_level S (y : maxUnramifiedOutside K.1 ℚ̄ S).2`. Use `hKN` as an intermediate fact. Establish `: Normal K.1 N.1` using `hgal.to_normal`. Set `gN : N.1 ≃ₐ[K.1] N.1` to `x'.restrictNormal' N.1`. Establish `hgN : ∀ z : N.1, ((gN z : N.1) : ℚ̄) = x' z` using `fun z => AlgHom.restrictNormal_commutes x' N.1 z`.

Establish `hw` using `placeOfEmbedding_eq_inv_smul ι gN (ι.comp x') fun z => by`. Rewrite using `[AlgHom.comp_apply, hgN]`. Establish `hmem : ((maxUnitsToUnits S (galUnitsHom K.1 _ x y) : ℚ̄ˣ) : ℚ̄) ∈ N.1`. Express the relevant statement in the definitionally equal form `((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1`. Rewrite using `[← hx', ← hgN ⟨_, hyN⟩]`.

Conclude with `(gN _).2`. Establish `e1` using `valuation_placeOfEmbedding_eq S ι hv N hNS _ hmem`. Establish `e2` using `valuation_placeOfEmbedding_eq S (ι.comp x') hv N hNS (maxUnitsToUnits S y) hyN`. Rewrite `e2` using `[hw, valuation_inv_smul_placesOver]`. Establish `key : (placeOfEmbedding ι N).1.valuation N.1 ⟨_, hmem⟩ = (placeOfEmbedding ι N).1.valuation N.1 (gN ⟨_, hyN⟩)`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = ((gN ⟨_, hyN⟩ : N.1) : ℚ̄)`. Rewrite using `[hgN, hx']`. Use `WithZero.exp_injective (e1.symm.trans (key.trans e2))` as an intermediate fact.

Rewrite using `[ordEmb_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordEmb_galUnitsHom_eq {v : HeightOneSpectrum (𝓞 K.1)}
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)
    (x : galUnramifiedOutside K.1 ℚ̄ S) (x' : ℚ̄ →ₐ[K.1] ℚ̄)
    (hx' : ∀ z : maxUnramifiedOutside K.1 ℚ̄ S, x' z = ((x z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄))
    (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ordEmb S ι hv (Additive.ofMul (galUnitsHom K.1 _ x y)) = ordEmbFun (ι.comp x') (maxUnitsToUnits S y) := by
  obtain ⟨N, hKN, hgal, hNS, hyN⟩ := exists_galois_level S (y : maxUnramifiedOutside K.1 ℚ̄ S).2
  have := hKN
  have : Normal K.1 N.1 := hgal.to_normal
  let gN : N.1 ≃ₐ[K.1] N.1 := x'.restrictNormal' N.1
  have hgN : ∀ z : N.1, ((gN z : N.1) : ℚ̄) = x' z := fun z => AlgHom.restrictNormal_commutes x' N.1 z
  have hw := placeOfEmbedding_eq_inv_smul ι gN (ι.comp x') fun z => by
    rw [AlgHom.comp_apply, hgN]
  have hmem : ((maxUnitsToUnits S (galUnitsHom K.1 _ x y) : ℚ̄ˣ) : ℚ̄) ∈ N.1 := by
    change ((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1
    rw [← hx', ← hgN ⟨_, hyN⟩]
    exact (gN _).2
  have e1 := valuation_placeOfEmbedding_eq S ι hv N hNS _ hmem
  have e2 := valuation_placeOfEmbedding_eq S (ι.comp x') hv N hNS (maxUnitsToUnits S y) hyN
  rw [hw, valuation_inv_smul_placesOver] at e2
  have key : (placeOfEmbedding ι N).1.valuation N.1 ⟨_, hmem⟩ =
      (placeOfEmbedding ι N).1.valuation N.1 (gN ⟨_, hyN⟩) := by
    congr 1
    apply Subtype.ext
    change ((x (y : maxUnramifiedOutside K.1 ℚ̄ S) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
      ((gN ⟨_, hyN⟩ : N.1) : ℚ̄)
    rw [hgN, hx']
  have := WithZero.exp_injective (e1.symm.trans (key.trans e2))
  rw [ordEmb_apply]
  omega

omit [FiniteDimensional K.1 L] in

/- English proof (translation)
The claim follows from `(eq_placeOfEmbedding ι₁ F (completionEmbedding ι₂ F) fun z => by rw [completionEmbedding_algebraMap] exact (h z).symm).symm`.
-/
theorem placeOfEmbedding_congr_of_eqOn {v : HeightOneSpectrum (𝓞 K.1)} (F : FiniteSubfield) [Fact (K ≤ F)]
    (ι₁ ι₂ : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (h : ∀ z : F.1, ι₁ z = ι₂ z) :
    placeOfEmbedding ι₁ F = placeOfEmbedding ι₂ F :=
  (eq_placeOfEmbedding ι₁ F (completionEmbedding ι₂ F) fun z => by
    rw [completionEmbedding_algebraMap]
    exact (h z).symm).symm

omit [FiniteDimensional K.1 L] in

/- English proof (translation)
Establish `key : ∀ w : PlacesOver F.1 v, w = placeOfEmbedding ι₁ F → ∃ c : w.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1), ∀ z : F.1, c (algebraMap F.1 _ z) = ι₁ z`. Introduce and unpack `w rfl`. Conclude with `⟨completionEmbedding ι₁ F, completionEmbedding_algebraMap ι₁ F⟩`. Take `⟨c₁, hc₁⟩` from `key (placeOfEmbedding ι₂ F) h.symm`. Use `finiteDimensional_adicCompletion_placesOver (K := K) (E := F) (placeOfEmbedding ι₂ F)` as an intermediate fact.

Set `c₂` to `completionEmbedding ι₂ F`. Set `: Algebra ((placeOfEmbedding ι₂ F).1.adicCompletion F.1) (AlgebraicClosure (v.adicCompletion K.1))` to `c₂.toRingHom.toAlgebra`. Establish `: IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι₂ F).1.adicCompletion F.1) (AlgebraicClosure (v.adicCompletion K.1))` using `IsScalarTower.of_algebraMap_eq fun a => (c₂.commutes a).symm`. Establish `: Algebra.IsAlgebraic ((placeOfEmbedding ι₂ F).1.adicCompletion F.1) (AlgebraicClosure (v.adicCompletion K.1))` using `Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _`. Take `⟨φ, hφ⟩` from `IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := v.adicCompletion K.1) (L := (placeOfEmbedding ι₂ F).1.adicCompletion F.1) (M := AlgebraicClosure (v.adicCompletion K.1)) (E := AlgebraicClosure (v.adicCompletion K.1)) c₁`.

Use `⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.ofBijective_apply]`. Establish `e` using `DFunLike.congr_fun hφ (algebraMap F.1 _ z)`. Express the relevant statement in the definitionally equal form `φ (c₂ (algebraMap F.1 _ z)) = c₁ (algebraMap F.1 _ z) at e`. Rewrite using `[← hc₁, ← e, completionEmbedding_algebraMap]`.
-/
theorem exists_algEquiv_of_placeOfEmbedding_eq {v : HeightOneSpectrum (𝓞 K.1)} (F : FiniteSubfield)
    [Fact (K ≤ F)] (ι₁ ι₂ : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (h : placeOfEmbedding ι₁ F = placeOfEmbedding ι₂ F) :
    ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      ∀ z : F.1, ι₁ z = σ (ι₂ z) := by
  have key : ∀ w : PlacesOver F.1 v, w = placeOfEmbedding ι₁ F →
      ∃ c : w.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1),
        ∀ z : F.1, c (algebraMap F.1 _ z) = ι₁ z := by
    rintro w rfl
    exact ⟨completionEmbedding ι₁ F, completionEmbedding_algebraMap ι₁ F⟩
  obtain ⟨c₁, hc₁⟩ := key (placeOfEmbedding ι₂ F) h.symm
  have := finiteDimensional_adicCompletion_placesOver (K := K) (E := F) (placeOfEmbedding ι₂ F)
  let c₂ := completionEmbedding ι₂ F
  let : Algebra ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) := c₂.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c₂.commutes a).symm
  have : Algebra.IsAlgebraic ((placeOfEmbedding ι₂ F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := v.adicCompletion K.1)
    (L := (placeOfEmbedding ι₂ F).1.adicCompletion F.1) (M := AlgebraicClosure (v.adicCompletion K.1))
    (E := AlgebraicClosure (v.adicCompletion K.1)) c₁
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun z => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  have e := DFunLike.congr_fun hφ (algebraMap F.1 _ z)
  change φ (c₂ (algebraMap F.1 _ z)) = c₁ (algebraMap F.1 _ z) at e
  rw [← hc₁, ← e, completionEmbedding_algebraMap]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hvv : v' = v`. Establish `h1` using `(placeOfEmbedding ((ιs.fin v').comp x') (levelOfField L)).2`. Establish `h2` using `(placeOfEmbedding (ιs.fin v) (levelOfField L)).2`.

Rewrite `h1` using `[h]`. Conclude with `HeightOneSpectrum.ext (h1.over.trans h2.over.symm)`. Substitute `hvv` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `exists_algEquiv_of_placeOfEmbedding_eq (levelOfField L) ((ιs.fin v').comp x') (ιs.fin v') (Subtype.ext h)`.

Use `⟨decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ, ⟨σ, rfl⟩, (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ)⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `w hw`. Establish `hxw : x w = decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w`. Apply `Subtype.val_injective` to reduce the goal to its premises.

Apply `(ιs.fin v').injective` to reduce the goal to its premises. Establish `h1` using `hσ ⟨(w : ℚ̄), (mem_levelOfField L).2 ⟨w, hw, rfl⟩⟩`. Establish `h2` using `decompHom_apply (Kv := v'.adicCompletion K.1) ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w`. Express the relevant statement in the definitionally equal form `(ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄)) at h1`. Rewrite `h1` using `[hx']`.

Express the relevant statement in the definitionally equal form `(ιs.fin v') ((x w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = (ιs.fin v') ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)`. Rewrite using `[h1]`. Conclude with `h2.symm`. Rewrite using `[AlgEquiv.mul_apply, hxw, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]`. Introduce and unpack `⟨rfl, z, ⟨σ, rfl⟩, u, hu, rfl⟩`.

Use `congrArg Subtype.val ?_` and prove the remaining obligations. Rewrite using `[← placeOfEmbedding_comp_algEquiv (ιs.fin v') σ]`. Apply `placeOfEmbedding_congr_of_eqOn` to reduce the goal to its premises. Introduce and unpack `⟨zz, hzz⟩`. Take `⟨w, hw, rfl⟩` from `(mem_levelOfField L).1 hzz`.

Express the relevant statement in the definitionally equal form `(ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄))`. Establish `e1 : (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ * u) w = decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ (u w)` using `AlgEquiv.mul_apply _ _ w`. Establish `e2 : u w = w` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hu w hw`. Establish `e3 : x' (w : ℚ̄) = ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)` using `(hx' w).trans (congrArg Subtype.val (e1.trans (congrArg _ e2)))`. Conclude with `(congrArg (ιs.fin v') e3).trans (decompHom_apply (Kv := v'.adicCompletion K.1) ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w)`.
-/
theorem placeOfEmbedding_comp_eq_iff [Normal K.1 L] (ιs : LocalEmbeddings K)
    (v v' : HeightOneSpectrum (𝓞 K.1)) (x : galUnramifiedOutside K.1 ℚ̄ S) (x' : ℚ̄ →ₐ[K.1] ℚ̄)
    (hx' : ∀ z : maxUnramifiedOutside K.1 ℚ̄ S, x' z = ((x z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) :
    (placeOfEmbedding ((ιs.fin v').comp x') (levelOfField L)).1 =
        (placeOfEmbedding (ιs.fin v) (levelOfField L)).1 ↔
      v' = v ∧ ∃ z ∈ (decompHomS (v.adicCompletion K.1) S (ιs.fin v)).range,
        ∃ u ∈ L.fixingSubgroup, x = z * u := by
  constructor
  · intro h
    have hvv : v' = v := by
      have h1 := (placeOfEmbedding ((ιs.fin v').comp x') (levelOfField L)).2
      have h2 := (placeOfEmbedding (ιs.fin v) (levelOfField L)).2
      rw [h] at h1
      exact HeightOneSpectrum.ext (h1.over.trans h2.over.symm)
    subst hvv
    refine ⟨rfl, ?_⟩
    obtain ⟨σ, hσ⟩ := exists_algEquiv_of_placeOfEmbedding_eq (levelOfField L) ((ιs.fin v').comp x')
      (ιs.fin v') (Subtype.ext h)
    refine ⟨decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ, ⟨σ, rfl⟩,
      (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ)⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro w hw
    have hxw : x w = decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w := by
      apply Subtype.val_injective
      apply (ιs.fin v').injective
      have h1 := hσ ⟨(w : ℚ̄), (mem_levelOfField L).2 ⟨w, hw, rfl⟩⟩
      have h2 := decompHom_apply (Kv := v'.adicCompletion K.1)
        ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w
      change (ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄)) at h1
      rw [hx'] at h1
      change (ιs.fin v') ((x w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
        (ιs.fin v') ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
      rw [h1]
      exact h2.symm
    rw [AlgEquiv.mul_apply, hxw, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · rintro ⟨rfl, z, ⟨σ, rfl⟩, u, hu, rfl⟩
    refine congrArg Subtype.val ?_
    rw [← placeOfEmbedding_comp_algEquiv (ιs.fin v') σ]
    apply placeOfEmbedding_congr_of_eqOn
    rintro ⟨zz, hzz⟩
    obtain ⟨w, hw, rfl⟩ := (mem_levelOfField L).1 hzz
    change (ιs.fin v') (x' (w : ℚ̄)) = σ ((ιs.fin v') (w : ℚ̄))
    have e1 : (decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ * u) w =
        decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ (u w) :=
      AlgEquiv.mul_apply _ _ w
    have e2 : u w = w := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hu w hw
    have e3 : x' (w : ℚ̄) = ((decompHomS (v'.adicCompletion K.1) S (ιs.fin v') σ w :
        maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
      (hx' w).trans (congrArg Subtype.val (e1.trans (congrArg _ e2)))
    exact (congrArg (ιs.fin v') e3).trans (decompHom_apply (Kv := v'.adicCompletion K.1)
      ((ιs.fin v').comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ w)

end

end PicInf

end GroundTheory.ProfCoh
