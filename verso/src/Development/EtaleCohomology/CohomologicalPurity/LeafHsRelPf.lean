import Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfMono

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

/- English proof (translation)
Take `⟨x, rfl⟩` from `x.mk_surjective`. Use `congrArg CohomologyClass.mk (Cocycle.ext ?_)` and prove the remaining obligations. Simplify using `[zcomp, Cochain.ofHom_comp]`.
-/
theorem hk_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

/- English proof (translation)
Substitute `ha` using the available equality. Substitute `hb` using the available equality. Both sides reduce to the same expression.
-/
theorem cone_map_congr {R : Type} [CommRing R] {K₁ L₁ K₂ L₂ : Cx R} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (h : f₁ ≫ b = a ≫ f₂) (h' : f₁ ≫ b' = a' ≫ f₂) (ha : a = a') (hb : b = b') :
    mappingCone.map f₁ f₂ a b h = mappingCone.map f₁ f₂ a' b' h' := by
  subst ha; subst hb; rfl

/- English proof (translation)
Rewrite using `[← Functor.map_comp, ← Functor.map_comp]`. Conclude with `congrArg (chains R).map pushout.condition`.
-/
theorem dbl_sq (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map P.hom ≫ (chains R).map (dbl.inl P) = (chains R).map P.hom ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map pushout.condition

def dblCone (R : Type) [CommRing R] (P : Arrow Spc) :
    mappingCone ((chains R).map P.hom) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map P.hom) ((chains R).map (dbl.inl P)) (dbl_sq R P)

/- English proof (translation)
Rewrite using `[← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]`.
-/
theorem dblMap_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map (dbl.inr P') ≫ (chains R).map (dbl.map φ) = (chains R).map φ.right ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]

def dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone ((chains R).map (dbl.inr P')) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map φ.right) ((chains R).map (dbl.map φ)) (dblMap_sq R φ)

/- English proof (translation)
Unfold `coneMap dblCone dblConeMap`. Rewrite using `[← mappingCone.map_comp, ← mappingCone.map_comp]`. Apply `cone_map_congr` to reduce the goal to its premises. Rewrite using `[← Functor.map_comp, ← Functor.map_comp]`. Conclude with `congrArg (chains R).map (Arrow.w φ)`.

Rewrite using `[← Functor.map_comp, ← Functor.map_comp, inl_map]`.
-/
theorem dblCone_nat (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    coneMap R φ ≫ dblCone R P = dblCone R P' ≫ dblConeMap R φ := by
  unfold coneMap dblCone dblConeMap
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  apply cone_map_congr
  · rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ)
  · rw [← Functor.map_comp, ← Functor.map_comp, inl_map]

/- English proof (translation)
Simplify using `[dblConeMap, mappingCone.map]`.
-/
theorem inr_dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone.inr _ ≫ dblConeMap R φ = (chains R).map (dbl.map φ) ≫ mappingCone.inr _ := by
  simp [dblConeMap, mappingCone.map]

def LeafDblConeQI : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → QuasiIso (dblCone R P)

def LeafConeSplit : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (g : K ⟶ L) (r : L ⟶ K), g ≫ r = 𝟙 K →
  ∀ (F : Shv R) (n : ℤ), Function.Injective (HK.pull R (mappingCone.inr g) F n) ∧
    ∀ y : HK R L F n, HK.pull R g F n y = 0 ↔ ∃ x, HK.pull R (mappingCone.inr g) F n x = y

/- English proof (translation)
Rewrite using `[← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]`.
-/
theorem inr_fold_chains (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map (dbl.inr P) ≫ (chains R).map (dbl.fold P) = 𝟙 _ := by
  rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]

def psi (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) :
    HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n).codRestrict _ fun x =>
    ((hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n).2 _).2 ⟨x, rfl⟩

/- English proof (translation)
Establish `h` using `hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n`. Use `⟨fun a b hab => h.1 (congrArg Subtype.val hab), fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `(h.2 y.1).1 y.2`. Conclude with `⟨x, Subtype.ext hx⟩`.
-/
theorem psi_bij (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) : Function.Bijective (psi q P n i hS) := by
  have h := hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n
  refine ⟨fun a b hab => h.1 (congrArg Subtype.val hab), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (h.2 y.1).1 y.2
  exact ⟨x, Subtype.ext hx⟩

/- English proof (translation)
Introduce `h1 q i`. Set `θ : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom → (HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hrel (ZMod q) P.hom (tw q i) n)` to `fun P n h => by haveI := hD (ZMod q) P h`. Conclude with `AddEquiv.ofBijective (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n) (h1 (ZMod q) _ (tw q i) n)`. Use `⟨fun P n h => (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm.trans (θ P n h), ?_⟩` and prove the remaining obligations. Introduce `P' P φ h' h n x`.

Establish `key : (AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x) = HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x)`. Rewrite using `[AddEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `set y := (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x with hy`. Establish `hx : x = psi q P n i hS y`.

Rewrite using `[hy]`. Conclude with `((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).apply_symm_apply x).symm`. Rewrite using `[hx]`. Express the relevant statement in the definitionally equal form `HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n y) = HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n (HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n y)`. Rewrite using `[← hk_pull_comp, ← hk_pull_comp, inr_dblConeMap]`.

Express the relevant statement in the definitionally equal form `HK.pull (ZMod q) (dblCone (ZMod q) P') (tw q i) n ((AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x)) = HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n ((AddEquiv.ofBijective (psi q P n i hS) …`. Rewrite using `[key, ← hk_pull_comp, ← hk_pull_comp, dblCone_nat]`.
-/
theorem leafHsRel_of (hD : LeafDblConeQI) (hS : LeafConeSplit) : LeafHsRel := by
  intro h1 q i
  let θ : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
      (HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hrel (ZMod q) P.hom (tw q i) n) :=
    fun P n h => by
      haveI := hD (ZMod q) P h
      exact AddEquiv.ofBijective (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n) (h1 (ZMod q) _ (tw q i) n)
  refine ⟨fun P n h => (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm.trans (θ P n h), ?_⟩
  intro P' P φ h' h n x
  have key : (AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x) =
      HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n
        ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x) := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    set y := (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x with hy
    have hx : x = psi q P n i hS y := by
      rw [hy]; exact ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).apply_symm_apply x).symm
    rw [hx]
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
        (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n y) =
      HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n (HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n y)
    rw [← hk_pull_comp, ← hk_pull_comp, inr_dblConeMap]
  change HK.pull (ZMod q) (dblCone (ZMod q) P') (tw q i) n
      ((AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x)) =
    HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n
      ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x))
  rw [key, ← hk_pull_comp, ← hk_pull_comp, dblCone_nat]

end LateralTheory.CohomologicalPurity.Thom.ExcSp
