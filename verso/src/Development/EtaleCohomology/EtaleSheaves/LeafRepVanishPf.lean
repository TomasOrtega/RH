import Development.EtaleCohomology.EtaleSheaves.LeafSupport

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRepVanishPf

variable (R : Type) [CommRing R]

/- English proof (translation)
Establish `: Mono ((freeP R).map φ)`. Rewrite using `[NatTrans.mono_iff_mono_app]`. Introduce `Y`. Rewrite using `[ModuleCat.mono_iff_injective]`. Establish `hi : Function.Injective (φ.app Y)` using `(mono_iff_injective _).1 inferInstance`.

Establish `hu : Function.Injective (uliftFunctor.{1}.map (φ.app Y))`. Introduce `a b h`. Conclude with `ULift.ext _ _ (hi (congrArg ULift.down h))`. Conclude with `Finsupp.mapDomain_injective hu`. Unfold `free`.

Simplify using `only [Functor.comp_map]`. Use `infer_instance`.
-/
theorem free_mono {P Q : PSh} (φ : P ⟶ Q) [Mono φ] : Mono ((free R).map φ) := by
  have : Mono ((freeP R).map φ) := by
    rw [NatTrans.mono_iff_mono_app]
    intro Y
    rw [ModuleCat.mono_iff_injective]
    have hi : Function.Injective (φ.app Y) := (mono_iff_injective _).1 inferInstance
    have hu : Function.Injective (uliftFunctor.{1}.map (φ.app Y)) := by
      intro a b h; exact ULift.ext _ _ (hi (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  unfold free
  simp only [Functor.comp_map]
  infer_instance

/- English proof (translation)
Conclude with `(HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := N) rfl).trans rfl`.
-/
theorem chains_f (E E' : Spc) (f : E ⟶ E') (N : ℕ) :
    ((chains R).map f).f (-(N : ℤ)) = (chainsXIso R E N).hom ≫ (free R).map (f.app (op (SimplexCategory.mk N))) ≫ (chainsXIso R E' N).inv := by
  exact (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := N) rfl).trans rfl

/- English proof (translation)
Establish `e` using `congrArg (fun t => (t.app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x))) (toSheafify_naturality Scheme.etaleTopology ((freeP R).map φ))`. Establish `e2 : (((freeP R).map φ).app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)) = ModuleCat.freeMk (ULift.up.{1} (φ.app _ x))` using `ModuleCat.free_map_apply _ _`. Simplify using `only [NatTrans.comp_app, ModuleCat.hom_comp] at e`. Use `e.symm.trans ?_` and prove the remaining obligations. Conclude with `congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op Y))) e2`.
-/
theorem freeGen_nat {P Q : PSh} (φ : P ⟶ Q) (Y : Scheme.{0}) (x : P.obj (op Y)) :
    (((free R).map φ).hom.app (op Y)).hom (freeGen R P Y x) = freeGen R Q Y (φ.app _ x) := by
  have e := congrArg (fun t => (t.app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map φ))
  have e2 : (((freeP R).map φ).app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)) =
      ModuleCat.freeMk (ULift.up.{1} (φ.app _ x)) := ModuleCat.free_map_apply _ _
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  refine e.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op Y))) e2

/- English proof (translation)
Unfold `ev`. Rewrite using `[Cochain.zero_cochain_comp_v, Cochain.ofHom_v, chains_f]`. Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc]`. Rewrite using `[← freeGen_nat]`. Both sides reduce to the same expression.
-/
theorem ev_pull {U E : Spc} (f : U ⟶ E) {K : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) K n) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y) :
    ev ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add n)) N w h Y y = ev γ N w h Y ((f.app _).app _ y) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, chains_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← freeGen_nat]
  rfl

/- English proof (translation)
Distinguish the cases in `hp : p ≤ 0`. Take `⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ)` from `⟨p.natAbs, by omega⟩`. Rewrite using `[chains_f]`. Use `free_mono R (f.app (op (SimplexCategory.mk N)))` as an intermediate fact. Use `infer_instance`.

Establish `hz : IsZero (((chains R).obj U).X p)` using `HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by`. Express the relevant statement in the definitionally equal form `-(i : ℤ) = p at hi`. Use the proof step `omega)`. Conclude with `⟨fun a b _ => hz.eq_of_tgt a b⟩`.
-/
theorem chains_mono {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) : Mono (((chains R).map f).f p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    rw [chains_f]
    have := free_mono R (f.app (op (SimplexCategory.mk N)))
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change -(i : ℤ) = p at hi; omega)
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩

/- English proof (translation)
Introduce `R _ U E f hf F n a ha`. Take `⟨α, rfl⟩` from `CohomologyClass.mk_surjective a`. Establish `hg` using `chains_mono R f`. Establish `hinj : ∀ q, Injective ((res R F).X q)` using `fun q => (inferInstance : Injective ((injectiveResolution F).cochainComplex.X q))`. Establish `h1 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0` using `ha`.

Rewrite `h1` using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Take `⟨β', hβ'⟩` from `h1`. Set `β : Cochain ((chains R).obj E) (res R F) (n - 1)` to `Cochain.mk fun p q hpq => Injective.factorThru (β'.v p q hpq) (((chains R).map f).f p)`. Establish `hβ : (Cochain.ofHom ((chains R).map f)).comp β (zero_add _) = β'`. Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations.

Rewrite using `[Cochain.zero_cochain_comp_v, Cochain.ofHom_v]`. Simplify using `only [β, Cochain.mk_v]`. Conclude with `Injective.comp_factorThru _ _`. Set `b : Cocycle ((chains R).obj E) (res R F) n` to `Cocycle.mk (δ (n - 1) n β) (n + 1) rfl (δ_δ _ _ _ _)`. Use `⟨α - b, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[CohomologyClass.mk_sub, (CohomologyClass.mk_eq_zero_iff b).2 ((mem_coboundaries_iff b (n - 1) (by omega)).2 ⟨β, rfl⟩), sub_zero]`. Introduce `N w h Y y`. Rewrite using `[← ev_pull]`. Establish `e : (Cochain.ofHom ((chains R).map f)).comp (α - b).1 (zero_add n) = 0`. Rewrite using `[Cocycle.coe_sub, Cochain.comp_sub]`.

Establish `: (Cochain.ofHom ((chains R).map f)).comp (b : Cochain _ _ n) (zero_add n) = δ (n - 1) n β'`. Rewrite using `[← hβ]`. Simplify using `[b]`. Rewrite using `[this, hβ']`. Simplify using `[zcomp]`.

Rewrite using `[e]`. Simplify using `[ev]`.
-/
theorem LeafRepVanish_of : LateralTheory.E.LeafA6suppPf.LeafRepVanish := by
  intro R _ U E f hf F n a ha
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  have hg := chains_mono R f
  have hinj : ∀ q, Injective ((res R F).X q) := fun q =>
    (inferInstance : Injective ((injectiveResolution F).cochainComplex.X q))
  have h1 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 := ha
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨β', hβ'⟩ := h1
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.mk fun p q hpq => Injective.factorThru (β'.v p q hpq) (((chains R).map f).f p)
  have hβ : (Cochain.ofHom ((chains R).map f)).comp β (zero_add _) = β' := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    simp only [β, Cochain.mk_v]
    exact Injective.comp_factorThru _ _
  let b : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - b, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, (CohomologyClass.mk_eq_zero_iff b).2
      ((mem_coboundaries_iff b (n - 1) (by omega)).2 ⟨β, rfl⟩), sub_zero]
  · intro N w h Y y
    rw [← ev_pull]
    have e : (Cochain.ofHom ((chains R).map f)).comp (α - b).1 (zero_add n) = 0 := by
      rw [Cocycle.coe_sub, Cochain.comp_sub]
      have : (Cochain.ofHom ((chains R).map f)).comp (b : Cochain _ _ n) (zero_add n) = δ (n - 1) n β' := by
        rw [← hβ]; simp [b]
      rw [this, hβ']
      simp [zcomp]
    rw [e]
    simp [ev]

end LateralTheory.E.LeafRepVanishPf
