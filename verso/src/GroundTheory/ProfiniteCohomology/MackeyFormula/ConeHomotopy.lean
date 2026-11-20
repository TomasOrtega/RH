import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConeMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

namespace mappingCoconeNat

variable {K L K' L' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  {α : K ⟶ K'} {β : L ⟶ L'}

noncomputable def homotopyShiftF (h : Homotopy (f ≫ β) (α ≫ f')) :
    ∀ n, K.X n ⟶ shiftNegOneX L' n
  | 0 => 0
  | n + 1 => h.hom (n + 1) n

noncomputable def mapOfHomotopyF (h : Homotopy (f ≫ β) (α ≫ f')) (n : ℕ) :
    (mappingCoconeNat f).X n ⟶ (mappingCoconeNat f').X n :=
  ModuleCat.ofHom (((α.f n).hom.comp (LinearMap.fst k _ _)).prod
    ((shiftNegOneMapF β n).hom.comp (LinearMap.snd k _ _) -
      (homotopyShiftF h n).hom.comp (LinearMap.fst k _ _)))

/- English proof (translation)
Establish `hβ : ∀ y : shiftNegOneX L n, (shiftNegOneMapF β (n + 1)).hom ((shiftNegOneD L n).hom y) = (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom y)` using `fun y => (hom_apply_hom_apply_eq_of_comp_eq (shiftNegOneMapF_comm β n) y).symm`. Establish `hcomm : ∀ x : K.X n, shiftNegOneSucc L' n ((β.f n).hom ((f.f n).hom x)) = shiftNegOneSucc L' n ((h.hom (n + 1) n).hom ((K.d n (n + 1)).hom x)) - (shiftNegOneD L' n).hom ((homotopyShiftF h n).hom x) + shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom x))` using `fun x => by`. Establish `e` using `congrArg (fun φ => φ.hom x) (h.comm n)`. Simplify using `only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply] at e`. Rewrite using `[shiftNegOneSucc_apply, shiftNegOneSucc_apply, shiftNegOneSucc_apply]`.

Consider the cases of `n with`. Consider the case `zero`. Rewrite `e` using `[Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex]`. Express the relevant statement in the definitionally equal form `(β.f 0).hom ((f.f 0).hom x) = (h.hom 1 0).hom ((K.d 0 1).hom x) - 0 + (f'.f 0).hom ((α.f 0).hom x)`. Rewrite using `[e]`.

Simplify using the standard rewrite rules. Consider the case `succ n`. Rewrite `e` using `[Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]`. Express the relevant statement in the definitionally equal form `(β.f (n + 1)).hom ((f.f (n + 1)).hom x) = (h.hom (n + 1 + 1) (n + 1)).hom ((K.d (n + 1) (n + 1 + 1)).hom x) - -(L'.d n (n + 1)).hom ((h.hom (n + 1) n).hom x) + (f'.f (n + 1)).hom ((α.f (n + 1)).hom x)`. Rewrite using `[e]`.

Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[mappingCoconeNat_d, mappingCoconeNat_d]`. Use `ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `hom_apply_hom_apply_eq_of_comp_eq (α.comm n (n + 1)) p.1`.

Express the relevant statement in the definitionally equal form `shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom p.1)) + (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom p.2 - (homotopyShiftF h n).hom p.1) = (shiftNegOneMapF β (n + 1)).hom (shiftNegOneSucc L n ((f.f n).hom p.1) + (shiftNegOneD L n).hom p.2) - shiftNegOneSucc L' n ((h.hom (n …`. Rewrite using `[map_add, shiftNegOneMapF_succ_apply, hβ, map_sub, hcomm p.1]`. Normalize the expressions using the abelian group laws.
-/
theorem mapOfHomotopyF_comm (h : Homotopy (f ≫ β) (α ≫ f')) (n : ℕ) :
    mapOfHomotopyF h n ≫ (mappingCoconeNat f').d n (n + 1) =
      (mappingCoconeNat f).d n (n + 1) ≫ mapOfHomotopyF h (n + 1) := by
  have hβ : ∀ y : shiftNegOneX L n, (shiftNegOneMapF β (n + 1)).hom ((shiftNegOneD L n).hom y) =
      (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom y) := fun y =>
    (hom_apply_hom_apply_eq_of_comp_eq (shiftNegOneMapF_comm β n) y).symm

  have hcomm : ∀ x : K.X n, shiftNegOneSucc L' n ((β.f n).hom ((f.f n).hom x)) =
      shiftNegOneSucc L' n ((h.hom (n + 1) n).hom ((K.d n (n + 1)).hom x)) -
        (shiftNegOneD L' n).hom ((homotopyShiftF h n).hom x) +
          shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom x)) := fun x => by
    have e := congrArg (fun φ => φ.hom x) (h.comm n)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_add, LinearMap.add_apply] at e
    rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply, shiftNegOneSucc_apply]
    cases n with
    | zero =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex] at e
      change (β.f 0).hom ((f.f 0).hom x) = (h.hom 1 0).hom ((K.d 0 1).hom x) - 0 +
        (f'.f 0).hom ((α.f 0).hom x)
      rw [e]
      simp
    | succ n =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex] at e
      change (β.f (n + 1)).hom ((f.f (n + 1)).hom x) =
        (h.hom (n + 1 + 1) (n + 1)).hom ((K.d (n + 1) (n + 1 + 1)).hom x) -
          -(L'.d n (n + 1)).hom ((h.hom (n + 1) n).hom x) + (f'.f (n + 1)).hom ((α.f (n + 1)).hom x)
      rw [e]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      abel
  rw [mappingCoconeNat_d, mappingCoconeNat_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (α.comm n (n + 1)) p.1
  · change shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom p.1)) +
        (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom p.2 - (homotopyShiftF h n).hom p.1) =
      (shiftNegOneMapF β (n + 1)).hom (shiftNegOneSucc L n ((f.f n).hom p.1) +
        (shiftNegOneD L n).hom p.2) -
          shiftNegOneSucc L' n ((h.hom (n + 1) n).hom ((K.d n (n + 1)).hom p.1))
    rw [map_add, shiftNegOneMapF_succ_apply, hβ, map_sub, hcomm p.1]
    abel

noncomputable def mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f')) :
    mappingCoconeNat f ⟶ mappingCoconeNat f' :=
  CochainComplex.ofHom (mapOfHomotopyF h) (mapOfHomotopyF_comm h)

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) @[reassoc (attr := simp)]`.
-/
theorem mapOfHomotopy_fst (h : Homotopy (f ≫ β) (α ≫ f')) :
    mapOfHomotopy h ≫ fst f' = fst f ≫ α :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
/- English proof (translation)
Use extensionality with `n : 1`. Use `ModuleCat.hom_ext (LinearMap.ext fun y => Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `(α.f n).hom.map_zero`. Express the relevant statement in the definitionally equal form `(shiftNegOneMapF β n).hom y - (homotopyShiftF h n).hom 0 = (shiftNegOneMapF β n).hom y`. Rewrite using `[map_zero, sub_zero]`.
-/
theorem inr_mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f')) :
    inr f ≫ mapOfHomotopy h = shiftNegOneMap β ≫ inr f' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun y => Prod.ext ?_ ?_)
  · exact (α.f n).hom.map_zero
  · change (shiftNegOneMapF β n).hom y - (homotopyShiftF h n).hom 0 = (shiftNegOneMapF β n).hom y
    rw [map_zero, sub_zero]

section FiveLemma

open HomologicalComplex

/- English proof (translation)
Rewrite using `[homologyδ, homologyδ, Category.assoc, ← homologyMap_comp, hinr, homologyMap_comp, shiftNegOneHomologyHom_naturality_assoc]`.
-/
theorem homologyδ_naturality_of_inr (Φ : mappingCoconeNat f ⟶ mappingCoconeNat f')
    (hinr : inr f ≫ Φ = shiftNegOneMap β ≫ inr f') (n : ℕ) :
    homologyδ f n ≫ homologyMap Φ (n + 1) = homologyMap β n ≫ homologyδ f' n := by
  rw [homologyδ, homologyδ, Category.assoc, ← homologyMap_comp, hinr, homologyMap_comp,
    shiftNegOneHomologyHom_naturality_assoc]

/- English proof (translation)
Establish `bα : ∀ m, Function.Bijective (homologyMap α m).hom` using `fun m => by`. Use `hα m` as an intermediate fact. Conclude with `ConcreteCategory.bijective_of_isIso _`. Establish `bβ : ∀ m, Function.Bijective (homologyMap β m).hom` using `fun m => by`. Use `hβ m` as an intermediate fact.

Conclude with `ConcreteCategory.bijective_of_isIso _`. Establish `sfst : ∀ m x, (homologyMap (fst f') m).hom ((homologyMap Φ m).hom x) = (homologyMap α m).hom ((homologyMap (fst f) m).hom x)` using `fun m x => hom_apply_hom_apply_eq_of_comp_eq (by rw [← homologyMap_comp, hfst, homologyMap_comp]) x`. Establish `sδ : ∀ m y, (homologyMap Φ (m + 1)).hom ((homologyδ f m).hom y) = (homologyδ f' m).hom ((homologyMap β m).hom y)` using `fun m y => hom_apply_hom_apply_eq_of_comp_eq (homologyδ_naturality_of_inr Φ hinr m) y`. Establish `sf : ∀ m z, (homologyMap f' m).hom ((homologyMap α m).hom z) = (homologyMap β m).hom ((homologyMap f m).hom z)` using `fun m z => (hom_apply_hom_apply_eq_of_comp_eq (hsq m) z).symm`. Establish `e1` using `fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₁ f m)`.

Establish `e2` using `fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₂ f m)`. Establish `e3` using `fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₃ f m)`. Establish `e1'` using `fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₁ f' m)`. Establish `e2'` using `fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₂ f' m)`. Establish `inj_fst0 : ∀ {K₀ L₀ : CochainComplex (ModuleCat.{u} k) ℕ} (g : K₀ ⟶ L₀), Function.Injective (homologyMap (fst g) 0).hom` using `fun g => by`.

Use `mono_homologyMap_fst_zero g` as an intermediate fact. Conclude with `(ModuleCat.mono_iff_injective _).1 this`. Use `@isIso_of_mono_of_epi _ _ _ _ _ _ ((ModuleCat.mono_iff_injective _).2 ?_) ((ModuleCat.epi_iff_surjective _).2 ?_)` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Consider the cases of `n with`. Consider the case `zero`. Apply `inj_fst0 f` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `(bα 0).1` to reduce the goal to its premises.

Rewrite using `[← sfst, hx, map_zero, map_zero]`. Consider the case `succ m`. Establish `h1 : (homologyMap (fst f) (m + 1)).hom x = 0`. Apply `(bα (m + 1)).1` to reduce the goal to its premises. Rewrite using `[← sfst, hx, map_zero, map_zero]`.

Take `⟨y, rfl⟩` from `e2 m x h1`. Establish `h2 : (homologyδ f' m).hom ((homologyMap β m).hom y) = 0`. Rewrite using `[← sδ]`. Conclude with `hx`. Take `⟨z', hz'⟩` from `e1' m _ h2`.

Take `⟨z, rfl⟩` from `(bα m).2 z'`. Establish `h3 : (homologyMap f m).hom z = y`. Apply `(bβ m).1` to reduce the goal to its premises. Rewrite using `[← sf]`. Conclude with `hz'`.

Express the relevant statement in the definitionally equal form `(homologyδ f m).hom y = 0`. Rewrite using `[← h3]`. Conclude with `hom_apply_hom_apply_of_comp_eq (homologyMap_homologyδ f m) z`. Introduce `y'`. Consider the cases of `n with`.

Consider the case `zero`. Take `⟨w, hw⟩` from `(bα 0).2 ((homologyMap (fst f') 0).hom y')`. Establish `h1 : (homologyMap f 0).hom w = 0`. Apply `(bβ 0).1` to reduce the goal to its premises. Rewrite using `[← sf, hw, map_zero]`.

Conclude with `hom_apply_hom_apply_of_comp_eq (homologyMap_fst_homologyMap f' 0) y'`. Take `⟨x, rfl⟩` from `e3 0 w h1`. Use `⟨x, inj_fst0 f' ?_⟩` and prove the remaining obligations. Rewrite using `[sfst]`. Conclude with `hw`.

Consider the case `succ m`. Take `⟨w, hw⟩` from `(bα (m + 1)).2 ((homologyMap (fst f') (m + 1)).hom y')`. Establish `h1 : (homologyMap f (m + 1)).hom w = 0`. Apply `(bβ (m + 1)).1` to reduce the goal to its premises. Rewrite using `[← sf, hw, map_zero]`.

Conclude with `hom_apply_hom_apply_of_comp_eq (homologyMap_fst_homologyMap f' (m + 1)) y'`. Take `⟨x, rfl⟩` from `e3 (m + 1) w h1`. Establish `h2 : (homologyMap (fst f') (m + 1)).hom (y' - (homologyMap Φ (m + 1)).hom x) = 0`. Rewrite using `[map_sub, sfst, hw, sub_self]`. Take `⟨u', hu'⟩` from `e2' m _ h2`.

Take `⟨u, rfl⟩` from `(bβ m).2 u'`. Use `⟨x + (homologyδ f m).hom u, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, sδ]`. Rewrite using `[show (homologyδ f' m).hom ((homologyMap β m).hom u) = y' - (homologyMap Φ (m + 1)).hom x from hu']`. Normalize the expressions using the abelian group laws.
-/
theorem isIso_homologyMap_of_comm (Φ : mappingCoconeNat f ⟶ mappingCoconeNat f')
    (hfst : Φ ≫ fst f' = fst f ≫ α) (hinr : inr f ≫ Φ = shiftNegOneMap β ≫ inr f')
    (hsq : ∀ n, homologyMap f n ≫ homologyMap β n = homologyMap α n ≫ homologyMap f' n)
    (hα : ∀ n, IsIso (homologyMap α n)) (hβ : ∀ n, IsIso (homologyMap β n)) (n : ℕ) :
    IsIso (homologyMap Φ n) := by
  have bα : ∀ m, Function.Bijective (homologyMap α m).hom := fun m => by
    have := hα m
    exact ConcreteCategory.bijective_of_isIso _
  have bβ : ∀ m, Function.Bijective (homologyMap β m).hom := fun m => by
    have := hβ m
    exact ConcreteCategory.bijective_of_isIso _

  have sfst : ∀ m x, (homologyMap (fst f') m).hom ((homologyMap Φ m).hom x) =
      (homologyMap α m).hom ((homologyMap (fst f) m).hom x) := fun m x =>
    hom_apply_hom_apply_eq_of_comp_eq (by rw [← homologyMap_comp, hfst, homologyMap_comp]) x
  have sδ : ∀ m y, (homologyMap Φ (m + 1)).hom ((homologyδ f m).hom y) =
      (homologyδ f' m).hom ((homologyMap β m).hom y) := fun m y =>
    hom_apply_hom_apply_eq_of_comp_eq (homologyδ_naturality_of_inr Φ hinr m) y
  have sf : ∀ m z, (homologyMap f' m).hom ((homologyMap α m).hom z) =
      (homologyMap β m).hom ((homologyMap f m).hom z) := fun m z =>
    (hom_apply_hom_apply_eq_of_comp_eq (hsq m) z).symm

  have e1 := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₁ f m)
  have e2 := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₂ f m)
  have e3 := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₃ f m)
  have e1' := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₁ f' m)
  have e2' := fun m => (ShortComplex.moduleCat_exact_iff _).1 (homology_exact₂ f' m)
  have inj_fst0 : ∀ {K₀ L₀ : CochainComplex (ModuleCat.{u} k) ℕ} (g : K₀ ⟶ L₀),
      Function.Injective (homologyMap (fst g) 0).hom := fun g => by
    have := mono_homologyMap_fst_zero g
    exact (ModuleCat.mono_iff_injective _).1 this
  refine @isIso_of_mono_of_epi _ _ _ _ _ _ ((ModuleCat.mono_iff_injective _).2 ?_)
    ((ModuleCat.epi_iff_surjective _).2 ?_)
  · rw [injective_iff_map_eq_zero]
    intro x hx
    cases n with
    | zero =>
      apply inj_fst0 f
      rw [map_zero]
      apply (bα 0).1
      rw [← sfst, hx, map_zero, map_zero]
    | succ m =>
      have h1 : (homologyMap (fst f) (m + 1)).hom x = 0 := by
        apply (bα (m + 1)).1
        rw [← sfst, hx, map_zero, map_zero]
      obtain ⟨y, rfl⟩ := e2 m x h1
      have h2 : (homologyδ f' m).hom ((homologyMap β m).hom y) = 0 := by
        rw [← sδ]
        exact hx
      obtain ⟨z', hz'⟩ := e1' m _ h2
      obtain ⟨z, rfl⟩ := (bα m).2 z'
      have h3 : (homologyMap f m).hom z = y := by
        apply (bβ m).1
        rw [← sf]
        exact hz'
      change (homologyδ f m).hom y = 0
      rw [← h3]
      exact hom_apply_hom_apply_of_comp_eq (homologyMap_homologyδ f m) z
  · intro y'
    cases n with
    | zero =>
      obtain ⟨w, hw⟩ := (bα 0).2 ((homologyMap (fst f') 0).hom y')
      have h1 : (homologyMap f 0).hom w = 0 := by
        apply (bβ 0).1
        rw [← sf, hw, map_zero]
        exact hom_apply_hom_apply_of_comp_eq (homologyMap_fst_homologyMap f' 0) y'
      obtain ⟨x, rfl⟩ := e3 0 w h1
      refine ⟨x, inj_fst0 f' ?_⟩
      rw [sfst]
      exact hw
    | succ m =>
      obtain ⟨w, hw⟩ := (bα (m + 1)).2 ((homologyMap (fst f') (m + 1)).hom y')
      have h1 : (homologyMap f (m + 1)).hom w = 0 := by
        apply (bβ (m + 1)).1
        rw [← sf, hw, map_zero]
        exact hom_apply_hom_apply_of_comp_eq (homologyMap_fst_homologyMap f' (m + 1)) y'
      obtain ⟨x, rfl⟩ := e3 (m + 1) w h1
      have h2 : (homologyMap (fst f') (m + 1)).hom (y' - (homologyMap Φ (m + 1)).hom x) = 0 := by
        rw [map_sub, sfst, hw, sub_self]
      obtain ⟨u', hu'⟩ := e2' m _ h2
      obtain ⟨u, rfl⟩ := (bβ m).2 u'
      refine ⟨x + (homologyδ f m).hom u, ?_⟩
      rw [map_add, sδ]
      rw [show (homologyδ f' m).hom ((homologyMap β m).hom u) =
        y' - (homologyMap Φ (m + 1)).hom x from hu']
      abel

/- English proof (translation)
The claim follows from `isIso_homologyMap_of_comm _ (mapOfHomotopy_fst h) (inr_mapOfHomotopy h) (fun m => by rw [← homologyMap_comp, ← homologyMap_comp, h.homologyMap_eq]) hα hβ n`.
-/
theorem isIso_homologyMap_mapOfHomotopy (h : Homotopy (f ≫ β) (α ≫ f'))
    (hα : ∀ n, IsIso (homologyMap α n)) (hβ : ∀ n, IsIso (homologyMap β n)) (n : ℕ) :
    IsIso (homologyMap (mapOfHomotopy h) n) :=
  isIso_homologyMap_of_comm _ (mapOfHomotopy_fst h) (inr_mapOfHomotopy h)
    (fun m => by rw [← homologyMap_comp, ← homologyMap_comp, h.homologyMap_eq]) hα hβ n

end FiveLemma

end mappingCoconeNat

end GroundTheory.ProfCoh
