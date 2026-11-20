import Mathlib
import GroundTheory.ProfiniteCohomology.MackeyFormula
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.InnerConj
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomApplyHomApplyEqOfCompEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

section Additive

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {A B : Rep.{u} k Γ} [IsDiscreteRep A] [IsDiscreteRep B]

/- English proof (translation)
Use extensionality with `n c : 3`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression.
-/
private theorem cochainsMap_add_alt (f g : A ⟶ B) :
    cochainsMap (f + g) = cochainsMap f + cochainsMap g := by
  ext n c : 3
  apply Subtype.ext
  funext x
  rfl

private noncomputable def cohomologyMapAddHom (n : ℕ) :
    (A ⟶ B) →+ (cohomology A n ⟶ cohomology B n) where
  toFun f := cohomologyMap f n
  map_zero' := cohomologyMap_zero n
  map_add' f g := by
    rw [cohomologyMap, cochainsMap_add_alt]
    exact HomologicalComplex.homologyMap_add _ _ _

/- English proof (translation)
The claim follows from `map_sum (cohomologyMapAddHom n) f s`.
-/
private theorem cohomologyMap_sum_alt {J : Type*} (s : Finset J) (f : J → (A ⟶ B)) (n : ℕ) :
    cohomologyMap (∑ j ∈ s, f j) n = ∑ j ∈ s, cohomologyMap (f j) n :=
  map_sum (cohomologyMapAddHom n) f s

end Additive

section Conj

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
  (V : OpenSubgroup G) (ι : H →ₜ* G)

def mackeyConjₜ (x : G) : mackeySubgroup (V : Subgroup G) ι.toMonoidHom x →ₜ* (V : Subgroup G) :=
  ⟨mackeyConj (V : Subgroup G) ι.toMonoidHom x,
    continuous_mackeyConj V (continuous_toMonoidHom ι) x⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mackeyConjₜ_toMonoidHom (x : G) :
    (mackeyConjₜ V ι x).toMonoidHom = mackeyConj (V : Subgroup G) ι.toMonoidHom x :=
  rfl

end Conj

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (V : OpenSubgroup G) (ι : H →ₜ* G) (N : Rep.{u} k (V : Subgroup G)) [IsDiscreteRep N]

instance isDiscreteRep_res_coind :
    IsDiscreteRep (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) :=
  IsDiscreteRep.res (continuous_toMonoidHom ι) _

instance isDiscreteRep_mackeyRep_continuousMonoidHom (x : G) :
    IsDiscreteRep (mackeyRep (V : Subgroup G) ι.toMonoidHom N x) :=
  isDiscreteRep_mackeyRep V (continuous_toMonoidHom ι) N x

instance isDiscreteRep_mackeySummand (x : G) :
    IsDiscreteRep (mackeySummand (V : Subgroup G) ι.toMonoidHom N x) :=
  @isDiscreteRep_coind k H _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) x)
    (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)
    (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N x) _

noncomputable instance fintype_mackeyDoubleCoset :
    Fintype (MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :=
  have := finite_mackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom
  Fintype.ofFinite _

noncomputable def mackeyCohomologyMap (x : G) (n : ℕ) :
    cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n ⟶
      cohomology (mackeyRep (V : Subgroup G) ι.toMonoidHom N x) n :=
  cohomologyMap (mackeyProj (V : Subgroup G) ι.toMonoidHom N x) n ≫
    cohomologyMapAlong (mackeySubgroup (V : Subgroup G) ι.toMonoidHom x).subtype
      (continuous_subgroup_subtype _)
      (coindEvalOne (mackeySubgroup (V : Subgroup G) ι.toMonoidHom x)
        (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)) n

omit [CompactSpace G] in
/- English proof (translation)
The claim follows from `@isIso_shapiroMap' k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) x) (mackeyRep (V : Subgroup G) ι.toMonoidHom N x) (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N x) n`.
-/
theorem isIso_shapiroMap_mackey (x : G) (n : ℕ) :
    IsIso (@shapiroMap k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) x)
      (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)
      (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N x) n) :=
  @isIso_shapiroMap' k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) x)
      (mackeyRep (V : Subgroup G) ι.toMonoidHom N x)
      (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N x) n

/- English proof (translation)
Use `set P := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom => cohomologyMap (mackeyProj (V : Subgroup G) ι.toMonoidHom N d.out) n`. Use `set I := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom => cohomologyMap (mackeyIncl (V : Subgroup G) ι.toMonoidHom N d) n`. Establish `hIP : ∀ d, I d ≫ P d = 𝟙 _` using `fun d => by`. Simplify using `only [I, P]`. Rewrite using `[← cohomologyMap_comp, mackeyIncl_comp_mackeyProj, cohomologyMap_id]`.

Establish `hIP' : ∀ d d', d ≠ d' → I d ≫ P d' = 0` using `fun d d' h => by`. Simplify using `only [I, P]`. Rewrite using `[← cohomologyMap_comp, mackeyIncl_comp_mackeyProj_of_ne _ _ _ h, cohomologyMap_zero]`. Establish `hsum : ∑ d, P d ≫ I d = 𝟙 _`. Simplify using `only [I, P]`.

Repeatedly rewrite using `[← cohomologyMap_comp]`. Rewrite using `[← cohomologyMap_sum_alt, sum_mackeyProj_comp_mackeyIncl, cohomologyMap_id]`. Use `set S := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom => @shapiroMap k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) d.out) (mackeyRep (V : Subgroup G) ι.toMonoidHom N d.out) (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N d.out) n`. Establish `key : ∀ d c, (mackeyCohomologyMap V ι N d.out n).hom c = (S d).hom ((P d).hom c)` using `fun _ _ => rfl`. Establish `hS : ∀ d, Function.Bijective (S d).hom` using `fun d => by`.

Use `isIso_shapiroMap_mackey V ι N d.out n` as an intermediate fact. Conclude with `ConcreteCategory.bijective_of_isIso _`. Prove the components needed by the constructor for the conclusion. Introduce `c c' hcc`. Establish `hP : ∀ d, (P d).hom c = (P d).hom c'` using `fun d => by`.

Establish `h1` using `congrFun hcc d`. Simplify using `only [key] at h1`. Conclude with `(hS d).1 h1`. Establish `e : ∀ c₀, c₀ = ∑ d, (I d).hom ((P d).hom c₀)` using `fun c₀ => by`. Use `congrArg (fun φ => φ.hom c₀) hsum` as an intermediate fact.

Rewrite `this` using `[ModuleCat.hom_sum, LinearMap.sum_apply]`. Conclude with `this.symm`. Rewrite using `[e c, e c']`. Simplify using `only [hP]`. Introduce `y choose z hz using fun d => (hS d).2 (y d)`.

Use `⟨∑ d, (I d).hom (z d), funext fun d' => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(mackeyCohomologyMap V ι N d'.out n).hom (∑ d, (I d).hom (z d)) = y d'`. Rewrite using `[key, map_sum, Finset.sum_eq_single d']`. Rewrite using `[hom_apply_hom_apply_of_comp_eq (hIP d') (z d')]`. Conclude with `hz d'`.

Introduce `d _ hd`. Rewrite using `[hom_apply_hom_apply_of_comp_eq (hIP' d d' hd) (z d)]`. Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ d') h`.
-/
theorem mackeyCohomology_bijective (n : ℕ) :
    Function.Bijective fun (c : cohomology (Rep.res ι.toMonoidHom
        (Rep.coind (V : Subgroup G).subtype N)) n)
        (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) =>
      (mackeyCohomologyMap V ι N d.out n).hom c := by
  classical
  set P := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom =>
    cohomologyMap (mackeyProj (V : Subgroup G) ι.toMonoidHom N d.out) n
  set I := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom =>
    cohomologyMap (mackeyIncl (V : Subgroup G) ι.toMonoidHom N d) n
  have hIP : ∀ d, I d ≫ P d = 𝟙 _ := fun d => by
    simp only [I, P]
    rw [← cohomologyMap_comp, mackeyIncl_comp_mackeyProj, cohomologyMap_id]
  have hIP' : ∀ d d', d ≠ d' → I d ≫ P d' = 0 := fun d d' h => by
    simp only [I, P]
    rw [← cohomologyMap_comp, mackeyIncl_comp_mackeyProj_of_ne _ _ _ h, cohomologyMap_zero]
  have hsum : ∑ d, P d ≫ I d = 𝟙 _ := by
    simp only [I, P]
    simp_rw [← cohomologyMap_comp]
    rw [← cohomologyMap_sum_alt, sum_mackeyProj_comp_mackeyIncl, cohomologyMap_id]
  set S := fun d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom =>
    @shapiroMap k H _ _ _ _ _ (mackeyOpenSubgroup V (continuous_toMonoidHom ι) d.out)
      (mackeyRep (V : Subgroup G) ι.toMonoidHom N d.out)
      (isDiscreteRep_mackeyRep_continuousMonoidHom V ι N d.out) n
  have key : ∀ d c, (mackeyCohomologyMap V ι N d.out n).hom c = (S d).hom ((P d).hom c) :=
    fun _ _ => rfl
  have hS : ∀ d, Function.Bijective (S d).hom := fun d => by
    have := isIso_shapiroMap_mackey V ι N d.out n
    exact ConcreteCategory.bijective_of_isIso _
  constructor
  · intro c c' hcc
    have hP : ∀ d, (P d).hom c = (P d).hom c' := fun d => by
      have h1 := congrFun hcc d
      simp only [key] at h1
      exact (hS d).1 h1
    have e : ∀ c₀, c₀ = ∑ d, (I d).hom ((P d).hom c₀) := fun c₀ => by
      have := congrArg (fun φ => φ.hom c₀) hsum
      rw [ModuleCat.hom_sum, LinearMap.sum_apply] at this
      exact this.symm
    rw [e c, e c']
    simp only [hP]
  · intro y
    choose z hz using fun d => (hS d).2 (y d)
    refine ⟨∑ d, (I d).hom (z d), funext fun d' => ?_⟩
    change (mackeyCohomologyMap V ι N d'.out n).hom (∑ d, (I d).hom (z d)) = y d'
    rw [key, map_sum, Finset.sum_eq_single d']
    · rw [hom_apply_hom_apply_of_comp_eq (hIP d') (z d')]
      exact hz d'
    · intro d _ hd
      rw [hom_apply_hom_apply_of_comp_eq (hIP' d d' hd) (z d)]
      rfl
    · intro h
      exact absurd (Finset.mem_univ d') h

noncomputable def mackeyCohomologyPi (n : ℕ) :
    cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n →ₗ[k]
      ∀ d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom,
        cohomology (mackeyRep (V : Subgroup G) ι.toMonoidHom N d.out) n :=
  LinearMap.pi fun d => (mackeyCohomologyMap V ι N d.out n).hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mackeyCohomologyPi_apply (n : ℕ)
    (c : cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n)
    (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :
    mackeyCohomologyPi V ι N n c d = (mackeyCohomologyMap V ι N d.out n).hom c :=
  rfl

/- English proof (translation)
Establish `h` using `mackeyCohomology_bijective V ι N n`. Use `⟨fun c c' hc => h.1 (funext fun d => ?_), fun y => ?_⟩` and prove the remaining obligations. Use `congrFun hc d` as an intermediate fact. Rewrite `this` using `[mackeyCohomologyPi_apply, mackeyCohomologyPi_apply]`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `h.2 y`.

Conclude with `⟨c, funext fun d => (mackeyCohomologyPi_apply V ι N n c d).trans (congrFun hc d)⟩`.
-/
theorem mackeyCohomologyPi_bijective (n : ℕ) : Function.Bijective (mackeyCohomologyPi V ι N n) := by
  have h := mackeyCohomology_bijective V ι N n
  refine ⟨fun c c' hc => h.1 (funext fun d => ?_), fun y => ?_⟩
  · have := congrFun hc d
    rwa [mackeyCohomologyPi_apply, mackeyCohomologyPi_apply] at this
  · obtain ⟨c, hc⟩ := h.2 y
    exact ⟨c, funext fun d => (mackeyCohomologyPi_apply V ι N n c d).trans (congrFun hc d)⟩

noncomputable def mackeyCohomologyEquiv (n : ℕ) :
    cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n ≃ₗ[k]
      ∀ d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom,
        cohomology (mackeyRep (V : Subgroup G) ι.toMonoidHom N d.out) n :=
  LinearEquiv.ofBijective (mackeyCohomologyPi V ι N n) (mackeyCohomologyPi_bijective V ι N n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mackeyCohomologyEquiv_apply (n : ℕ)
    (c : cohomology (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) n)
    (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :
    mackeyCohomologyEquiv V ι N n c d = (mackeyCohomologyMap V ι N d.out n).hom c :=
  rfl

/- English proof (translation)
Rewrite using `[← Category.id_comp (cohomologyMapAlong ι.toMonoidHom _ _ n), ← cohomologyInnerConj_eq_id n (Rep.coind (V : Subgroup G).subtype N) x⁻¹, mackeyCohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap, shapiroMap_eq, cohomologyInnerConj, Category.assoc]`. Rewrite using `[← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]`. Use `Eq.trans ?_ (cohomologyMapAlong_comp _ _ _ _ _ _ n)` and prove the remaining obligations. Use `cohomologyMapAlong_congr _ _ _ _ ?_ (fun f => ?_) n` and prove the remaining obligations. Use extensionality with `h`.

Express the relevant statement in the definitionally equal form `x⁻¹⁻¹ * ι.toMonoidHom (h : H) * x⁻¹ = x * ι.toMonoidHom (h : H) * x⁻¹`. Rewrite using `[inv_inv]`. Express the relevant statement in the definitionally equal form `f.1 (x * ι.toMonoidHom 1 * x⁻¹) = f.1 1`. Rewrite using `[map_one, mul_one, mul_inv_cancel]`.
-/
theorem cohomologyMapAlong_comp_mackeyCohomologyMap (x : G) (n : ℕ) :
    cohomologyMapAlong ι.toMonoidHom (continuous_toMonoidHom ι)
        (𝟙 (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N))) n ≫
      mackeyCohomologyMap V ι N x n =
    shapiroMap V N n ≫ cohomologyMapAlong (mackeyConj (V : Subgroup G) ι.toMonoidHom x)
      (continuous_toMonoidHom (mackeyConjₜ V ι x)) (𝟙 _) n := by
  rw [← Category.id_comp (cohomologyMapAlong ι.toMonoidHom _ _ n),
    ← cohomologyInnerConj_eq_id n (Rep.coind (V : Subgroup G).subtype N) x⁻¹,
    mackeyCohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap, shapiroMap_eq,
    cohomologyInnerConj, Category.assoc]
  rw [← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine Eq.trans ?_ (cohomologyMapAlong_comp _ _ _ _ _ _ n)
  refine cohomologyMapAlong_congr _ _ _ _ ?_ (fun f => ?_) n
  · ext h
    change x⁻¹⁻¹ * ι.toMonoidHom (h : H) * x⁻¹ = x * ι.toMonoidHom (h : H) * x⁻¹
    rw [inv_inv]
  · change f.1 (x * ι.toMonoidHom 1 * x⁻¹) = f.1 1
    rw [map_one, mul_one, mul_inv_cancel]

/- English proof (translation)
Rewrite using `[mackeyCohomologyEquiv_apply]`. Conclude with `hom_apply_hom_apply_eq_of_comp_eq (cohomologyMapAlong_comp_mackeyCohomologyMap V ι N d.out n) c`.
-/
theorem mackeyCohomologyEquiv_cohomologyMapAlong (n : ℕ)
    (c : cohomology (Rep.coind (V : Subgroup G).subtype N) n)
    (d : MackeyDoubleCoset (V : Subgroup G) ι.toMonoidHom) :
    mackeyCohomologyEquiv V ι N n ((cohomologyMapAlong ι.toMonoidHom (continuous_toMonoidHom ι)
        (𝟙 (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N))) n).hom c) d =
      (cohomologyMapAlong (mackeyConj (V : Subgroup G) ι.toMonoidHom d.out)
        (continuous_toMonoidHom (mackeyConjₜ V ι d.out)) (𝟙 _) n).hom ((shapiroMap V N n).hom c) := by
  rw [mackeyCohomologyEquiv_apply]
  exact hom_apply_hom_apply_eq_of_comp_eq (cohomologyMapAlong_comp_mackeyCohomologyMap V ι N d.out n) c

end GroundTheory.ProfCoh
