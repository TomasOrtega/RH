import Mathlib
import GroundTheory.ProfiniteCohomology.CoinducedModules.CohomologyCoindCokernelIsoHom
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
import GroundTheory.ProfiniteCohomology.InflationRestriction.CohomologyResMemCohomologyConjInvariants
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

def innerConjHom (g : Γ) : Γ →* Γ where
  toFun γ := g⁻¹ * γ * g
  map_one' := by group
  map_mul' a b := by group

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem innerConjHom_apply (g γ : Γ) : innerConjHom g γ = g⁻¹ * γ * g :=
  rfl

/- English proof (translation)
The claim follows from `(continuous_const.mul continuous_id).mul continuous_const`.
-/
theorem continuous_innerConjHom (g : Γ) : Continuous (innerConjHom g) :=
  (continuous_const.mul continuous_id).mul continuous_const

noncomputable def innerConjMor (A : Rep.{u} k Γ) (g : Γ) : Rep.res (innerConjHom g) A ⟶ A :=
  Rep.ofHom ⟨A.ρ g, fun γ => by
    ext a
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      innerConjHom_apply]
    change A.ρ g (A.ρ (g⁻¹ * γ * g) a) = A.ρ γ (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem innerConjMor_hom_apply (A : Rep.{u} k Γ) (g : Γ) (a : A) :
    (innerConjMor A g).hom a = A.ρ g a :=
  rfl

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in

@[reassoc]
/- English proof (translation)
Use extensionality with `a`. Conclude with `(Rep.hom_comm_apply f g a).symm`.
-/
theorem innerConjMor_naturality {A B : Rep.{u} k Γ} (f : A ⟶ B) (g : Γ) :
    (Rep.resFunctor (innerConjHom g)).map f ≫ innerConjMor B g = innerConjMor A g ≫ f := by
  ext a
  exact (Rep.hom_comm_apply f g a).symm

noncomputable def cohomologyInnerConj (A : Rep.{u} k Γ) [IsDiscreteRep A] (n : ℕ) (g : Γ) :
    cohomology A n ⟶ cohomology A n :=
  cohomologyMapAlong (innerConjHom g) (continuous_innerConjHom g) (innerConjMor A g) n

noncomputable def innerConjShortComplexMor (S : ShortComplex (Rep.{u} k Γ)) (g : Γ) :
    S.map (Rep.resFunctor (innerConjHom g)) ⟶ S where
  τ₁ := innerConjMor S.X₁ g
  τ₂ := innerConjMor S.X₂ g
  τ₃ := innerConjMor S.X₃ g
  comm₁₂ := (innerConjMor_naturality S.f g).symm
  comm₂₃ := (innerConjMor_naturality S.g g).symm

@[reassoc]
/- English proof (translation)
The claim follows from `δ_comp_cohomologyMapAlong (innerConjHom g) (continuous_innerConjHom g) (innerConjShortComplexMor S g) hS hS i j hij`.
-/
theorem δ_comp_cohomologyInnerConj {S : ShortComplex (Rep.{u} k Γ)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j)
    (g : Γ) :
    δ hS i j hij ≫ cohomologyInnerConj S.X₁ j g = cohomologyInnerConj S.X₃ i g ≫ δ hS i j hij :=
  δ_comp_cohomologyMapAlong (innerConjHom g) (continuous_innerConjHom g)
    (innerConjShortComplexMor S g) hS hS i j hij

/- English proof (translation)
Apply `ModuleCat.hom_ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Take `⟨z, rfl⟩` from `homologyπ_surjective (cochainsComplex A) 0 x`. Express the relevant statement in the definitionally equal form `(cohomologyInnerConj A 0 g).hom ((cohomologyπ A 0).hom z) = (cohomologyπ A 0).hom z`.

Rewrite using `[cohomologyInnerConj, cohomologyπ_cohomologyMapAlong_apply]`. Use `congr 1`. Apply `iCycles_injective (cochainsComplex A) 0` to reduce the goal to its premises. Rewrite using `[iCycles_cyclesMap_apply]`. Use `set c := ((cochainsComplex A).iCycles 0).hom z`.

Establish `hd : ((cochainsComplex A).d 0 1).hom c = 0` using `iCycles_d_apply _ 0 1 z`. Establish `hfix : A.ρ g (c.1 Fin.elim0) = c.1 Fin.elim0`. Establish `h1` using `congrArg (fun c' : locallyConstantCochains A 1 => c'.1 fun _ => g) hd`. Establish `h2` using `cochainsComplex_d_zero_apply A c (fun _ => g)`. Establish `h3` using `h2.symm.trans h1`.

Conclude with `sub_eq_zero.1 h3`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `A.ρ g (c.1 (⇑(innerConjHom g) ∘ x)) = c.1 x`. Rewrite using `[Subsingleton.elim (⇑(innerConjHom g) ∘ x) Fin.elim0, Subsingleton.elim x Fin.elim0, hfix]`.
-/
theorem cohomologyInnerConj_zero (A : Rep.{u} k Γ) [IsDiscreteRep A] (g : Γ) :
    cohomologyInnerConj A 0 g = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochainsComplex A) 0 x
  change (cohomologyInnerConj A 0 g).hom ((cohomologyπ A 0).hom z) = (cohomologyπ A 0).hom z
  rw [cohomologyInnerConj, cohomologyπ_cohomologyMapAlong_apply]
  congr 1
  apply iCycles_injective (cochainsComplex A) 0
  rw [iCycles_cyclesMap_apply]
  set c := ((cochainsComplex A).iCycles 0).hom z
  have hd : ((cochainsComplex A).d 0 1).hom c = 0 := iCycles_d_apply _ 0 1 z
  have hfix : A.ρ g (c.1 Fin.elim0) = c.1 Fin.elim0 := by
    have h1 := congrArg (fun c' : locallyConstantCochains A 1 => c'.1 fun _ => g) hd
    have h2 := cochainsComplex_d_zero_apply A c (fun _ => g)
    have h3 := h2.symm.trans h1
    exact sub_eq_zero.1 h3
  apply Subtype.ext
  funext x
  change A.ρ g (c.1 (⇑(innerConjHom g) ∘ x)) = c.1 x
  rw [Subsingleton.elim (⇑(innerConjHom g) ∘ x) Fin.elim0, Subsingleton.elim x Fin.elim0, hfix]

variable [CompactSpace Γ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro A _ g`. Conclude with `cohomologyInnerConj_zero A g`. Consider the case `succ n ih`. Introduce `A _ g`.

Establish `h` using `δ_comp_cohomologyInnerConj (coindShortComplex_shortExact A) n (n + 1) rfl g`. Establish `h3 : cohomologyInnerConj (coindShortComplex A).X₃ n g = 𝟙 _` using `ih _ g`. Rewrite `h` using `[h3, Category.id_comp]`. Express the relevant statement in the definitionally equal form `coindδ A n ≫ cohomologyInnerConj A (n + 1) g = coindδ A n at h`. Rewrite using `[← cancel_epi (coindδ A n), h, Category.comp_id]`.
-/
theorem cohomologyInnerConj_eq_id (n : ℕ) :
    ∀ (A : Rep.{u} k Γ) [IsDiscreteRep A] (g : Γ), cohomologyInnerConj A n g = 𝟙 _ := by
  induction n with
  | zero => intro A _ g; exact cohomologyInnerConj_zero A g
  | succ n ih =>
    intro A _ g
    have h := δ_comp_cohomologyInnerConj (coindShortComplex_shortExact A) n (n + 1) rfl g
    have h3 : cohomologyInnerConj (coindShortComplex A).X₃ n g = 𝟙 _ := ih _ g
    rw [h3, Category.id_comp] at h
    change coindδ A n ≫ cohomologyInnerConj A (n + 1) g = coindδ A n at h
    rw [← cancel_epi (coindδ A n), h, Category.comp_id]

/- English proof (translation)
Rewrite using `[cohomologyInnerConj_eq_id]`. Both sides reduce to the same expression.
-/
theorem cohomologyInnerConj_apply (A : Rep.{u} k Γ) [IsDiscreteRep A] (n : ℕ) (g : Γ)
    (x : cohomology A n) : (cohomologyInnerConj A n g).hom x = x := by
  rw [cohomologyInnerConj_eq_id]
  rfl

end GroundTheory.ProfCoh
