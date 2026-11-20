import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PowImage

/- English proof (translation)
Apply `biproduct.hom_ext'` to reduce the goal to its premises. Introduce `k`. Simplify using `only [idealSumMap, biproduct.ι_desc_assoc, biproduct.ι_map_assoc, smulHom_comp, biproduct.ι_desc]`.
-/
lemma idealSumMap_comp_natural {A : Type} [CommRing A] [IsNoetherianRing A] {Z : Scheme.{0}}
    [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (J : Ideal A) :
    idealSumMap F J ≫ g = biproduct.map (fun _ => g) ≫ idealSumMap G J := by
  apply biproduct.hom_ext'
  intro k
  simp only [idealSumMap, biproduct.ι_desc_assoc, biproduct.ι_map_assoc, smulHom_comp,
    biproduct.ι_desc]

/- English proof (translation)
Apply `(cancel_epi (Abelian.factorThruImage (idealSumMap F (I ^ m)))).1` to reduce the goal to its premises. Establish `hfac : Abelian.factorThruImage (idealSumMap F (I ^ m)) ≫ kernel.ι (cokernel.π (idealSumMap F (I ^ m))) = idealSumMap F (I ^ m)` using `Abelian.image.fac _`. Rewrite using `[comp_zero, ← Category.assoc, hfac, ← Category.assoc, idealSumMap_comp_natural, Category.assoc, cokernel.condition, comp_zero]`.
-/
lemma idealPowι_comp_cokernel {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (m : ℕ) :
    idealPowι I F m ≫ g ≫ cokernel.π (idealSumMap G (I ^ m)) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage (idealSumMap F (I ^ m)))).1
  have hfac : Abelian.factorThruImage (idealSumMap F (I ^ m)) ≫
      kernel.ι (cokernel.π (idealSumMap F (I ^ m))) = idealSumMap F (I ^ m) :=
    Abelian.image.fac _
  rw [comp_zero, ← Category.assoc, hfac, ← Category.assoc, idealSumMap_comp_natural,
    Category.assoc, cokernel.condition, comp_zero]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Set `f` to `cokernel.π B.arrow ≫ cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1)))`. Establish `hle : pullSys I φ E S n ≤ kernelSubobject f`. Rewrite using `[← hB]`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Apply `le_kernelSubobject` to reduce the goal to its premises. Rewrite using `[← Category.assoc, cokernel.condition, zero_comp]`. Apply `le_kernelSubobject` to reduce the goal to its premises. Rewrite using `[powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, idealPowι_comp_cokernel, comp_zero]`. Establish `hS : (Scheme.Modules.pullback φ).map (S n).arrow ≫ f = 0`.

Establish `h1` using `le_sup_left.trans hle`. Rewrite using `[← imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S n).arrow), Category.assoc, ← Subobject.ofLE_arrow h1, Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]`. Set `k` to `kernel.lift (cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1)))) ((Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow) (by rw [Category.assoc]; exact hS)`. Establish `hk : k ≫ idealPowι I (cokernel B.arrow) (n + 1) = (Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow` using `kernel.lift_ι _ _ _`. Establish `hadj : (S n).arrow ≫ adjMap φ B = (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _ ≫ (Scheme.Modules.pushforward φ).map (k ≫ idealPowι I (cokernel B.arrow) (n + 1))`.

Rewrite using `[adjMap, Adjunction.homEquiv_unit, hk, Functor.map_comp, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Conclude with `(Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality (S n).arrow`. Use `⟨((Scheme.Modules.pushforward φ).map k).app V (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _).app V y), ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun g => g.app V y) hadj`.

Simplify using `only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.map_comp] at h2`. Rewrite using `[h2]`. Both sides reduce to the same expression.
-/
theorem adjMap_app_mem_range_idealPowι {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ)
    (hB : B ⊔ powSub I _ (n + 1) = pullSys I φ E S n) (V : X.Opens) (x : Γ(E, V))
    (hx : x ∈ secs (S n) V) :
    (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈
      Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  obtain ⟨y, rfl⟩ := hx
  let f := cokernel.π B.arrow ≫ cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1)))
  have hle : pullSys I φ E S n ≤ kernelSubobject f := by
    rw [← hB]
    refine sup_le ?_ ?_
    · apply le_kernelSubobject
      rw [← Category.assoc, cokernel.condition, zero_comp]
    · apply le_kernelSubobject
      rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_cokernel, comp_zero]
  have hS : (Scheme.Modules.pullback φ).map (S n).arrow ≫ f = 0 := by
    have h1 := le_sup_left.trans hle
    rw [← imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S n).arrow), Category.assoc,
      ← Subobject.ofLE_arrow h1, Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]
  let k := kernel.lift (cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1))))
    ((Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow)
    (by rw [Category.assoc]; exact hS)
  have hk : k ≫ idealPowι I (cokernel B.arrow) (n + 1) =
      (Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow := kernel.lift_ι _ _ _
  have hadj : (S n).arrow ≫ adjMap φ B =
      (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _ ≫
        (Scheme.Modules.pushforward φ).map (k ≫ idealPowι I (cokernel B.arrow) (n + 1)) := by
    rw [adjMap, Adjunction.homEquiv_unit, hk, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality (S n).arrow
  refine ⟨((Scheme.Modules.pushforward φ).map k).app V
    (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _).app V y), ?_⟩
  have h2 := congrArg (fun g => g.app V y) hadj
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.map_comp] at h2
  rw [h2]
  rfl

end GlobalTheory.CompanionTheory.GE.PowImage
