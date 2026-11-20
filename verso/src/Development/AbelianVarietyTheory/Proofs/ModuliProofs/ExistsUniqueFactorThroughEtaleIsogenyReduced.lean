import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFactor

/- English proof (translation)
Set `K : T → Type` to `fun t => AlgebraicClosure (T.residueField t)`. Set `pts : (∐ fun t : T => Sp (K t)) ⟶ T` to `Sigma.desc fun t => Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) (K t))) ≫ T.fromSpecResidueField t`. Establish `: Surjective pts`. Use `⟨fun t => ⟨Sigma.ι (fun t : T => Sp (K t)) t (IsLocalRing.closedPoint (K t)), ?_⟩⟩` and prove the remaining obligations. Establish `e : (Sigma.ι (fun t : T => Sp (K t)) t ≫ pts) (IsLocalRing.closedPoint (K t)) = t`.

Simplify using `only [pts, Sigma.ι_desc]`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)`. Conclude with `(Scheme.Hom.comp_apply _ _ _).symm.trans e`. Use `ext_of_isDominant_of_isSeparated q h pts ?_` and prove the remaining obligations. Use `Sigma.hom_ext _ _ fun t => ?_` and prove the remaining obligations.

Simplify `H (K t) _` using `only [pts, Sigma.ι_desc_assoc]`.
-/
lemma ext_of_geometricPoints {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by
  classical

  let K : T → Type := fun t => AlgebraicClosure (T.residueField t)
  let pts : (∐ fun t : T => Sp (K t)) ⟶ T := Sigma.desc fun t =>
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) (K t))) ≫ T.fromSpecResidueField t

  have : Surjective pts := by
    refine ⟨fun t => ⟨Sigma.ι (fun t : T => Sp (K t)) t (IsLocalRing.closedPoint (K t)), ?_⟩⟩
    have e : (Sigma.ι (fun t : T => Sp (K t)) t ≫ pts) (IsLocalRing.closedPoint (K t)) = t := by
      simp only [pts, Sigma.ι_desc]
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e
  refine ext_of_isDominant_of_isSeparated q h pts ?_
  refine Sigma.hom_ext _ _ fun t => ?_
  simpa only [pts, Sigma.ι_desc_assoc] using H (K t) _

/- English proof (translation)
Introduce `S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H`. Set `T : Over S` to `pullback ψ η[B]`. Set `i : T ⟶ A` to `pullback.fst ψ η[B]`. Establish `hker : IsPullback i (toUnit T) ψ η[B]`. Establish `hp` using `IsPullback.of_hasPullback ψ η[B]`.

Rewrite `hp` using `[toUnit_unique (pullback.snd ψ η[B]) (toUnit T)]`. Then use the resulting hypothesis. Establish `: IsReduced T.left`. Establish `hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left` using `hker.map (Over.forget S)`. Establish `: Etale (toUnit T).left` using `MorphismProperty.of_isPullback hp het`. Establish `: IsReduced (𝟙_ (Over S)).left` using `by dsimp; infer_instance`.

Conclude with `GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left`. Use `hsep` as an intermediate fact. Establish `hf : i ≫ g = toUnit T ≫ η[B']`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_` and prove the remaining obligations.

Introduce `k _ _ x`. Set `xo : Over.mk (x ≫ T.hom) ⟶ T` to `Over.homMk x`. Establish `e1 : (xo ≫ i) ≫ ψ = 1`. Rewrite using `[Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]`. Establish `e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B'])`.

Rewrite using `[← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc, toUnit_unique (xo ≫ toUnit T) (toUnit _)]`. Simplify `congrArg CommaMorphism.left e3` using `only [xo, Over.comp_left, Over.homMk_left]`. Use `hψ` as an intermediate fact. Use `hg` as an intermediate fact. Use `hfin` as an intermediate fact.

Use `het` as an intermediate fact. Use `hsurj` as an intermediate fact. Take `⟨β, hβ, hψβ⟩` from `FlatQuotient.exists_desc ψ i g hker hf`. Establish `: Epi ψ` using `FlatQuotient.epi_of_flat_surjective ψ`. Conclude with `⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩`.
-/
theorem exists_unique_factor : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  intro S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H

  let T : Over S := pullback ψ η[B]
  let i : T ⟶ A := pullback.fst ψ η[B]
  have hker : IsPullback i (toUnit T) ψ η[B] := by
    have hp := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit T)] at hp

  have : IsReduced T.left := by
    have hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left := hker.map (Over.forget S)
    have : Etale (toUnit T).left := MorphismProperty.of_isPullback hp het
    have : IsReduced (𝟙_ (Over S)).left := by dsimp; infer_instance
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left
  have := hsep

  have hf : i ≫ g = toUnit T ≫ η[B'] := by
    apply Over.OverMorphism.ext
    refine ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_
    intro k _ _ x
    let xo : Over.mk (x ≫ T.hom) ⟶ T := Over.homMk x
    have e1 : (xo ≫ i) ≫ ψ = 1 := by
      rw [Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    have e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B']) := by
      rw [← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc,
        toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    simpa only [xo, Over.comp_left, Over.homMk_left] using congrArg CommaMorphism.left e3
  have := hψ; have := hg; have := hfin; have := het; have := hsurj
  obtain ⟨β, hβ, hψβ⟩ := FlatQuotient.exists_desc ψ i g hker hf
  have : Epi ψ := FlatQuotient.epi_of_flat_surjective ψ
  exact ⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩

end GlobalTheory.HkFactor
