import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeNoetherianInducTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualConFT

/- English proof (translation)
Set `f : Sp T ⟶ Sp S` to `spMap φ`. Set `B : Over (Sp T)` to `(Over.pullback f).obj A`. Use `letI : GrpObj B := Functor.grpObjObj`. Establish `hB : IsGrpPullback B A f (pullback.fst A.hom f)` using `isGrpPullback_pullback A f`. Take `⟨hAB, hgB⟩` from `GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback φ A B _ g hB hA hg`.

Establish `h2` using `(GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ f A B _ hB g (𝟙_ _)).1.mp (h B hAB hgB)`. Use `GlobalTheory.T.baseChangeBis _ A (Over.mk ((𝟙_ (Over (Sp T))).hom ≫ f)) (Over.mk (spMap (Ideal.Quotient.mk J))) g (Over.homMk (spMap ψ) ?_) h2` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `spMap ψ ≫ 𝟙 _ ≫ spMap φ = spMap (Ideal.Quotient.mk J)`. Rewrite using `[Category.id_comp, ← hcomp, spMap_comp]`.
-/
theorem hasRep_quot_of_factor {S T : Type} [CommRing S] [CommRing T] (J : Ideal S) (φ : S →+* T)
    (ψ : T →+* S ⧸ J) (hcomp : ψ.comp φ = Ideal.Quotient.mk J) (g : ℕ)
    (h : ∀ (B : Over (Sp T)) [GrpObj B], IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      HasRep B g (𝟙_ _))
    (A : Over (Sp S)) [GrpObj A] (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) := by
  let f : Sp T ⟶ Sp S := spMap φ
  let B : Over (Sp T) := (Over.pullback f).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback φ A B _ g hB hA hg
  have h2 := (GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ f A B _ hB g (𝟙_ _)).1.mp (h B hAB hgB)
  refine GlobalTheory.T.baseChangeBis _ A (Over.mk ((𝟙_ (Over (Sp T))).hom ≫ f)) (Over.mk (spMap (Ideal.Quotient.mk J))) g
    (Over.homMk (spMap ψ) ?_) h2
  change spMap ψ ≫ 𝟙 _ ≫ spMap φ = spMap (Ideal.Quotient.mk J)
  rw [Category.id_comp, ← hcomp, spMap_comp]

end GlobalTheory.DualConFT

namespace GlobalTheory.DualConFT

/- English proof (translation)
Use `haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R`. Proceed by induction on `I using WellFoundedGT.induction with`. Consider the case `_ I ih`. Introduce `A _ hA hg`. Use `haveI : @Algebra.FiniteType ℤ (R ⧸ I) _ _ (Ring.toIntAlgebra _) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective`.

Use `GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction (R ⧸ I) A g hA hg fun J' hJ' => ?_` and prove the remaining obligations. Set `J : Ideal R` to `J'.comap (Ideal.Quotient.mk I)`. Establish `hle : I ≤ J` using `fun a ha => by show Ideal.Quotient.mk I a ∈ J'`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr ha]`. Conclude with `J'.zero_mem`.

Establish `hlt : I < J`. Use `lt_of_le_of_ne hle fun hIJ => hJ' ?_` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Establish `ha : a ∈ J` using `hx`. Rewrite `ha` using `[← hIJ]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr ha]`. Conclude with `(⊥ : Ideal (R ⧸ I)).zero_mem`. Set `ψ : R ⧸ J →+* (R ⧸ I) ⧸ J'` to `Ideal.Quotient.lift J ((Ideal.Quotient.mk J').comp (Ideal.Quotient.mk I)) fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha`.

Use `hasRep_quot_of_factor J' (Ideal.Quotient.factor hle) ψ ?_ g (fun B _ hB hgB => ih J hlt B hB hgB) A hA hg` and prove the remaining obligations. Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Use extensionality with `a`. Both sides reduce to the same expression.
-/
theorem hasRep_quot (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (g : ℕ) (I : Ideal R) :
    ∀ (A : Over (Sp (R ⧸ I))) [GrpObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      HasRep A g (𝟙_ _) := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  induction I using WellFoundedGT.induction with
  | _ I ih =>
    intro A _ hA hg
    haveI : @Algebra.FiniteType ℤ (R ⧸ I) _ _ (Ring.toIntAlgebra _) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mk I).toIntAlgHom Ideal.Quotient.mk_surjective
    refine GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction (R ⧸ I) A g hA hg fun J' hJ' => ?_
    let J : Ideal R := J'.comap (Ideal.Quotient.mk I)
    have hle : I ≤ J := fun a ha => by
      show Ideal.Quotient.mk I a ∈ J'
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact J'.zero_mem
    have hlt : I < J := by
      refine lt_of_le_of_ne hle fun hIJ => hJ' ?_
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have ha : a ∈ J := hx
      rw [← hIJ] at ha
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact (⊥ : Ideal (R ⧸ I)).zero_mem
    let ψ : R ⧸ J →+* (R ⧸ I) ⧸ J' :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk J').comp (Ideal.Quotient.mk I)) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr ha
    refine hasRep_quot_of_factor J' (Ideal.Quotient.factor hle) ψ ?_ g (fun B _ hB hgB => ih J hlt B hB hgB)
      A hA hg
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

/- English proof (translation)
Introduce `R _ _ A _ g hA hg`. Use `GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction R A g hA hg fun J _ => ?_` and prove the remaining obligations. Conclude with `hasRep_quot_of_factor J (Ideal.Quotient.mk J) (RingHom.id _) rfl g (fun B _ hB hgB => hasRep_quot R g J B hB hgB) A hA hg`.
-/
theorem hasRep_of_finiteType : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg
  refine GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction R A g hA hg fun J _ => ?_
  exact hasRep_quot_of_factor J (Ideal.Quotient.mk J) (RingHom.id _) rfl g
    (fun B _ hB hgB => hasRep_quot R g J B hB hgB) A hA hg

end GlobalTheory.DualConFT
