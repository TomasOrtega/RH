import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecPi

/- English proof (translation)
Introduce `R _ n D _ _`. Set `S` to `sigmaSpec (fun i => CommRingCat.of (D i))`. Establish `hS : ∀ i, Sigma.ι (fun i => Spec (CommRingCat.of (D i))) i ≫ S = spMap (Pi.evalRingHom D i)` using `fun i => ι_sigmaSpec _ i`. Establish `hinv : ∀ y, (inv S) (S y) = y` using `fun y => by`. Rewrite using `[← Scheme.Hom.comp_apply, IsIso.hom_inv_id]`.

Both sides reduce to the same expression. Establish `hsurj : ∀ x, S ((inv S) x) = x` using `fun x => by`. Rewrite using `[← Scheme.Hom.comp_apply, IsIso.inv_hom_id]`. Both sides reduce to the same expression. Use `⟨fun i => (spMap (Pi.evalRingHom D i)).opensRange, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Establish `hcov : ∀ y : ↥(∐ fun i => Spec (CommRingCat.of (D i))), ∃ k, ∃ z : Sp (D k), (Sigma.ι (fun i => Spec (CommRingCat.of (D i))) k) z = y` using `fun y => ⟨_, (sigmaOpenCover (fun i => Spec (CommRingCat.of (D i)))).covers y⟩`. Take `⟨k, z, hz⟩` from `hcov ((inv S) x)`. Rewrite using `[TopologicalSpace.Opens.mem_iSup]`.

Use `⟨k, z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hS k, Scheme.Hom.comp_apply, hz, hsurj]`. Introduce `i j hij`. Rewrite using `[disjoint_iff, eq_bot_iff]`. Introduce and unpack `x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩`.

Rewrite `ha`, `hb` using `[← hS, Scheme.Hom.comp_apply]`. Establish `e` using `congrArg (inv S) (ha.trans hb.symm)`. Rewrite `e` using `[hinv, hinv]`. Take `⟨rfl⟩` from `(sigmaι_eq_iff _ _ _ _ _).mp e`. Conclude with `absurd rfl hij`.

Introduce `i`. Use `⟨Over.isoMk (spMap (Pi.evalRingHom D i)).isoOpensRange.symm ?_⟩` and prove the remaining obligations. Simplify using `only [Over.mk_hom, Iso.symm_hom]`. Rewrite using `[← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]`. Use `congr 1`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem specPi_cover : ∀ (R : Type) [CommRing R] (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], ∃ V : Fin n → (Sp (∀ i, D i)).Opens, (⨆ i, V i = ⊤) ∧ (Pairwise fun i i' => Disjoint (V i) (V i')) ∧ ∀ i, Nonempty (Over.mk ((V i).ι ≫ spMap (algebraMap R (∀ i, D i))) ≅ Over.mk (spMap (algebraMap R (D i)))) := by
  intro R _ n D _ _
  let S := sigmaSpec (fun i => CommRingCat.of (D i))
  have hS : ∀ i, Sigma.ι (fun i => Spec (CommRingCat.of (D i))) i ≫ S = spMap (Pi.evalRingHom D i) :=
    fun i => ι_sigmaSpec _ i
  have hinv : ∀ y, (inv S) (S y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hsurj : ∀ x, S ((inv S) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  refine ⟨fun i => (spMap (Pi.evalRingHom D i)).opensRange, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have hcov : ∀ y : ↥(∐ fun i => Spec (CommRingCat.of (D i))), ∃ k, ∃ z : Sp (D k),
        (Sigma.ι (fun i => Spec (CommRingCat.of (D i))) k) z = y :=
      fun y => ⟨_, (sigmaOpenCover (fun i => Spec (CommRingCat.of (D i)))).covers y⟩
    obtain ⟨k, z, hz⟩ := hcov ((inv S) x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨k, z, ?_⟩
    rw [← hS k, Scheme.Hom.comp_apply, hz, hsurj]
  · intro i j hij
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [← hS, Scheme.Hom.comp_apply] at ha hb
    have e := congrArg (inv S) (ha.trans hb.symm)
    rw [hinv, hinv] at e
    obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp e
    exact absurd rfl hij
  · intro i
    refine ⟨Over.isoMk (spMap (Pi.evalRingHom D i)).isoOpensRange.symm ?_⟩
    simp only [Over.mk_hom, Iso.symm_hom]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl

end GlobalTheory.SpecPi
