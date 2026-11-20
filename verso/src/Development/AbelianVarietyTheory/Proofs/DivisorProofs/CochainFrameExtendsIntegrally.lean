import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraCoordinateLinearEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CochInt

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieCoord)
open GlobalTheory.TorusLieCoord Formalism.L2.Pj

/- English proof (translation)
Establish `hb : spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap S (DualNumber S)) ≫ spMap φ`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Set `p : Over.mk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ⟶ torus R r` to `Over.homMk (e.1.left ≫ SplitTorus.bcMap (spMap φ) (Fin r → ℤ)) (by`.

Rewrite using `[Category.assoc, SplitTorus.bcMap_hom, ← Category.assoc, Over.w]`. Use the proof step `rfl)`. Set `q : Over.mk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ⟶ torus R r` to `Over.homMk (spMap (dualMap φ) ≫ e₀.1.left) (by`. Rewrite using `[Category.assoc, Over.w]`. Conclude with `hb)`.

Establish `: p = q` using `SplitTorus.pull_ext fun χ => by`. Establish `h₁ : SplitTorus.pull p (Rosenlicht.chi _ χ) = valA e.1 χ`. Unfold `valA`. Rewrite using `[SplitTorus.charUnit_val, ← SplitTorus.bcMap_appTop_chi (spMap φ), ← Rosenlicht.appTop_comp_apply]`. Both sides reduce to the same expression.

Establish `h₂ : SplitTorus.pull q (Rosenlicht.chi _ χ) = dualMap φ (valA e₀.1 χ)`. Unfold `valA`. Rewrite using `[SplitTorus.charUnit_val]`. Conclude with `congrArg (fun g => g.hom (e₀.1.left.appTop.hom (Rosenlicht.chi _ χ))) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap φ)))`. Rewrite using `[h₁, h₂, val_eq_of_lieCoord, val_eq_of_lieCoord]`.

Apply the tactic sequence `ext <;> simp [dualMap, h]`. Conclude with `congrArg (·.left) this`.
-/
theorem left_comp_bcMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r : ℕ} (e₀ : LieG (torus R r))
    (e : LieG (torus S r)) (h : ∀ j, lieCoord e j = φ (lieCoord e₀ j)) :
    e.1.left ≫ SplitTorus.bcMap (spMap φ) (Fin r → ℤ) = spMap (dualMap φ) ≫ e₀.1.left := by
  have hb : spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap S (DualNumber S)) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let p : Over.mk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ⟶ torus R r :=
    Over.homMk (e.1.left ≫ SplitTorus.bcMap (spMap φ) (Fin r → ℤ)) (by
      rw [Category.assoc, SplitTorus.bcMap_hom, ← Category.assoc, Over.w]; rfl)
  let q : Over.mk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ⟶ torus R r :=
    Over.homMk (spMap (dualMap φ) ≫ e₀.1.left) (by
      rw [Category.assoc, Over.w]; exact hb)
  have : p = q := SplitTorus.pull_ext fun χ => by
    have h₁ : SplitTorus.pull p (Rosenlicht.chi _ χ) = valA e.1 χ := by
      unfold valA
      rw [SplitTorus.charUnit_val, ← SplitTorus.bcMap_appTop_chi (spMap φ), ← Rosenlicht.appTop_comp_apply]
      rfl
    have h₂ : SplitTorus.pull q (Rosenlicht.chi _ χ) = dualMap φ (valA e₀.1 χ) := by
      unfold valA
      rw [SplitTorus.charUnit_val]
      exact congrArg (fun g => g.hom (e₀.1.left.appTop.hom (Rosenlicht.chi _ χ)))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap φ)))
    rw [h₁, h₂, val_eq_of_lieCoord, val_eq_of_lieCoord]
    ext <;> simp [dualMap, h]
  exact congrArg (·.left) this

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Conclude with `congrArg (· ≫ x) (Over.w v.1)`. Establish `h : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.1.left = (1 : specO R R ⟶ (Over.pullback x).obj t.G).left` using `congrArg (·.left) v.2`. Establish `e : (specO R R).hom ≫ x = x`.

Conclude with `(congrArg (· ≫ x) (Spec.map_id (CommRingCat.of R))).trans (Category.id_comp x)`. Establish `key : ∀ (y : Sp R ⟶ X), (specO R R).hom ≫ x = y → (1 : specO R R ⟶ (Over.pullback x).obj t.G).left ≫ pullback.fst t.G.hom x = (1 : Over.mk y ⟶ t.G).left`. Introduce and unpack `_ rfl`. Conclude with `(grpPull_one (isGrpPullback_pullback t.G x) (specO R R)).symm`. Rewrite using `[← Category.assoc, h]`.

Conclude with `key x e`.
-/
theorem isTan_of_lieG {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) (v : LieG ((Over.pullback x).obj t.G)) :
    IsTanAtG t x (v.1.left ≫ pullback.fst t.G.hom x) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w v.1)
  · have h : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.1.left =
        (1 : specO R R ⟶ (Over.pullback x).obj t.G).left := congrArg (·.left) v.2
    have e : (specO R R).hom ≫ x = x := by
      exact (congrArg (· ≫ x) (Spec.map_id (CommRingCat.of R))).trans (Category.id_comp x)
    have key : ∀ (y : Sp R ⟶ X), (specO R R).hom ≫ x = y → (1 : specO R R ⟶ (Over.pullback x).obj t.G).left ≫
        pullback.fst t.G.hom x = (1 : Over.mk y ⟶ t.G).left := by
      rintro _ rfl
      exact (grpPull_one (isGrpPullback_pullback t.G x) (specO R R)).symm
    rw [← Category.assoc, h]
    exact key x e

/- English proof (translation)
Introduce and unpack `hP E _ _ _ H X t K _ _ xO xK hx r ε ⟨u, hu, -, hε⟩ i`. Take `⟨e, he, hi⟩` from `hε i`. Set `ψ : ((Over.pullback xK).obj t.G).left ⟶ ((Over.pullback xO).obj t.G).left` to `pullback.lift (pullback.fst t.G.hom xK) (pullback.snd t.G.hom xK ≫ spMap (algebraMap (𝓞 K) K)) (by rw [Category.assoc, hx, pullback.condition])`. Establish `hψ₁ : ψ ≫ pullback.fst t.G.hom xO = pullback.fst t.G.hom xK` using `pullback.lift_fst _ _ _`. Establish `hψ : IsGrpPullback ((Over.pullback xK).obj t.G) ((Over.pullback xO).obj t.G) (spMap (algebraMap (𝓞 K) K)) ψ` using `(isGrpPullback_pullback t.G xO).cancel ((isGrpPullback_pullback t.G xK).congr hx.symm hψ₁.symm) (pullback.lift_snd _ _ _)`.

Take `⟨U, ⟨hU, hU'⟩, -⟩` from `hP.fractionField_of_isGrpPullback (Diag.isSemiAbelian (Sp (𝓞 K)) (Fin r → ℤ)) (IsSemiAbelian.pullback xO t.G t.semi) (SplitTorus.isGrpPullback_bcMap _ _) hψ u`. Take `⟨e₀, he₀⟩` from `(lieCoord_bijective_add_smul (𝓞 K) r).1.2 (Pi.single i 1)`. Establish `hb` using `left_comp_bcMap (algebraMap (𝓞 K) K) e₀ e fun j => by`. Rewrite using `[he, he₀]`. Apply the tactic sequence `by_cases h : j = i <;> simp [Pi.single_apply, h]`.

Use `⟨tanOf (isTan_of_lieG t xO (lieMap U e₀)), tan_ext ?_⟩` and prove the remaining obligations. Rewrite using `[left_bcTan, left_tanOf, hi, ← hψ₁, ← Category.assoc u.left, hU', Category.assoc, ← Category.assoc e.1.left, hb]`. Simplify using `[lieMap]`.
-/
theorem exists_bcTan_eq_of_isCochFrame : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] [NumberField K] (xO : Sp (𝓞 K) ⟶ X) (xK : Sp K ⟶ X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) (r : ℕ) (ε : Fin r → TanM xK t.G), IsCochFrame t xK ε → ∀ i, ∃ w : TanM xO t.G, bcTan (algebraMap (𝓞 K) K) hx w = ε i := by
  rintro hP E _ _ _ H X t K _ _ xO xK hx r ε ⟨u, hu, -, hε⟩ i
  obtain ⟨e, he, hi⟩ := hε i
  let ψ : ((Over.pullback xK).obj t.G).left ⟶ ((Over.pullback xO).obj t.G).left :=
    pullback.lift (pullback.fst t.G.hom xK) (pullback.snd t.G.hom xK ≫ spMap (algebraMap (𝓞 K) K))
      (by rw [Category.assoc, hx, pullback.condition])
  have hψ₁ : ψ ≫ pullback.fst t.G.hom xO = pullback.fst t.G.hom xK := pullback.lift_fst _ _ _
  have hψ : IsGrpPullback ((Over.pullback xK).obj t.G) ((Over.pullback xO).obj t.G) (spMap (algebraMap (𝓞 K) K)) ψ :=
    (isGrpPullback_pullback t.G xO).cancel ((isGrpPullback_pullback t.G xK).congr hx.symm hψ₁.symm)
      (pullback.lift_snd _ _ _)
  obtain ⟨U, ⟨hU, hU'⟩, -⟩ := hP.fractionField_of_isGrpPullback (Diag.isSemiAbelian (Sp (𝓞 K)) (Fin r → ℤ))
    (IsSemiAbelian.pullback xO t.G t.semi) (SplitTorus.isGrpPullback_bcMap _ _) hψ u
  obtain ⟨e₀, he₀⟩ := (lieCoord_bijective_add_smul (𝓞 K) r).1.2 (Pi.single i 1)
  have hb := left_comp_bcMap (algebraMap (𝓞 K) K) e₀ e fun j => by
    rw [he, he₀]
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  refine ⟨tanOf (isTan_of_lieG t xO (lieMap U e₀)), tan_ext ?_⟩
  rw [left_bcTan, left_tanOf, hi, ← hψ₁, ← Category.assoc u.left, hU', Category.assoc, ← Category.assoc e.1.left, hb]
  simp [lieMap]

end GlobalTheory.CochInt

end
