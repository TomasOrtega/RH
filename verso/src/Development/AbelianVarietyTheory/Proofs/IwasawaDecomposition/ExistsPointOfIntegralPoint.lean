import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj.PointsOfFlagModel GlobalTheory.ShFam.Pad.Pull

namespace GlobalTheory.ModelPt

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ _ _ Z C z hz`. Use `set w : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ z with hw`. Take `⟨pt⟩ : Nonempty (Sp ↥C.S)` from `inferInstance`. Establish `hpt : w pt ∈ Z.opn` using `hz ⟨pt, rfl⟩`. Rewrite `hpt` using `[← Z.cover]`.

Take `⟨a, ha⟩` from `Set.mem_iUnion.1 hpt`. Establish `hsub : Subsingleton (Sp ↥C.S)` using `inferInstance`. Take `⟨φ, hφ⟩` from `exists_fromSpec (Z.U a).2 w (fun q _ => by`. Rewrite using `[Subsingleton.elim q pt]`. Conclude with `ha)`.

Establish `hcomp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D), spMap (g.comp f) = spMap g ≫ spMap f` using `fun f g => by`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Set `fK : Z.i.c.F →+* ↥C.S` to `φ.comp (Z.alg a)`. Set `alg : ↥(Z.i.c.V W) →+* ↥(intO ↥C.S)` to `(Spec.preimage (z ≫ Z.π ≫ (Y Z.i).s)).hom`.

Establish `halg : spMap alg = z ≫ Z.π ≫ (Y Z.i).s` using `Spec.map_preimage _`. Establish `hs` using `affineOpenChart_comp_structure_eq_spMap Z hφ`. Establish `compat : (intO ↥C.S).subtype.comp alg = fK.comp (Z.i.c.V W).subtype`. Use `congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `spMap _ = spMap _`.

Rewrite using `[hcomp, hcomp, halg, ← hs, hw, Category.assoc]`. Use `(Y Z.i).jQ_open` as an intermediate fact. Set `q : Sp ↥C.S ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype)` to `pullback.lift (w ≫ Z.π) (spMap fK) ((Category.assoc _ _ _).trans hs)`. Establish `hq : q ≫ pullback.fst _ _ = w ≫ Z.π` using `pullback.lift_fst _ _ _`. Establish `hq2 : q ≫ pullback.snd _ _ = spMap fK` using `pullback.lift_snd _ _ _`.

Establish `: IsPreimmersion (spMap (Z.i.c.V W).subtype)` using `IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)`. Establish `hr : Set.range q ⊆ Set.range (Y Z.i).jQ`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, hy⟩` from `range_opn Z hφ ⟨x, rfl⟩`. Use `⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]`. Conclude with `hy`. Set `y` to `IsOpenImmersion.lift _ q hr`. Establish `hy : y ≫ (Y Z.i).jQ = q` using `IsOpenImmersion.lift_fac _ _ _`. Use `⟨⟨alg, fK, compat, y, ?_, z ≫ Z.π, ?_, ?_⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[← (Y Z.i).jQ_over, ← Category.assoc, hy, hq2]`. Rewrite using `[halg, Category.assoc]`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, reassoc_of% hy, hq]`. Both sides reduce to the same expression.
-/
theorem exists_ptC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X), Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn → ∃ P : PointsOfFlagModel.PtC (Y Z.i) C, z ≫ Z.π = P.yt := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ Z C z hz
  set w : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ z with hw
  obtain ⟨pt⟩ : Nonempty (Sp ↥C.S) := inferInstance
  have hpt : w pt ∈ Z.opn := hz ⟨pt, rfl⟩
  rw [← Z.cover] at hpt
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hpt
  have hsub : Subsingleton (Sp ↥C.S) := inferInstance
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 w (fun q _ => by
    rw [Subsingleton.elim q pt]; exact ha)
  have hcomp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    rw [← Spec.map_comp]; rfl
  let fK : Z.i.c.F →+* ↥C.S := φ.comp (Z.alg a)
  let alg : ↥(Z.i.c.V W) →+* ↥(intO ↥C.S) := (Spec.preimage (z ≫ Z.π ≫ (Y Z.i).s)).hom
  have halg : spMap alg = z ≫ Z.π ≫ (Y Z.i).s := Spec.map_preimage _
  have hs := affineOpenChart_comp_structure_eq_spMap Z hφ
  have compat : (intO ↥C.S).subtype.comp alg = fK.comp (Z.i.c.V W).subtype := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    change spMap _ = spMap _
    rw [hcomp, hcomp, halg, ← hs, hw, Category.assoc]
  have := (Y Z.i).jQ_open
  let q : Sp ↥C.S ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) (spMap fK) ((Category.assoc _ _ _).trans hs)
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have hq2 : q ≫ pullback.snd _ _ = spMap fK := pullback.lift_snd _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z hφ ⟨x, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  let y := IsOpenImmersion.lift _ q hr
  have hy : y ≫ (Y Z.i).jQ = q := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨alg, fK, compat, y, ?_, z ≫ Z.π, ?_, ?_⟩, rfl⟩
  · rw [← (Y Z.i).jQ_over, ← Category.assoc, hy, hq2]
  · rw [halg, Category.assoc]
  · rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, reassoc_of% hy, hq]
    rfl

end GlobalTheory.ModelPt
