import Development.WeilBound.CoreStatements.SesquilinearFractions.Models
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.cm_lie_model_action

open PositivityTheory.Xgf.isogeny_decomposition_product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}
  (X : CMPack Z c FU i hP)

abbrev pK : Sp X.K ⟶ Sp (𝓞 X.K) := 𝟙 (Sp X.K) ≫ spMap (algebraMap (𝓞 X.K) X.K)

def Mm : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K) := (models X).choose

def ρm : 𝓞 E →+* Module.End X.K (Fin g → X.K) := (models X).choose_spec.choose
/- English proof (translation)
The claim follows from `(models X).choose_spec.choose_spec.1`.
-/
theorem hρm : (Mm X).IsActOf Xo.univ.t.act.act (ρm X) := (models X).choose_spec.choose_spec.1

def curveLieModel : LieModel X.t.G (𝟙 (Sp X.K)) (Fin g → X.K) := (models X).choose_spec.choose_spec.2.choose

def integralLieModel : LieModel X.B.t.G (pK X) (Fin g → X.K) := (models X).choose_spec.choose_spec.2.choose_spec.choose
/- English proof (translation)
The claim follows from `(models X).choose_spec.choose_spec.2.choose_spec.choose_spec.1`.
-/
theorem hM1 : ∀ e, ((curveLieModel X).pt e).left ≫ X.m.φ = ((Mm X).pt e).left :=
  (models X).choose_spec.choose_spec.2.choose_spec.choose_spec.1
/- English proof (translation)
The claim follows from `(models X).choose_spec.choose_spec.2.choose_spec.choose_spec.2`.
-/
theorem hM2 : ∀ e, ((curveLieModel X).pt e).left ≫ X.m'.φ = ((integralLieModel X).pt e).left :=
  (models X).choose_spec.choose_spec.2.choose_spec.choose_spec.2

def bK : epsAt (pK X) ⟶ epsR (𝓞 X.K) :=
  Over.homMk (spMap (dualMap (algebraMap (𝓞 X.K) X.K))) (by
    simp only [Over.mk_hom, Category.id_comp]
    rw [isogeny_decomposition_product.spMap_comp, isogeny_decomposition_product.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bK_left : (bK X).left = spMap (dualMap (algebraMap (𝓞 X.K) X.K)) := rfl

def wB (b : Bool) (a : PureType.lat hP (sgnRt H b)) : epsAt (pK X) ⟶ X.B.t.G := bK X ≫ (X.C b).v ≫ X.ψ b a

/- English proof (translation)
Use `haveI := ((X.fam b).1 a).isMonHom`. Unfold `IsTanAt wB`. Establish `hv` using `(X.C b).basis.1 0`. Simplify using `only [Matrix.cons_val_zero] at hv`. Unfold `IsTangent at hv`.

Rewrite using `[Over.comp_left, Over.comp_left, bK_left, ← Category.assoc, ← Category.assoc]`. Establish `e1 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫ spMap (dualMap (algebraMap (𝓞 X.K) X.K)) = spMap (algebraMap (𝓞 X.K) X.K) ≫ spMap (TrivSqZeroExt.fstHom (𝓞 X.K) (𝓞 X.K) (𝓞 X.K)).toRingHom`. Rewrite using `[show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) = spMap (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom from rfl, isogeny_decomposition_product.spMap_comp, isogeny_decomposition_product.spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.

Rewrite using `[e1]`. Simplify using `only [Category.assoc]`. Rewrite using `[← Category.assoc (spMap (TrivSqZeroExt.fstHom (𝓞 X.K) (𝓞 X.K) (𝓞 X.K)).toRingHom) (X.C b).v.left (X.ψ b a).left, hv, ← Over.comp_left, IsMonHom.one_hom, one_left]`. Simplify using `[pK]`.
-/
theorem wB_tan (b : Bool) (a : PureType.lat hP (sgnRt H b)) : IsTanAt X.B.t.G (pK X) (wB X b a) := by
  haveI := ((X.fam b).1 a).isMonHom
  unfold IsTanAt wB
  have hv := (X.C b).basis.1 0
  simp only [Matrix.cons_val_zero] at hv
  unfold IsTangent at hv
  rw [Over.comp_left, Over.comp_left, bK_left, ← Category.assoc, ← Category.assoc]
  have e1 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫
      spMap (dualMap (algebraMap (𝓞 X.K) X.K)) =
      spMap (algebraMap (𝓞 X.K) X.K) ≫ spMap (TrivSqZeroExt.fstHom (𝓞 X.K) (𝓞 X.K) (𝓞 X.K)).toRingHom := by
    rw [show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) =
      spMap (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom from rfl, isogeny_decomposition_product.spMap_comp, isogeny_decomposition_product.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e1]
  simp only [Category.assoc]
  rw [← Category.assoc (spMap (TrivSqZeroExt.fstHom (𝓞 X.K) (𝓞 X.K) (𝓞 X.K)).toRingHom) (X.C b).v.left (X.ψ b a).left, hv,
    ← Over.comp_left, IsMonHom.one_hom, one_left]
  simp [pK]

def lam (b : Bool) (a : PureType.lat hP (sgnRt H b)) : Fin g → X.K :=
  Classical.choose ((integralLieModel X).onto (wB X b a) (wB_tan X b a))

/- English proof (translation)
The claim follows from `Classical.choose_spec ((integralLieModel X).onto (wB X b a) (wB_tan X b a))`.
-/
theorem lam_spec (b : Bool) (a : PureType.lat hP (sgnRt H b)) : (integralLieModel X).pt (lam X b a) = wB X b a :=
  Classical.choose_spec ((integralLieModel X).onto (wB X b a) (wB_tan X b a))

end PositivityTheory.Xgf.cm_lie_model_action

end
