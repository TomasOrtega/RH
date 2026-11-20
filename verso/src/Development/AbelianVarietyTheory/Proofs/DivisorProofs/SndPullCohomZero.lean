import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartIStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `h1 : (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ` using `AlgHom.ext fun a ↦ by simp [epsHom, DualNumber.lift_apply_apply]`. Establish `h2 : (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D'` using `DualNumber.algHom_ext (by simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply])`. Simplify using `only [ptV, comp_lift, ← Category.assoc, spOver_comp, h1, h2]`.
-/
theorem spOver_epsHom_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B)
    {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver (epsHom φ) ≫ ptV v x = ptV v (spOver φ ≫ x) := by
  have h1 : (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ :=
    AlgHom.ext fun a ↦ by simp [epsHom, DualNumber.lift_apply_apply]
  have h2 : (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' :=
    DualNumber.algHom_ext (by simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply])
  simp only [ptV, comp_lift, ← Category.assoc, spOver_comp, h1, h2]

/- English proof (translation)
Establish `h1 : (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D` using `AlgHom.ext fun _ ↦ rfl`. Establish `h2 : (TrivSqZeroExt.fstHom R D D).comp (EpsWeil.epsMap R D) = (Algebra.ofId R D).comp (TrivSqZeroExt.fstHom R R R)` using `DualNumber.algHom_ext (by simp [EpsWeil.epsMap, DualNumber.lift_apply_apply])`. Rewrite using `[ptV, pt0, comp_lift, ← Category.assoc, spOver_comp, h1, spOver_id, Category.id_comp, ← Category.assoc, spOver_comp, h2, ← spOver_comp, Category.assoc]`. Use `congr 1`. Use `ext1`.

Rewrite using `[Over.comp_left, Over.comp_left, spOver_left, spOver_left, Hom.one_def, Over.comp_left, Over.toUnit_left]`. Use `hv` as an intermediate fact. Unfold `IsTangent at this`. Use `erw [this]`. Both sides reduce to the same expression.
-/
theorem fst_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {v : epsR R ⟶ B} (hv : IsTangent v)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x = pt0 B x := by
  have h1 : (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D :=
    AlgHom.ext fun _ ↦ rfl
  have h2 : (TrivSqZeroExt.fstHom R D D).comp (EpsWeil.epsMap R D) =
      (Algebra.ofId R D).comp (TrivSqZeroExt.fstHom R R R) :=
    DualNumber.algHom_ext (by simp [EpsWeil.epsMap, DualNumber.lift_apply_apply])
  rw [ptV, pt0, comp_lift, ← Category.assoc, spOver_comp, h1, spOver_id, Category.id_comp,
    ← Category.assoc, spOver_comp, h2, ← spOver_comp, Category.assoc]
  congr 1
  ext1
  rw [Over.comp_left, Over.comp_left, spOver_left, spOver_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
  have := hv
  unfold IsTangent at this
  erw [this]
  rfl

/- English proof (translation)
Take `⟨i, hi⟩` from `hx`. Use `⟨i, ?_⟩` and prove the remaining obligations. Establish `hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left`. Rewrite using `[spOver_left]`. Use `GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩` and prove the remaining obligations.

Rewrite using `[sq, Ideal.zero_eq_bot, eq_bot_iff]`. Use `Ideal.mul_le.2 fun a ha b hb ↦ ?_` and prove the remaining obligations. Establish `ha' : a.fst = 0` using `ha`. Establish `hb' : b.fst = 0` using `hb`. Rewrite using `[Ideal.mem_bot]`.

Apply the tactic sequence `ext <;> simp [ha', hb']`. Establish `e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x).left = x.left ≫ (AbDual.inl A B).left`. Rewrite using `[fst_ptV hv, ← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]`. Use `GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left (ptV v x).left (U := P.U i) (by` as an intermediate fact. Rewrite using `[← Over.comp_left, e, Scheme.Hom.comp_preimage]`.

Conclude with `top_unique hi)`. Conclude with `this.ge`.
-/
theorem sm_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) {v : epsR R ⟶ B}
    (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} (hx : Sm (chartsA P) x) :
    Sm P.U (ptV v x) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  have hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left := by
    rw [spOver_left]
    refine GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  have e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x).left = x.left ≫ (AbDual.inl A B).left := by
    rw [fst_ptV hv, ← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  have := GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left
    (ptV v x).left (U := P.U i) (by
      rw [← Over.comp_left, e, Scheme.Hom.comp_preimage]
      exact top_unique hi)
  exact this.ge

end GlobalTheory.PtExt
