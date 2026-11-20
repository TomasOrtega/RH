import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOneFormsIsBaseChangeTangentRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentRepresentationSmoothGroupSchemeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
open GlobalTheory.AbTan GlobalTheory.AbTan.Transl GlobalTheory.TanForms GlobalTheory.InvForm

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvSpan

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `letI : Algebra B D := (redHom φ).toAlgebra`. Use `haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm`. Conclude with `(map_smul (Derivation.liftKaehlerDifferential _) b m).trans (Algebra.smul_def _ _)`.
-/
theorem dVal_smul {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    (φ : B →ₐ[R] DualNumber D) (b : B) (m : Ω[B⁄R]) : dVal φ (b • m) = redHom φ b * dVal φ m := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact (map_smul (Derivation.liftKaehlerDifferential _) b m).trans (Algebra.smul_def _ _)

variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W]

def tr (A : Over (Sp R)) [GrpObj A] : TrTy A := fun B M ↦ tau A B M

/- English proof (translation)
The claim follows from `fun _ _ _ _ _ _ _ _ P hP ↦ bijOn_tau A P hP`.
-/
theorem tr_bij : TrBij A (tr A) := fun _ _ _ _ _ _ _ _ P hP ↦ bijOn_tau A P hP

/- English proof (translation)
The claim follows from `fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ α f β hβ P hP z hz ↦ tau_natural A α f β hβ P hP z hz`.
-/
theorem tr_nat : TrNat A (tr A) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ α f β hβ P hP z hz ↦
  tau_natural A α f β hβ P hP z hz

/- English proof (translation)
Use `letI := opMod (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R]`. Use `haveI : IsCentralScalar (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] := ⟨fun _ _ ↦ rfl⟩`. Take `⟨hz0, hτz0⟩` from `back_spec (τ := tr A) U tr_bij (pt A U (KaehlerDifferential.D R (Sec A.hom U.1))) (pt_lifts A U _)`. Set `α : Sec A.hom U.1 →ₐ[R] D` to `{ redHom φ with commutes' := redHom_algebraMap φ }`. Establish `hf : ∀ (b : Sec A.hom U.1) (m : Ω[Sec A.hom U.1⁄R]), (dVal φ).toAddMonoidHom (b • m) = redHom φ b • (dVal φ).toAddMonoidHom m` using `fun b m ↦ dVal_smul φ b m`.

Set `β` to `sumHom (redHom φ) (dVal φ).toAddMonoidHom hf`. Establish `hβ : IsSum β α (dVal φ)` using `sumHom_isSum _ (dVal φ).toAddMonoidHom hf`. Take `⟨hl, hnat⟩` from `tau_natural A α (dVal φ) β hβ (affPt A.hom U) (affPt_w A.hom U) _ hz0`. Establish `hpt : spMap β ≫ pt A U (KaehlerDifferential.D R (Sec A.hom U.1)) = spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U`. Rewrite using `[pt, ← Category.assoc, sp_comp]`.

Use `congr 2`. Use `RingHom.ext fun b ↦ ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, show TanForms.derHom (KaehlerDifferential.D R (Sec A.hom U.1)) b = TrivSqZeroExt.inl b + TrivSqZeroExt.inr (KaehlerDifferential.D R (Sec A.hom U.1) b) from rfl, map_add, hβ.1, hβ.2, dVal_D]`. Conclude with `TrivSqZeroExt.inl_fst_add_inr_snd_eq (φ b)`. Use `⟨_, hl, ?_, fun w ↦ ?_⟩` and prove the remaining obligations.

Use `hnat.trans ?_` and prove the remaining obligations. Rewrite using `[← hpt]`. Conclude with `congrArg _ hτz0`. Rewrite using `[T.nat α (dVal φ) β hβ _ hz0]`. Both sides reduce to the same expression.
-/
theorem exists_tangent (T : TanRep A W) (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    ∃ z : Sp (DualNumber D) ⟶ A.left, Lifts A.hom (unitPt A D) z ∧
      tau A D D (spMap (redHom φ) ≫ affPt A.hom U) z =
        spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U ∧
      ∀ w, T.Φ z w = dVal φ (eU T (tr A) U w) := by
  letI := opMod (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R]
  haveI : IsCentralScalar (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨hz0, hτz0⟩ := back_spec (τ := tr A) U tr_bij (pt A U (KaehlerDifferential.D R (Sec A.hom U.1)))
    (pt_lifts A U _)
  let α : Sec A.hom U.1 →ₐ[R] D := { redHom φ with commutes' := redHom_algebraMap φ }
  have hf : ∀ (b : Sec A.hom U.1) (m : Ω[Sec A.hom U.1⁄R]), (dVal φ).toAddMonoidHom (b • m) =
      redHom φ b • (dVal φ).toAddMonoidHom m := fun b m ↦ dVal_smul φ b m
  let β := sumHom (redHom φ) (dVal φ).toAddMonoidHom hf
  have hβ : IsSum β α (dVal φ) := sumHom_isSum _ (dVal φ).toAddMonoidHom hf
  obtain ⟨hl, hnat⟩ := tau_natural A α (dVal φ) β hβ (affPt A.hom U) (affPt_w A.hom U) _ hz0
  have hpt : spMap β ≫ pt A U (KaehlerDifferential.D R (Sec A.hom U.1)) =
      spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U := by
    rw [pt, ← Category.assoc, sp_comp]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    rw [RingHom.comp_apply, show TanForms.derHom (KaehlerDifferential.D R (Sec A.hom U.1)) b =
      TrivSqZeroExt.inl b + TrivSqZeroExt.inr (KaehlerDifferential.D R (Sec A.hom U.1) b) from rfl, map_add,
      hβ.1, hβ.2, dVal_D]
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq (φ b)
  refine ⟨_, hl, ?_, fun w ↦ ?_⟩
  · refine hnat.trans ?_
    rw [← hpt]
    exact congrArg _ hτz0
  · rw [T.nat α (dVal φ) β hβ _ hz0]
    rfl

def form (T : TanRep A W) (w : W) : GlobForm A.hom :=
  ⟨fun V ↦ eU T (tr A) V.unop w, fun _ _ a ↦ eU_nat T tr_bij tr_nat a w⟩

/- English proof (translation)
Rewrite using `[Category.assoc, affPt_w, sp_comp]`. Conclude with `congrArg spMap (RingHom.ext (redHom_algebraMap φ))`.
-/
theorem red_w (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    (spMap (redHom φ) ≫ affPt A.hom U) ≫ A.hom = spMap (algebraMap R D) := by
  rw [Category.assoc, affPt_w, sp_comp]
  exact congrArg spMap (RingHom.ext (redHom_algebraMap φ))

/- English proof (translation)
Introduce `D _ _ U V φ ψ p q q₀ hp hq hpq`. Take `⟨z, hz, hτ, hΦ⟩` from `exists_tangent T U φ`. Take `⟨z', hz', hτ', hΦ'⟩` from `exists_tangent T V ψ`. Express the relevant statement in the definitionally equal form `dVal φ (eU T (tr A) U w) = dVal ψ (eU T (tr A) V w)`. Rewrite using `[← hΦ, ← hΦ']`.

It suffices to establish `h : z = z' by rw [h]`. Rewrite `hτ` using `[tau_eq A _ (red_w U φ) z hz.1, ← hp]`. Rewrite `hτ'` using `[tau_eq A _ (red_w V ψ) z' hz'.1, ← hpq]`. Set `c : ovT R D D ⟶ ovT R D D` to `Over.homMk (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (TrivSqZeroExt.fstHom D D D).toRingHom) (by`. Rewrite using `[Category.assoc, fst_w]`.

Conclude with `sp_comp _ _)`. Set `p' : ovT R D D ⟶ A` to `p`. Set `q' : ovT R D D ⟶ A` to `q`. Establish `e1 : Over.homMk (U` using `ovT R D D) (V := A) (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom φ) ≫ affPt A.hom U) (inl_w A _ (red_w U φ)) = c ≫ p' := by`. Use `ext`.

Express the relevant statement in the definitionally equal form `spMap _ ≫ spMap (redHom φ) ≫ affPt A.hom U = (spMap _ ≫ spMap _) ≫ p.left`. Rewrite using `[hp, Category.assoc, ← Category.assoc (spMap _) (spMap (φ : Sec A.hom U.1 →+* DualNumber D)), sp_comp]`. Both sides reduce to the same expression. Establish `e2 : Over.homMk (U` using `ovT R D D) (V := A) (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom ψ) ≫ affPt A.hom V) (inl_w A _ (red_w V ψ)) = c ≫ (p' * q') := by`. Use `ext`.

Express the relevant statement in the definitionally equal form `spMap _ ≫ spMap (redHom ψ) ≫ affPt A.hom V = (spMap _ ≫ spMap _) ≫ (p * q).left`. Rewrite using `[hpq, Category.assoc, ← Category.assoc (spMap _) (spMap (ψ : Sec A.hom V.1 →+* DualNumber D)), sp_comp]`. Both sides reduce to the same expression. Establish `e3 : c ≫ q' = q'`. Use `ext`.

Express the relevant statement in the definitionally equal form `(_ ≫ _) ≫ q.left = q.left`. Rewrite using `[hq, Category.assoc]`. Express the relevant statement in the definitionally equal form `_ ≫ _ ≫ spMap (TrivSqZeroExt.inlHom D D) ≫ q₀ = _`. Rewrite using `[← Category.assoc (spMap _) (spMap _) q₀, fst_inl, Category.id_comp]`. Rewrite `hτ` using `[e1]`.

Rewrite `hτ'` using `[e2, MonObj.comp_mul, e3]`. Establish `k1 : (c ≫ p') * Over.homMk (U` using `ovT R D D) (V := A) z hz.1 = p' := Over.OverMorphism.ext hτ`. Establish `k2 : (c ≫ p') * q' * Over.homMk (U` using `ovT R D D) (V := A) z' hz'.1 = p' * q' := Over.OverMorphism.ext hτ'`. Establish `k3 : Over.homMk (U` using `ovT R D D) (V := A) z hz.1 = Over.homMk (U := ovT R D D) (V := A) z' hz'.1 := by`. Rewrite `k2` using `[mul_right_comm]`.

Conclude with `mul_left_cancel (k1.trans (mul_right_cancel k2).symm)`. Conclude with `congrArg CommaMorphism.left k3`.
-/
theorem isInv_form [IsCommMonObj A] (T : TanRep A W) (w : W) : IsInv A (form T w) := by
  intro D _ _ U V φ ψ p q q₀ hp hq hpq
  obtain ⟨z, hz, hτ, hΦ⟩ := exists_tangent T U φ
  obtain ⟨z', hz', hτ', hΦ'⟩ := exists_tangent T V ψ
  change dVal φ (eU T (tr A) U w) = dVal ψ (eU T (tr A) V w)
  rw [← hΦ, ← hΦ']
  suffices h : z = z' by rw [h]
  rw [tau_eq A _ (red_w U φ) z hz.1, ← hp] at hτ
  rw [tau_eq A _ (red_w V ψ) z' hz'.1, ← hpq] at hτ'
  let c : ovT R D D ⟶ ovT R D D :=
    Over.homMk (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (TrivSqZeroExt.fstHom D D D).toRingHom) (by
      rw [Category.assoc, fst_w]
      exact sp_comp _ _)
  let p' : ovT R D D ⟶ A := p
  let q' : ovT R D D ⟶ A := q
  have e1 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom φ) ≫ affPt A.hom U) (inl_w A _ (red_w U φ)) =
      c ≫ p' := by
    ext
    change spMap _ ≫ spMap (redHom φ) ≫ affPt A.hom U = (spMap _ ≫ spMap _) ≫ p.left
    rw [hp, Category.assoc, ← Category.assoc (spMap _) (spMap (φ : Sec A.hom U.1 →+* DualNumber D)), sp_comp]
    rfl
  have e2 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom ψ) ≫ affPt A.hom V) (inl_w A _ (red_w V ψ)) =
      c ≫ (p' * q') := by
    ext
    change spMap _ ≫ spMap (redHom ψ) ≫ affPt A.hom V = (spMap _ ≫ spMap _) ≫ (p * q).left
    rw [hpq, Category.assoc, ← Category.assoc (spMap _) (spMap (ψ : Sec A.hom V.1 →+* DualNumber D)), sp_comp]
    rfl
  have e3 : c ≫ q' = q' := by
    ext
    change (_ ≫ _) ≫ q.left = q.left
    rw [hq, Category.assoc]
    change _ ≫ _ ≫ spMap (TrivSqZeroExt.inlHom D D) ≫ q₀ = _
    rw [← Category.assoc (spMap _) (spMap _) q₀, fst_inl, Category.id_comp]
  rw [e1] at hτ
  rw [e2, MonObj.comp_mul, e3] at hτ'
  have k1 : (c ≫ p') * Over.homMk (U := ovT R D D) (V := A) z hz.1 = p' := Over.OverMorphism.ext hτ
  have k2 : (c ≫ p') * q' * Over.homMk (U := ovT R D D) (V := A) z' hz'.1 = p' * q' :=
    Over.OverMorphism.ext hτ'
  have k3 : Over.homMk (U := ovT R D D) (V := A) z hz.1 = Over.homMk (U := ovT R D D) (V := A) z' hz'.1 := by
    rw [mul_right_comm] at k2
    exact mul_left_cancel (k1.trans (mul_right_cancel k2).symm)
  exact congrArg CommaMorphism.left k3

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Proceed by induction on `x using (eU_isBaseChange T tr_bij tr_nat U.unop).inductionOn with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul w => exact Submodule.subset_span ⟨⟨form T w, isInv_form T w⟩, rfl⟩`.

Consider the case `smul s n hn => exact Submodule.smul_mem _ _ (hn trivial)`. Consider the case `add a b ha hb => exact add_mem (ha trivial) (hb trivial)`.
-/
theorem span_eq_top_of_tanRep [IsCommMonObj A] (T : TanRep A W) (U : AffOp A.left) :
    Submodule.span (Sec A.hom U.unop.1) (Set.range fun w : InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using (eU_isBaseChange T tr_bij tr_nat U.unop).inductionOn with
  | zero => exact zero_mem _
  | tmul w => exact Submodule.subset_span ⟨⟨form T w, isInv_form T w⟩, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ _ (hn trivial)
  | add a b ha hb => exact add_mem (ha trivial) (hb trivial)

/- English proof (translation)
Introduce `R _ A _ g hA _ U`. Use `hA.comm` as an intermediate fact. Take `⟨W, _, _, -, -, ⟨T⟩⟩` from `GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hA.smooth`. Conclude with `span_eq_top_of_tanRep T U`.
-/
theorem span_invForm_eq_top : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left,
    Submodule.span (Sec A.hom U.unop.1)
      (Set.range fun w : GlobalTheory.InvForm.InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  intro R _ A _ g hA _ U
  have := hA.comm
  obtain ⟨W, _, _, -, -, ⟨T⟩⟩ := GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hA.smooth
  exact span_eq_top_of_tanRep T U

end GlobalTheory.InvSpan
