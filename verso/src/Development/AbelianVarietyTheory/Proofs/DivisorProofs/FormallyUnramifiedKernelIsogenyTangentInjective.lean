import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedOfDualNumbers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerUnram

/- English proof (translation)
Introduce `K _ _ B f hf H`. Establish `hfin : IsFinite (Hom.hom f).left` using `hf.1`. Use `set Z := pullback (Hom.hom f).left η[B.X].left with hZ`. Use `set p : Z ⟶ Sp K := pullback.snd (Hom.hom f).left η[B.X].left with hp`. Establish `: IsFinite p` using `inferInstance`.

Establish `: IsAffine Z` using `isAffine_of_isAffineHom p`. Establish `hnat` using `Scheme.isoSpec_hom_naturality p`. Establish `hS : Spec.map p.appTop = Z.isoSpec.inv ≫ p ≫ (Sp K).isoSpec.hom`. Rewrite using `[← hnat]`. Simplify using the standard rewrite rules.

Establish `hfinS : IsFinite (Spec.map p.appTop)` using `by rw [hS]; infer_instance`. Establish `hfinR : p.appTop.hom.Finite` using `(IsFinite.SpecMap_iff _).1 hfinS`. Set `ψ : CommRingCat.of K ⟶ Γ(Z, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop`. Set `_ : Algebra K Γ(Z, ⊤)` to `ψ.hom.toAlgebra`. Establish `: Module.Finite K Γ(Z, ⊤)`.

Establish `h : ψ.hom.Finite` using `by show (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite`. Conclude with `hfinR.comp (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)`. Conclude with `h`. Establish `hp' : p.appTop = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ ψ` using `by simp [ψ]`. Establish `: IsAffine (𝟙_ (Over (Sp K))).left` using `inferInstanceAs (IsAffine (Sp K))`.

Rewrite using `[HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified), hp', CommRingCat.hom_comp, RingHom.RespectsIso.cancel_left_isIso RingHom.FormallyUnramified.respectsIso]`. Use `show Algebra.FormallyUnramified K Γ(Z, ⊤)`. Use `GlobalTheory.T.formally_unramified_of_dual_numbers K Γ(Z, ⊤) fun φ r => ?_` and prove the remaining obligations. Set `q : Sp (DualNumber K) ⟶ Z` to `Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Z.isoSpec.inv`. Establish `hq : q ≫ p = spMap (algebraMap K (DualNumber K))`.

Establish `e` using `Scheme.isoSpec_inv_naturality p`. Simplify using `only [q, Category.assoc]`. Rewrite using `[← e, Scheme.isoSpec_Spec]`. Simplify using `only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`.

Use `congr 1`. Use `CommRingCat.hom_ext (RingHom.ext fun a => ?_)` and prove the remaining obligations. Conclude with `φ.commutes a`. Establish `hfst : ∀ {T : Scheme} (g : T ⟶ Z), (g ≫ pullback.fst (Hom.hom f).left η[B.X].left) ≫ B.X.hom = g ≫ p`. Introduce `T g`.

Rewrite using `[Category.assoc, ← Over.w (Hom.hom f), ← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc, Over.w η[B.X]]`. Both sides reduce to the same expression. Set `v : epsPtR (𝟙 (Sp K)) ⟶ B.X` to `Over.homMk (q ≫ pullback.fst _ _) (by`. Rewrite using `[hfst, hq]`. Conclude with `(Category.comp_id _).symm)`.

Establish `hv : v ≫ Hom.hom f = 1` using `by ext1`. Rewrite using `[Over.comp_left, Hom.one_def, Over.comp_left]`. Simplify using `only [v, Over.homMk_left, Category.assoc]`. Rewrite using `[pullback.condition, ← Category.assoc q, hq]`. Both sides reduce to the same expression.

Set `T₀ : Over (Sp K)` to `Over.mk (𝟙 (Sp K))`. Set `red : T₀ ⟶ epsPtR (𝟙 (Sp K))` to `Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ ≫ 𝟙 _ = 𝟙 _`. Rewrite using `[Category.comp_id, ← Spec.map_comp, ← Spec.map_id]`. Use `congr 1)`.

Set `bas : epsPtR (𝟙 (Sp K)) ⟶ T₀` to `Over.homMk (spMap (algebraMap K (DualNumber K))) rfl`. Establish `hrb : red ≫ bas = 𝟙 T₀` using `by ext1`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.

Set `w : epsPtR (𝟙 (Sp K)) ⟶ B.X` to `v * (bas ≫ red ≫ v)⁻¹`. Establish `hw₀ : red ≫ w = 1`. Simplify using `only [w]`. Rewrite using `[comp_mul, GrpObj.comp_inv, ← Category.assoc red bas, hrb, Category.id_comp, mul_inv_cancel]`. Establish `hwf : w ≫ Hom.hom f = 1`.

Simplify using `only [w]`. Rewrite using `[mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hv, comp_one, comp_one, inv_one, _root_.mul_one]`. Establish `hw : w = 1` using `H w (by`. Use `congrArg Over.Hom.left hw₀` as an intermediate fact. Rewrite `this` using `[Over.comp_left]`.

Conclude with `this) hwf`. Establish `hvc : v = bas ≫ red ≫ v` using `mul_inv_eq_one.mp hw`. Establish `hq2 : q = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ q`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Use `congrArg Over.Hom.left hvc` as an intermediate fact.

Simplify `this` using `[v, red, bas]`. Express the relevant statement in the definitionally equal form `q ≫ p = _ ≫ _ ≫ q ≫ p`. Rewrite using `[hq, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Simplify using `only [q, ← Category.assoc] at hq2`.

Rewrite `hq2` using `[cancel_mono, ← Spec.map_comp, ← Spec.map_comp]`. Use `congrArg TrivSqZeroExt.snd congr($(Spec.map_injective hq2).hom r)` as an intermediate fact. Simplify `this` using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem formallyUnramified_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  intro K _ _ B f hf H
  have hfin : IsFinite (Hom.hom f).left := hf.1
  set Z := pullback (Hom.hom f).left η[B.X].left with hZ
  set p : Z ⟶ Sp K := pullback.snd (Hom.hom f).left η[B.X].left with hp
  have : IsFinite p := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom p
  have hnat := Scheme.isoSpec_hom_naturality p
  have hS : Spec.map p.appTop = Z.isoSpec.inv ≫ p ≫ (Sp K).isoSpec.hom := by
    rw [← hnat]; simp
  have hfinS : IsFinite (Spec.map p.appTop) := by rw [hS]; infer_instance
  have hfinR : p.appTop.hom.Finite := (IsFinite.SpecMap_iff _).1 hfinS
  let ψ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  let _ : Algebra K Γ(Z, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) := by
    have h : ψ.hom.Finite := by
      show (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite
      exact hfinR.comp (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
    exact h
  have hp' : p.appTop = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ ψ := by simp [ψ]
  have : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified), hp',
    CommRingCat.hom_comp, RingHom.RespectsIso.cancel_left_isIso RingHom.FormallyUnramified.respectsIso]
  show Algebra.FormallyUnramified K Γ(Z, ⊤)
  refine GlobalTheory.T.formally_unramified_of_dual_numbers K Γ(Z, ⊤) fun φ r => ?_

  let q : Sp (DualNumber K) ⟶ Z := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Z.isoSpec.inv
  have hq : q ≫ p = spMap (algebraMap K (DualNumber K)) := by
    have e := Scheme.isoSpec_inv_naturality p
    simp only [q, Category.assoc]
    rw [← e, Scheme.isoSpec_Spec]
    simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact φ.commutes a
  have hfst : ∀ {T : Scheme} (g : T ⟶ Z), (g ≫ pullback.fst (Hom.hom f).left η[B.X].left) ≫ B.X.hom = g ≫ p := by
    intro T g
    rw [Category.assoc, ← Over.w (Hom.hom f), ← Category.assoc (pullback.fst _ _), pullback.condition,
      Category.assoc, Over.w η[B.X]]
    rfl
  let v : epsPtR (𝟙 (Sp K)) ⟶ B.X := Over.homMk (q ≫ pullback.fst _ _) (by
    rw [hfst, hq]; exact (Category.comp_id _).symm)
  have hv : v ≫ Hom.hom f = 1 := by
    ext1
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    simp only [v, Over.homMk_left, Category.assoc]
    rw [pullback.condition, ← Category.assoc q, hq]
    rfl

  let T₀ : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let red : T₀ ⟶ epsPtR (𝟙 (Sp K)) := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_id]
    congr 1)
  let bas : epsPtR (𝟙 (Sp K)) ⟶ T₀ := Over.homMk (spMap (algebraMap K (DualNumber K))) rfl
  have hrb : red ≫ bas = 𝟙 T₀ := by
    ext1
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let w : epsPtR (𝟙 (Sp K)) ⟶ B.X := v * (bas ≫ red ≫ v)⁻¹
  have hw₀ : red ≫ w = 1 := by
    simp only [w]
    rw [comp_mul, GrpObj.comp_inv, ← Category.assoc red bas, hrb, Category.id_comp, mul_inv_cancel]
  have hwf : w ≫ Hom.hom f = 1 := by
    simp only [w]
    rw [mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hv, comp_one, comp_one, inv_one,
      _root_.mul_one]
  have hw : w = 1 := H w (by
    have := congrArg Over.Hom.left hw₀
    rw [Over.comp_left] at this
    exact this) hwf
  have hvc : v = bas ≫ red ≫ v := mul_inv_eq_one.mp hw
  have hq2 : q = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ q := by
    refine pullback.hom_ext ?_ ?_
    · have := congrArg Over.Hom.left hvc
      simpa [v, red, bas] using this
    · change q ≫ p = _ ≫ _ ≫ q ≫ p
      rw [hq, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
  simp only [q, ← Category.assoc] at hq2
  rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at hq2
  have := congrArg TrivSqZeroExt.snd congr($(Spec.map_injective hq2).hom r)
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KerUnram
