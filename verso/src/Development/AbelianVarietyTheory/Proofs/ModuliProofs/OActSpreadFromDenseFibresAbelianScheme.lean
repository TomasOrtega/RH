import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ActSpread

variable {O : Type} [CommRing O] {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Establish `h : i.act 0 * i.act 0 = i.act 0 * 1` using `by rw [← i.add, add_zero, _root_.mul_one]`. Conclude with `mul_left_cancel h`.
-/
theorem act_zero {T : Scheme.{0}} {G : Over T} [GrpObj G] (i : OAct O G) : i.act 0 = 1 := by
  have h : i.act 0 * i.act 0 = i.act 0 * 1 := by rw [← i.add, add_zero, _root_.mul_one]
  exact mul_left_cancel h

/- English proof (translation)
Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← i.add, neg_add_cancel, act_zero]`.
-/
theorem act_neg {T : Scheme.{0}} {G : Over T} [GrpObj G] (i : OAct O G) (x : O) : i.act (-x) = (i.act x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← i.add, neg_add_cancel, act_zero]

section
variable {T : Scheme.{0}} {x : T ⟶ S} {G : Over T} [GrpObj G] {φ : G.left ⟶ A.left}

/- English proof (translation)
Establish `hp : (pushHom hG G u).left = u.left ≫ φ`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `h ext1`. Rewrite using `[hp, h]`.

Simplify using the standard rewrite rules. Introduce `h`. Establish `h'` using `congrArg Over.Hom.left h`. Rewrite `h'` using `[hp]`. Simplify using `using h'`.
-/
theorem compat_iff (hG : IsGrpPullback G A x φ) (u : G ⟶ G) (f : A ⟶ A) :
    u.left ≫ φ = φ ≫ f.left ↔
      pushHom hG G u = (Over.homMk φ hG.1.w : Over.mk (G.hom ≫ x) ⟶ A) ≫ f := by
  have hp : (pushHom hG G u).left = u.left ≫ φ := by
    rfl
  constructor
  · intro h
    ext1
    rw [hp, h]
    simp
  · intro h
    have h' := congrArg Over.Hom.left h
    rw [hp] at h'
    simpa using h'

/- English proof (translation)
Rewrite using `[compat_iff hG, map_one]`. Simplify using the standard rewrite rules.
-/
theorem compat_one (hG : IsGrpPullback G A x φ) : (1 : G ⟶ G).left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  rw [compat_iff hG, map_one]
  simp

/- English proof (translation)
Rewrite `hf`, `hg`, the goal using `[compat_iff hG]`. Rewrite using `[map_mul, hf, hg, comp_mul]`.
-/
theorem compat_mul (hG : IsGrpPullback G A x φ) {u v : G ⟶ G} {f g : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) (hg : v.left ≫ φ = φ ≫ g.left) : (u * v).left ≫ φ = φ ≫ (f * g).left := by
  rw [compat_iff hG] at hf hg ⊢
  rw [map_mul, hf, hg, comp_mul]

/- English proof (translation)
Rewrite `hf`, the goal using `[compat_iff hG]`. Rewrite using `[map_inv, hf, GrpObj.comp_inv]`.
-/
theorem compat_inv (hG : IsGrpPullback G A x φ) {u : G ⟶ G} {f : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) : (u⁻¹).left ≫ φ = φ ≫ (f⁻¹).left := by
  rw [compat_iff hG] at hf ⊢
  rw [map_inv, hf, GrpObj.comp_inv]

omit [GrpObj A] [GrpObj G] in
/- English proof (translation)
Simplify using `only [Over.comp_left, Category.assoc, hg]`. Rewrite using `[reassoc_of% hf]`.
-/
theorem compat_comp {u v : G ⟶ G} {f g : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) (hg : v.left ≫ φ = φ ≫ g.left) : (u ≫ v).left ≫ φ = φ ≫ (f ≫ g).left := by
  simp only [Over.comp_left, Category.assoc, hg]
  rw [reassoc_of% hf]

omit [GrpObj A] [GrpObj G] in
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem compat_id : (𝟙 G : G ⟶ G).left ≫ φ = φ ≫ (𝟙 A : A ⟶ A).left := by
  simp

end

/- English proof (translation)
Establish `m1 : IsMonHom (1 : A ⟶ A)`. Rewrite using `[Hom.one_def]`. Use `infer_instance`. Establish `m2 : ∀ f g : A ⟶ A, IsMonHom f → IsMonHom g → IsMonHom (f * g)` using `fun f g _ _ => by`. Rewrite using `[Hom.mul_def]`.

Use `infer_instance`. Establish `hc : c ∈ Subring.closure (Set.range a)` using `hcl ▸ Subring.mem_top c`. Proceed by induction on `hc using Subring.closure_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`.

Conclude with `⟨act₀ j, hh j, fun _ _ _ _ _ _ _ h => h j⟩`. Consider the case `zero`. Use `⟨1, m1, fun _ _ _ _ _ act hG _ => ?_⟩` and prove the remaining obligations. Rewrite using `[act_zero]`. Conclude with `compat_one hG`.

Consider the case `one`. Use `⟨𝟙 A, inferInstance, fun _ _ _ _ _ act _ _ => ?_⟩` and prove the remaining obligations. Rewrite using `[act.one]`. Conclude with `compat_id`. Consider the case `add y z _ _ hy hz`.

Take `⟨f, hf, Hf⟩` from `hy`. Take `⟨g, hg, Hg⟩` from `hz`. Use `⟨f * g, m2 f g hf hg, fun T x G _ φ act hG h => ?_⟩` and prove the remaining obligations. Rewrite using `[act.add]`. Conclude with `compat_mul hG (Hf T x G φ act hG h) (Hg T x G φ act hG h)`.

Consider the case `neg y _ hy`. Take `⟨f, hf, Hf⟩` from `hy`. Use `⟨f⁻¹, inferInstance, fun T x G _ φ act hG h => ?_⟩` and prove the remaining obligations. Rewrite using `[act_neg]`. Conclude with `compat_inv hG (Hf T x G φ act hG h)`.

Consider the case `mul y z _ _ hy hz`. Take `⟨f, hf, Hf⟩` from `hy`. Take `⟨g, hg, Hg⟩` from `hz`. Use `⟨f ≫ g, inferInstance, fun T x G _ φ act hG h => ?_⟩` and prove the remaining obligations. Rewrite using `[act.mul]`.

Conclude with `compat_comp (Hf T x G φ act hG h) (Hg T x G φ act hG h)`.
-/
theorem exists_universal [IsCommMonObj A] {J : Type} (a : J → O) (act₀ : J → (A ⟶ A))
    (hcl : Subring.closure (Set.range a) = ⊤) (hh : ∀ j, IsMonHom (act₀ j)) (c : O) :
    ∃ f : A ⟶ A, IsMonHom f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left)
      (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) →
      (act.act c).left ≫ φ = φ ≫ f.left := by
  have m1 : IsMonHom (1 : A ⟶ A) := by
    rw [Hom.one_def]; infer_instance
  have m2 : ∀ f g : A ⟶ A, IsMonHom f → IsMonHom g → IsMonHom (f * g) := fun f g _ _ => by
    rw [Hom.mul_def]; infer_instance
  have hc : c ∈ Subring.closure (Set.range a) := hcl ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact ⟨act₀ j, hh j, fun _ _ _ _ _ _ _ h => h j⟩
  | zero =>
    refine ⟨1, m1, fun _ _ _ _ _ act hG _ => ?_⟩
    rw [act_zero]
    exact compat_one hG
  | one =>
    refine ⟨𝟙 A, inferInstance, fun _ _ _ _ _ act _ _ => ?_⟩
    rw [act.one]
    exact compat_id
  | add y z _ _ hy hz =>
    obtain ⟨f, hf, Hf⟩ := hy
    obtain ⟨g, hg, Hg⟩ := hz
    refine ⟨f * g, m2 f g hf hg, fun T x G _ φ act hG h => ?_⟩
    rw [act.add]
    exact compat_mul hG (Hf T x G φ act hG h) (Hg T x G φ act hG h)
  | neg y _ hy =>
    obtain ⟨f, hf, Hf⟩ := hy
    refine ⟨f⁻¹, inferInstance, fun T x G _ φ act hG h => ?_⟩
    rw [act_neg]
    exact compat_inv hG (Hf T x G φ act hG h)
  | mul y z _ _ hy hz =>
    obtain ⟨f, hf, Hf⟩ := hy
    obtain ⟨g, hg, Hg⟩ := hz
    refine ⟨f ≫ g, inferInstance, fun T x G _ φ act hG h => ?_⟩
    rw [act.mul]
    exact compat_comp (Hf T x G φ act hG h) (Hg T x G φ act hG h)

omit [GrpObj A] in

/- English proof (translation)
Establish `hred : IsReduced A.left` using `GlobalTheory.isReduced_of_smooth_of_isReduced A.hom`. Establish `hw : f.left ≫ A.hom = g.left ≫ A.hom` using `by rw [Over.w f, Over.w g]`. Take `⟨-, -, H3⟩` from `GlobalTheory.dense_fibres_ext A.left S A.hom D hD`. Establish `hin : ∀ y : A.left, A.hom y ∈ D → pullback.lift f.left g.left hw y ∈ Set.range (pullback.diagonal A.hom)`. Introduce `y hy`.

Take `⟨T, P, x, q, φ, ⟨t, ht⟩, hpb, hφ⟩` from `H _ hy`. Establish `key : φ ≫ pullback.lift f.left g.left hw = (φ ≫ f.left) ≫ pullback.diagonal A.hom`. Apply the tactic sequence `apply pullback.hom_ext <;>`. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, hφ]`. Establish `hy' : y ∈ Set.range (pullback.fst A.hom x)`.

Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `⟨t, ht⟩`. Take `⟨z, hz⟩` from `hy'`. Establish `hinv : hpb.isoPullback.inv ≫ φ = pullback.fst A.hom x`. Conclude with `hpb.isoPullback_inv_fst`.

Use `⟨(φ ≫ f.left) (hpb.isoPullback.inv z), ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← key, Scheme.Hom.comp_apply, ← hz, ← hinv, Scheme.Hom.comp_apply]`. Take `⟨e, he⟩` from `H3 _ _ (pullback.diagonal A.hom) (pullback.lift f.left g.left hw) hin`. Establish `e1` using `congrArg (· ≫ pullback.fst A.hom A.hom) he`. Establish `e2` using `congrArg (· ≫ pullback.snd A.hom A.hom) he`.

Simplify using `only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, pullback.lift_fst, pullback.lift_snd] at e1 e2`. Use `ext1`. Rewrite using `[← e1, ← e2]`.
-/
theorem ext_of_dense [IsReduced S] [Smooth A.hom] [IsSeparated A.hom] (f g : A ⟶ A) (D : Set S) (hD : Dense D)
    (H : ∀ p ∈ D, ∃ (T P : Scheme.{0}) (x : T ⟶ S) (q : P ⟶ T) (φ : P ⟶ A.left), p ∈ Set.range x ∧
      IsPullback φ q A.hom x ∧ φ ≫ f.left = φ ≫ g.left) : f = g := by
  have hred : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : f.left ≫ A.hom = g.left ≫ A.hom := by rw [Over.w f, Over.w g]
  obtain ⟨-, -, H3⟩ := GlobalTheory.dense_fibres_ext A.left S A.hom D hD
  have hin : ∀ y : A.left, A.hom y ∈ D → pullback.lift f.left g.left hw y ∈ Set.range (pullback.diagonal A.hom) := by
    intro y hy
    obtain ⟨T, P, x, q, φ, ⟨t, ht⟩, hpb, hφ⟩ := H _ hy
    have key : φ ≫ pullback.lift f.left g.left hw = (φ ≫ f.left) ≫ pullback.diagonal A.hom := by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
          pullback.diagonal_snd, Category.comp_id, hφ]
    have hy' : y ∈ Set.range (pullback.fst A.hom x) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    obtain ⟨z, hz⟩ := hy'
    have hinv : hpb.isoPullback.inv ≫ φ = pullback.fst A.hom x := by
      exact hpb.isoPullback_inv_fst
    refine ⟨(φ ≫ f.left) (hpb.isoPullback.inv z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← key, Scheme.Hom.comp_apply, ← hz, ← hinv, Scheme.Hom.comp_apply]
  obtain ⟨e, he⟩ := H3 _ _ (pullback.diagonal A.hom) (pullback.lift f.left g.left hw) hin
  have e1 := congrArg (· ≫ pullback.fst A.hom A.hom) he
  have e2 := congrArg (· ≫ pullback.snd A.hom A.hom) he
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at e1 e2
  ext1
  rw [← e1, ← e2]

end GlobalTheory.ActSpread

namespace GlobalTheory

open ActSpread in

/- English proof (translation)
Introduce `O _ J a S _ A _ act₀ hcl hab hh hD`. Take `⟨hcomm, hsm, hpr, -⟩` from `hab`. Use `choose F hF HF using fun c => ActSpread.exists_universal a act₀ hcl hh c`. Establish `ext : ∀ f g : A ⟶ A, (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (G : Over (Sp K)) [GrpObj G] (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → φ ≫ f.left = φ ≫ g.left) → f = g`. Introduce `f g H`.

Use `ActSpread.ext_of_dense f g _ hD ?_` and prove the remaining obligations. Introduce and unpack `p ⟨K, _, x, G, _, φ, act, hp, hG, hc⟩`. Conclude with `⟨Sp K, G.left, x, G.hom, φ, hp, hG.1, H K x G φ act hG hc⟩`. Use `⟨⟨F, hF, ?_, ?_, ?_⟩, ?_, fun T x G _ φ act hG hc c => HF c T x G φ act hG hc⟩` and prove the remaining obligations. Use `ext _ _ fun K _ x G _ φ act hG hc => ?_` and prove the remaining obligations.

Rewrite using `[← HF 1 _ x G φ act hG hc, act.one]`. Conclude with `ActSpread.compat_id`. Introduce `b c`. Use `ext _ _ fun K _ x G _ φ act hG hc => ?_` and prove the remaining obligations. Rewrite using `[← HF (b * c) _ x G φ act hG hc, act.mul]`.

Conclude with `ActSpread.compat_comp (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)`. Introduce `b c`. Use `ext _ _ fun K _ x G _ φ act hG hc => ?_` and prove the remaining obligations. Rewrite using `[← HF (b + c) _ x G φ act hG hc, act.add]`. Conclude with `ActSpread.compat_mul hG (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)`.

Introduce `j`. Use `ext _ _ fun K _ x G _ φ act hG hc => ?_` and prove the remaining obligations. Rewrite using `[← HF (a j) _ x G φ act hG hc]`. Conclude with `hc j`.
-/
theorem oAct_spread_of_dense_fibres : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] (act₀ : J → (A ⟶ A)), Subring.closure (Set.range a) = ⊤ → IsAbelianScheme A → (∀ j, IsMonHom (act₀ j)) → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (φ : G.left ⟶ A.left) (act : OAct O G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ ∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left} → ∃ r : OAct O A, (∀ j, r.act (a j) = act₀ j) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  intro O _ J a S _ A _ act₀ hcl hab hh hD
  obtain ⟨hcomm, hsm, hpr, -⟩ := hab
  choose F hF HF using fun c => ActSpread.exists_universal a act₀ hcl hh c
  have ext : ∀ f g : A ⟶ A, (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (G : Over (Sp K)) [GrpObj G]
      (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ →
      (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → φ ≫ f.left = φ ≫ g.left) → f = g := by
    intro f g H
    refine ActSpread.ext_of_dense f g _ hD ?_
    rintro p ⟨K, _, x, G, _, φ, act, hp, hG, hc⟩
    exact ⟨Sp K, G.left, x, G.hom, φ, hp, hG.1, H K x G φ act hG hc⟩
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, ?_, fun T x G _ φ act hG hc c => HF c T x G φ act hG hc⟩
  · refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF 1 _ x G φ act hG hc, act.one]
    exact ActSpread.compat_id
  · intro b c
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (b * c) _ x G φ act hG hc, act.mul]
    exact ActSpread.compat_comp (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)
  · intro b c
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (b + c) _ x G φ act hG hc, act.add]
    exact ActSpread.compat_mul hG (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)
  · intro j
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (a j) _ x G φ act hG hc]
    exact hc j

end GlobalTheory
