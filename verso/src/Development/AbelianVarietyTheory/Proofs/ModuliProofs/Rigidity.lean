import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.EpsAct

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Subsingleton (PrimeSpectrum (DualNumber k))`. Establish `key : ∀ (p : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ p.asIdeal ↔ x.fst = 0`. Introduce `p x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Assume the negation of the conclusion as `h`. Conclude with `p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)))`. Introduce `h`. Apply `p.isPrime.mem_of_pow_mem 2` to reduce the goal to its premises. Establish `hx : x = TrivSqZeroExt.inr x.snd` using `TrivSqZeroExt.ext (by simp [h]) (by simp)`.

Rewrite using `[hx, pow_two]`. Simplify using the standard rewrite rules. Conclude with `⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => (key p x).trans (key q x).symm)⟩`.
-/
theorem subsingleton_sp_dualNumber (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  change Subsingleton (PrimeSpectrum (DualNumber k))
  have key : ∀ (p : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)))
    · intro h
      apply p.isPrime.mem_of_pow_mem 2
      have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      rw [hx, pow_two]
      simp
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => (key p x).trans (key q x).symm)⟩

/- English proof (translation)
Establish `hsurj : Function.Surjective A'.hom.appTop.hom` using `(hL.globalFns _ A' hA).2`. Use `set d : A' ⟶ G' := a * b⁻¹ with hd`. Establish `hsub : Subsingleton (Sp (DualNumber k))` using `subsingleton_sp_dualNumber k`. Establish `hjs : Function.Surjective j.base`. Establish `hs0 : Surjective (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)`.

Prove the components needed by the constructor for the conclusion. Introduce `y`. Choose the witnesses or unpack the hypotheses as in `⟨q⟩ : Nonempty (Sp k) := by`. Express the relevant statement in the definitionally equal form `Nonempty (PrimeSpectrum k)`. Use `infer_instance`.

Conclude with `⟨q, Subsingleton.elim _ _⟩`. Conclude with `(MorphismProperty.of_isPullback (P := @Surjective) hj.flip hs0).surj`. Establish `key : ∀ {W : Over (Sp (DualNumber k))} (u : W ⟶ A'), u ≫ a = u ≫ b → u ≫ d = 1`. Introduce `W u h`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, h, mul_inv_cancel]`.

Establish `hjd : j ≫ d.left = (toUnit (Over.mk (j ≫ A'.hom))).left ≫ η[G'].left`. Establish `h1` using `congrArg (fun f => Over.Hom.left f) (key (Over.homMk j rfl : Over.mk (j ≫ A'.hom) ⟶ A') (by ext; exact hab))`. Simplify `h1` using `[Hom.one_def]`. Choose the witnesses or unpack the hypotheses as in `⟨pt⟩ : Nonempty ((𝟙_ (Over (Sp (DualNumber k)))).left) := by`. Choose the witnesses or unpack the hypotheses as in `⟨q⟩ : Nonempty (Sp k) := by`.

Express the relevant statement in the definitionally equal form `Nonempty (PrimeSpectrum k)`. Use `infer_instance`. Conclude with `⟨(spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base q⟩`. Establish `hsub1 : Subsingleton ((𝟙_ (Over (Sp (DualNumber k)))).left)` using `hsub`. Establish `hy : ∀ x, d.left x = η[G'].left pt`.

Introduce `x`. Take `⟨z, rfl⟩` from `hjs x`. Establish `h2` using `congrArg (fun f : Z ⟶ G'.left => f z) hjd`. Simplify using `only [Scheme.Hom.comp_apply] at h2`. Rewrite using `[h2]`.

Conclude with `congrArg _ (Subsingleton.elim _ _)`. Establish `hfac` using `GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom η[A'].left d.left (by simp) hsurj _ hy`. Establish `hη' : η[A'] ≫ d = 1` using `key _ hη`. Establish `hd2 : d = toUnit A' ≫ η[A'] ≫ d`. Use `ext`.

Conclude with `hfac`. Establish `hd1 : d = 1`. Rewrite using `[hd2, hη']`. Simplify using the standard rewrite rules. Conclude with `mul_inv_eq_one.1 hd1`.
-/
theorem rigidity (hL : Out.Laws) (k : Type) [Field k] {Z : Scheme.{0}} (c₀ : Z ⟶ Sp k)
    (A' G' : Over (Sp (DualNumber k))) [GrpObj A'] [GrpObj G'] (j : Z ⟶ A'.left) (a b : A' ⟶ G')
    (hA : IsAbelianScheme A')
    (hj : IsPullback j c₀ A'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  classical
  have hsurj : Function.Surjective A'.hom.appTop.hom := (hL.globalFns _ A' hA).2
  set d : A' ⟶ G' := a * b⁻¹ with hd
  have hsub : Subsingleton (Sp (DualNumber k)) := subsingleton_sp_dualNumber k
  have hjs : Function.Surjective j.base := by
    have hs0 : Surjective (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      constructor
      intro y
      obtain ⟨q⟩ : Nonempty (Sp k) := by
        change Nonempty (PrimeSpectrum k)
        infer_instance
      exact ⟨q, Subsingleton.elim _ _⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) hj.flip hs0).surj
  have key : ∀ {W : Over (Sp (DualNumber k))} (u : W ⟶ A'), u ≫ a = u ≫ b → u ≫ d = 1 := by
    intro W u h
    rw [MonObj.comp_mul, GrpObj.comp_inv, h, mul_inv_cancel]
  have hjd : j ≫ d.left = (toUnit (Over.mk (j ≫ A'.hom))).left ≫ η[G'].left := by
    have h1 := congrArg (fun f => Over.Hom.left f)
      (key (Over.homMk j rfl : Over.mk (j ≫ A'.hom) ⟶ A') (by ext; exact hab))
    simpa [Hom.one_def] using h1
  obtain ⟨pt⟩ : Nonempty ((𝟙_ (Over (Sp (DualNumber k)))).left) := by
    obtain ⟨q⟩ : Nonempty (Sp k) := by
      change Nonempty (PrimeSpectrum k)
      infer_instance
    exact ⟨(spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base q⟩
  have hsub1 : Subsingleton ((𝟙_ (Over (Sp (DualNumber k)))).left) := hsub
  have hy : ∀ x, d.left x = η[G'].left pt := by
    intro x
    obtain ⟨z, rfl⟩ := hjs x
    have h2 := congrArg (fun f : Z ⟶ G'.left => f z) hjd
    simp only [Scheme.Hom.comp_apply] at h2
    rw [h2]
    exact congrArg _ (Subsingleton.elim _ _)
  have hfac := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom η[A'].left d.left
    (by simp) hsurj _ hy
  have hη' : η[A'] ≫ d = 1 := key _ hη
  have hd2 : d = toUnit A' ≫ η[A'] ≫ d := by
    ext
    exact hfac
  have hd1 : d = 1 := by
    rw [hd2, hη']
    simp
  exact mul_inv_eq_one.1 hd1

/- English proof (translation)
Introduce `hL E _ _ _ H k _ T t x t' ν φ hP hpb hag a`. Establish `hsq` using `hpb.1`. Establish `hprop : IsProper t'.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) hsq hP`. Establish `hs` using `t'.semi`. Establish `hA : IsAbelianScheme t'.G` using `{ comm := hs.comm, smooth := hs.smooth, proper := hprop, geomConnected := hs.geomConnected }`.

Establish `hα : ((t'.act.act a).left ≫ φ) ≫ t.G.hom = t'.G.hom ≫ constPt x`. Rewrite using `[Category.assoc, hsq.w, ← Category.assoc, Over.w]`. Establish `hβ : (φ ≫ (t.act.act a).left) ≫ t.G.hom = t'.G.hom ≫ constPt x`. Rewrite using `[Category.assoc, Over.w, hsq.w]`. Set `A : t'.G ⟶ t'.G` to `Over.homMk (hsq.lift _ _ hα) (hsq.lift_snd _ _ _)`.

Set `B : t'.G ⟶ t'.G` to `Over.homMk (hsq.lift _ _ hβ) (hsq.lift_snd _ _ _)`. Establish `e3 : (t'.act.act a).left ≫ ν.φ = ν.φ ≫ (t.act.act a).left` using `ν.act a`. Establish `hj` using `IsPullback.of_hasPullback t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)`. Establish `hab : pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ A.left = pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ B.left`. Apply `hsq.hom_ext` to reduce the goal to its premises.

Simplify using `only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]`. Establish `e1` using `hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) hj.w`. Establish `e2` using `hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t'.act.act a).left) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (by rw [Category.assoc, Over.w]; exact hj.w)`. Rewrite using `[← Category.assoc, e2, Category.assoc, e3, ← Category.assoc, ← e1, Category.assoc]`. Simplify using `only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]`.

Set `e : Over.mk ((𝟙_ (Over (Sp (DualNumber k)))).hom ≫ constPt x) ⟶ t.G` to `Over.homMk (η[t'.G].left ≫ φ) (by rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]; rfl)`. Establish `hη1 : (η[t'.G] : 𝟙_ _ ⟶ t'.G) = 1` using `by simp [Hom.one_def]`. Establish `he1 : e = 1`. Establish `hm` using `hpb.2 _ η[t'.G] η[t'.G] e e rfl rfl`. Rewrite `hm` using `[hη1, _root_.mul_one]`.

Establish `hee : e * e = e`. Use `ext`. Rewrite using `[hm, ← hη1]`. Both sides reduce to the same expression. Conclude with `_root_.mul_eq_left.1 hee`.

Establish `he2 : e ≫ t.act.act a = e`. Use `t.act.hom a` as an intermediate fact. Rewrite using `[he1, Hom.one_def, Category.assoc, IsMonHom.one_hom]`. Establish `he3` using `congrArg Over.Hom.left he2`. Establish `hm1 : η[t'.G] ≫ t'.act.act a = η[t'.G]`.

Use `t'.act.hom a` as an intermediate fact. Conclude with `IsMonHom.one_hom _`. Establish `hm2` using `congrArg Over.Hom.left hm1`. Establish `hη : η[t'.G] ≫ A = η[t'.G] ≫ B`. Use `ext`.

Simplify using `only [Over.comp_left]`. Apply `hsq.hom_ext` to reduce the goal to its premises. Simplify using `only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]`. Simplify using `only [e, Over.comp_left, Over.homMk_left, Category.assoc] at he3 hm2`. Rewrite using `[← Category.assoc, hm2, he3]`.

Simplify using `only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]`. Establish `hAB` using `rigidity hL k (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) t'.G t'.G (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) A B hA hj hab hη`. Establish `hL'` using `congrArg Over.Hom.left hAB`. Simplify using `only [A, B, Over.homMk_left] at hL'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T : Scheme.{0}) (t : SAB H T) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G (constPt x) φ → (∀ (Z : Scheme.{0}) (j : Z ⟶ t'.G.left) (c : Z ⟶ Sp k), j ≫ t'.G.hom = c ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → j ≫ φ = j ≫ ν.φ) → ∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  intro hL E _ _ _ H k _ T t x t' ν φ hP hpb hag a
  have hsq := hpb.1
  have hprop : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq hP
  have hs := t'.semi
  have hA : IsAbelianScheme t'.G :=
    { comm := hs.comm, smooth := hs.smooth, proper := hprop, geomConnected := hs.geomConnected }
  have hα : ((t'.act.act a).left ≫ φ) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]
  have hβ : (φ ≫ (t.act.act a).left) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, Over.w, hsq.w]
  let A : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hα) (hsq.lift_snd _ _ _)
  let B : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hβ) (hsq.lift_snd _ _ _)
  have e3 : (t'.act.act a).left ≫ ν.φ = ν.φ ≫ (t.act.act a).left := ν.act a
  have hj := IsPullback.of_hasPullback t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  have hab : pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ A.left = pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ B.left := by
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      have e1 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) hj.w
      have e2 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t'.act.act a).left) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
        (by rw [Category.assoc, Over.w]; exact hj.w)
      rw [← Category.assoc, e2, Category.assoc, e3, ← Category.assoc, ← e1, Category.assoc]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  let e : Over.mk ((𝟙_ (Over (Sp (DualNumber k)))).hom ≫ constPt x) ⟶ t.G :=
    Over.homMk (η[t'.G].left ≫ φ) (by rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]; rfl)
  have hη1 : (η[t'.G] : 𝟙_ _ ⟶ t'.G) = 1 := by simp [Hom.one_def]
  have he1 : e = 1 := by
    have hm := hpb.2 _ η[t'.G] η[t'.G] e e rfl rfl
    rw [hη1, _root_.mul_one] at hm
    have hee : e * e = e := by
      ext
      rw [hm, ← hη1]
      rfl
    exact _root_.mul_eq_left.1 hee
  have he2 : e ≫ t.act.act a = e := by
    have := t.act.hom a
    rw [he1, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have he3 := congrArg Over.Hom.left he2
  have hm1 : η[t'.G] ≫ t'.act.act a = η[t'.G] := by
    have := t'.act.hom a
    exact IsMonHom.one_hom _
  have hm2 := congrArg Over.Hom.left hm1
  have hη : η[t'.G] ≫ A = η[t'.G] ≫ B := by
    ext
    simp only [Over.comp_left]
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      simp only [e, Over.comp_left, Over.homMk_left, Category.assoc] at he3 hm2
      rw [← Category.assoc, hm2, he3]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  have hAB := rigidity hL k (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) t'.G t'.G (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) A B hA hj hab hη
  have hL' := congrArg Over.Hom.left hAB
  simp only [A, B, Over.homMk_left] at hL'
  calc (t'.act.act a).left ≫ φ = hsq.lift _ _ hα ≫ φ := (hsq.lift_fst _ _ _).symm
    _ = hsq.lift _ _ hβ ≫ φ := by rw [hL']
    _ = φ ≫ (t.act.act a).left := hsq.lift_fst _ _ _

end GlobalTheory.EpsAct
