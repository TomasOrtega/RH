import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace TripleHodge

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

/- English proof (translation)
The claim follows from `congrArg (fun p => p.left) (map_one (pushHom h T))`.
-/
theorem one_left_comp (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
  congrArg (fun p => p.left) (map_one (pushHom h T))

/- English proof (translation)
Establish `one` using `one_left_comp h (Over.mk z)`. Establish `wv` using `Over.w v'`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Unfold `IsTanAt at hv ⊢`.

Rewrite using `[e, ← Category.assoc, hv]`. Conclude with `one`. Introduce `hv`. Unfold `IsTanAt at hv ⊢`. Apply `h.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, ← e, hv]`. Conclude with `one.symm`. Establish `w1` using `Over.w (1 : Over.mk z ⟶ G')`. Rewrite using `[Category.assoc, w1, wv]`. Use `show Spec.map _ ≫ Spec.map _ ≫ z = z`.

Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Establish `e₁ : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[e₁, Spec.map_id, Category.id_comp]`.
-/
theorem isTanAt_iff (h : IsGrpPullback G' G f φ) (z : Spec (CommRingCat.of ℂ) ⟶ S') (v' : epsAt z ⟶ G')
    (v : epsAt (z ≫ f) ⟶ G) (e : v.left = v'.left ≫ φ) : IsTanAt G' z v' ↔ IsTanAt G (z ≫ f) v := by
  have one := one_left_comp h (Over.mk z)
  have wv := Over.w v'
  constructor
  · intro hv
    unfold IsTanAt at hv ⊢
    rw [e, ← Category.assoc, hv]
    exact one
  · intro hv
    unfold IsTanAt at hv ⊢
    apply h.1.hom_ext
    · rw [Category.assoc, ← e, hv]
      exact one.symm
    · have w1 := Over.w (1 : Over.mk z ⟶ G')
      rw [Category.assoc, w1, wv]
      show Spec.map _ ≫ Spec.map _ ≫ z = z
      rw [← Category.assoc, ← Spec.map_comp]
      have e₁ : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext x
        simp
      rw [e₁, Spec.map_id, Category.id_comp]

variable {X X' : Scheme.{0}}

/- English proof (translation)
Establish `hP : (L'.pull p).IsLB` using `pull_isLB hL' p`. Establish `hr` using `(isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)`. Establish `hw'` using `(isGen_iff _).1 hw`. Take `⟨w₂, T⟩` from `exists_comp hL' w _ hw' hr hL hP`. Conclude with `⟨w₂, (isGen_iff _).2 (T.pgen_comp hL' hw' hr)⟩`.
-/
theorem exists_iso_comp {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L'.pull p) (L.pull (p ≫ F)), w₂.IsGen := by
  have hP : (L'.pull p).IsLB := pull_isLB hL' p
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_comp hL' w _ hw' hr hL hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_comp hL' hw' hr)⟩

/- English proof (translation)
Establish `hP : (L.pull (p ≫ F)).IsLB` using `pull_isLB hL (p ≫ F)`. Establish `hr` using `(isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)`. Establish `hw'` using `(isGen_iff _).1 hw`. Take `⟨w₂, T⟩` from `exists_cancel hL w _ hw' hr hL' hP`. Conclude with `⟨w₂, (isGen_iff _).2 (T.pgen_cancel hL hw' hr)⟩`.
-/
theorem exists_iso_cancel {Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (p : Y ⟶ X') :
    ∃ w₂ : LB.Iso (L.pull (p ≫ F)) (L'.pull p), w₂.IsGen := by
  have hP : (L.pull (p ≫ F)).IsLB := pull_isLB hL (p ≫ F)
  have hr := (isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl hP)
  have hw' := (isGen_iff _).1 hw
  obtain ⟨w₂, T⟩ := exists_cancel hL w _ hw' hr hL' hP
  exact ⟨w₂, (isGen_iff _).2 (T.pgen_cancel hL hw' hr)⟩

end TripleHodge

/- English proof (translation)
Introduce `E _ _ _ H X t X' t' f m z v' w' v w c hv hw`. Take `⟨i, hi, -, -⟩` from `m.lin`. Establish `tv` using `TripleHodge.isTanAt_iff m.cart z v' v hv`. Establish `tw` using `TripleHodge.isTanAt_iff m.cart z w' w hw`. Establish `hL` using `t.PP.isLB`.

Establish `hL'` using `t'.PP.isLB`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h₁, h₂, A, _, φ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩`. Take `⟨i₂, hi₂⟩` from `TripleHodge.exists_iso_comp hL hL' hi φ`. Establish `hP` using `pull_isLB hL' φ`.

Establish `hQ` using `pull_isLB hL (φ ≫ m.φ)`. Use `⟨hL, tv.1 h₁, tw.1 h₂, A, inferInstance, φ ≫ m.φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ, a', b', a, b, p₁.comp m.cart, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂, ?_, ?_, p₅, p₆, rfl⟩` and prove the remaining obligations. Rewrite using `[hv, ← p₃, Category.assoc]`. Rewrite using `[hw, ← p₄, Category.assoc]`. Introduce and unpack `⟨-, h₁, h₂, A, _, ψ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩`.

Take `⟨φ, rfl, hφ⟩ : ∃ φ : A.left ⟶ t'.G.left, φ ≫ m.φ = ψ ∧ φ ≫ t'.G.hom = A.hom ≫ z` from `⟨m.cart.1.lift ψ (A.hom ≫ z) (by rw [p₁.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩`. Take `⟨i₂, hi₂⟩` from `TripleHodge.exists_iso_cancel hL hL' hi φ`. Establish `hP` using `pull_isLB hL (φ ≫ m.φ)`. Establish `hQ` using `pull_isLB hL' φ`. Establish `lift : ∀ (x : epsR ℂ ⟶ A) (y : epsAt z ⟶ t'.G) (y₀ : epsAt (z ≫ f) ⟶ t.G), y₀.left = y.left ≫ m.φ → x.left ≫ φ ≫ m.φ = y₀.left → x.left ≫ φ = y.left`.

Introduce `x y y₀ e e'`. Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, e', e]`. Rewrite using `[Category.assoc, hφ, ← Category.assoc, Over.w x, Over.w y]`. Both sides reduce to the same expression.

Conclude with `⟨hL', tv.2 h₁, tw.2 h₂, A, inferInstance, φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ, a', b', a, b, IsGrpPullback.cancel m.cart p₁ hφ, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂, lift a' v' v hv p₃, lift b' w' w hw p₄, p₅, p₆, rfl⟩`.
-/
theorem hodgeInnerProduct_tripleMap_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ),
    v.left = v'.left ≫ m.φ → w.left = w'.left ≫ m.φ →
      (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  intro E _ _ _ H X t X' t' f m z v' w' v w c hv hw
  obtain ⟨i, hi, -, -⟩ := m.lin
  have tv := TripleHodge.isTanAt_iff m.cart z v' v hv
  have tw := TripleHodge.isTanAt_iff m.cart z w' w hw
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  constructor
  · rintro ⟨-, h₁, h₂, A, _, φ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_comp hL hL' hi φ
    have hP := pull_isLB hL' φ
    have hQ := pull_isLB hL (φ ≫ m.φ)
    refine ⟨hL, tv.1 h₁, tw.1 h₂, A, inferInstance, φ ≫ m.φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, p₁.comp m.cart, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂, ?_, ?_, p₅, p₆, rfl⟩
    · rw [hv, ← p₃, Category.assoc]
    · rw [hw, ← p₄, Category.assoc]
  · rintro ⟨-, h₁, h₂, A, _, ψ, g, u, Hm, χ, a', b', a, b, p₁, p₂, p₃, p₄, p₅, p₆, rfl⟩
    obtain ⟨φ, rfl, hφ⟩ : ∃ φ : A.left ⟶ t'.G.left, φ ≫ m.φ = ψ ∧ φ ≫ t'.G.hom = A.hom ≫ z :=
      ⟨m.cart.1.lift ψ (A.hom ≫ z) (by rw [p₁.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
    obtain ⟨i₂, hi₂⟩ := TripleHodge.exists_iso_cancel hL hL' hi φ
    have hP := pull_isLB hL (φ ≫ m.φ)
    have hQ := pull_isLB hL' φ
    have lift : ∀ (x : epsR ℂ ⟶ A) (y : epsAt z ⟶ t'.G) (y₀ : epsAt (z ≫ f) ⟶ t.G), y₀.left = y.left ≫ m.φ →
        x.left ≫ φ ≫ m.φ = y₀.left → x.left ≫ φ = y.left := by
      intro x y y₀ e e'
      apply m.cart.1.hom_ext
      · rw [Category.assoc, e', e]
      · rw [Category.assoc, hφ, ← Category.assoc, Over.w x, Over.w y]
        rfl
    exact ⟨hL', tv.2 h₁, tw.2 h₂, A, inferInstance, φ, g, GlobalTheory.TorsionTauCompare.transport hP hQ hi₂ u, Hm, χ,
      a', b', a, b, IsGrpPullback.cancel m.cart p₁ hφ, GlobalTheory.TorsionTauCompare.isAH_transport hP hQ hi₂ u p₂,
      lift a' v' v hv p₃, lift b' w' w hw p₄, p₅, p₆, rfl⟩

end GlobalTheory.CompanionTheory.Ar
