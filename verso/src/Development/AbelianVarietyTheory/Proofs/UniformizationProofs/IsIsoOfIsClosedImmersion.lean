import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsoLimit

open ThickeningClosed

/- English proof (translation)
Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian f`. Establish `key : ∀ x, x ∈ zeroLocusOpen j.ker`. Introduce `x`. Assume the negation of the conclusion as `hx`. Establish `hc : IsClosed (f '' (zeroLocusOpen j.ker)ᶜ)` using `f.isClosedMap _ (isOpen_zeroLocusOpen _).isClosed_compl`.

Take `⟨y, hy, hy'⟩` from `(IsLocalRing.specializes_closedPoint (R := V) (f x)).mem_closed hc ⟨x, hx, rfl⟩`. Use `hy (mem_of_thickenings _ f j h y ?_)` and prove the remaining obligations. Rewrite using `[hy']`. Conclude with `le_rfl`. Rewrite using `[IsClosedImmersion.isIso_iff_ker_eq_bot]`.

Use `le_bot_iff.1 fun U a ha ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a = 0`. Use `eq_zero_of_localization a fun J hJ ↦ ?_` and prove the remaining obligations. Take `⟨s, hs, hsa⟩` from `exists_mul_eq_zero_of_mem j.ker U ⟨J, hJ.isPrime⟩ (key _) ha`. Conclude with `(IsLocalization.map_eq_zero_iff J.primeCompl _ a).2 ⟨⟨s, hs⟩, hsa⟩`.
-/
theorem isIso_of_isClosedImmersion {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f] (j : Z ⟶ X)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : pullback f (thick V (IsLocalRing.maximalIdeal V) n) ⟶ Z,
      l ≫ j = pullback.fst f (thick V (IsLocalRing.maximalIdeal V) n)) : IsIso j := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have key : ∀ x, x ∈ zeroLocusOpen j.ker := by
    intro x
    by_contra hx
    have hc : IsClosed (f '' (zeroLocusOpen j.ker)ᶜ) :=
      f.isClosedMap _ (isOpen_zeroLocusOpen _).isClosed_compl
    obtain ⟨y, hy, hy'⟩ :=
      (IsLocalRing.specializes_closedPoint (R := V) (f x)).mem_closed hc ⟨x, hx, rfl⟩
    refine hy (mem_of_thickenings _ f j h y ?_)
    rw [hy']
    exact le_rfl
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  refine le_bot_iff.1 fun U a ha ↦ ?_
  change a = 0
  refine eq_zero_of_localization a fun J hJ ↦ ?_
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem j.ker U ⟨J, hJ.isPrime⟩ (key _) ha
  exact (IsLocalization.map_eq_zero_iff J.primeCompl _ a).2 ⟨⟨s, hs⟩, hsa⟩

/- English proof (translation)
Introduce `V _ _ _ _ Γ₁ Y p _ _ h`. Establish `hw : p.left ≫ Y.hom = Γ₁.hom` using `Over.w p`. Set `q (e : ℕ) : pullback Γ₁.hom (thick V (IsLocalRing.maximalIdeal V) e) ⟶ pullback Y.hom (thick V (IsLocalRing.maximalIdeal V) e)` to `((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p).left`. Establish `hq (e : ℕ) : IsIso (q e)` using `by haveI := h e`. Conclude with `inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)))`.

Establish `q1 (e : ℕ) : q e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p.left` using `pullback.lift_fst _ _ _`. Establish `q2 (e : ℕ) : q e ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `hd : IsIso (pullback.diagonal p.left)`. Use `isIso_of_isClosedImmersion (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) _ fun n ↦ ?_` and prove the remaining obligations. Establish `c` using `pullback.condition (f := pullback.fst p.left p.left ≫ p.left ≫ Y.hom) (g := thick V (IsLocalRing.maximalIdeal V) n)`.

Establish `c'` using `pullback.condition (f := p.left) (g := p.left)`. Use `set u := pullback.fst (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) (thick V (IsLocalRing.maximalIdeal V) n)`. Use `set v := pullback.snd (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) (thick V (IsLocalRing.maximalIdeal V) n)`. Establish `e : pullback.lift (f` using `Γ₁.hom) (u ≫ pullback.fst _ _) v (by rw [← c, ← hw, Category.assoc]) = pullback.lift (f := Γ₁.hom) (u ≫ pullback.snd _ _) v (by rw [← c, ← hw, Category.assoc, ← reassoc_of% c']) := by haveI := hq n`. Rewrite using `[← cancel_mono (q n)]`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, q1, pullback.lift_fst_assoc, c']`. Simplify using `only [Category.assoc, q2, pullback.lift_snd]`. Establish `e'` using `congrArg (· ≫ pullback.fst _ _) e`. Simplify using `only [pullback.lift_fst] at e'`.

Use `⟨u ≫ pullback.fst _ _, ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[e']`. Establish `hm : Mono p.left` using `(pullback.isIso_diagonal_iff p.left).1 hd`.

Establish `hc : IsClosedImmersion p.left` using `(IsClosedImmersion.iff_isProper_and_mono p.left).2 ⟨‹_›, hm⟩`. Establish `hi : IsIso p.left`. Use `isIso_of_isClosedImmersion Y.hom _ fun n ↦ ?_` and prove the remaining obligations. Use `haveI := hq n`. Conclude with `⟨inv (q n) ≫ pullback.fst _ _, by rw [Category.assoc, ← q1, IsIso.inv_hom_id_assoc]⟩`.

Establish `: IsIso ((Over.forget _).map p)` using `hi`. Conclude with `isIso_of_reflects_iso p (Over.forget _)`.
-/
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Γ₁ Y : Over (Spec (CommRingCat.of V))) (p : Γ₁ ⟶ Y) [IsProper Y.hom] [IsProper p.left], (∀ e, IsIso ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)) → IsIso p := by
  intro V _ _ _ _ Γ₁ Y p _ _ h
  have hw : p.left ≫ Y.hom = Γ₁.hom := Over.w p
  let q (e : ℕ) : pullback Γ₁.hom (thick V (IsLocalRing.maximalIdeal V) e) ⟶
      pullback Y.hom (thick V (IsLocalRing.maximalIdeal V) e) :=
    ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p).left
  have hq (e : ℕ) : IsIso (q e) := by
    haveI := h e
    exact inferInstanceAs (IsIso ((Over.forget _).map
      ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)))
  have q1 (e : ℕ) : q e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p.left := pullback.lift_fst _ _ _
  have q2 (e : ℕ) : q e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hd : IsIso (pullback.diagonal p.left) := by
    refine isIso_of_isClosedImmersion (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) _ fun n ↦ ?_
    have c := pullback.condition (f := pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (g := thick V (IsLocalRing.maximalIdeal V) n)
    have c' := pullback.condition (f := p.left) (g := p.left)
    set u := pullback.fst (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    set v := pullback.snd (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    have e : pullback.lift (f := Γ₁.hom) (u ≫ pullback.fst _ _) v
          (by rw [← c, ← hw, Category.assoc]) =
        pullback.lift (f := Γ₁.hom) (u ≫ pullback.snd _ _) v
          (by rw [← c, ← hw, Category.assoc, ← reassoc_of% c']) := by
      haveI := hq n
      rw [← cancel_mono (q n)]
      apply pullback.hom_ext
      · simp only [Category.assoc, q1, pullback.lift_fst_assoc, c']
      · simp only [Category.assoc, q2, pullback.lift_snd]
    have e' := congrArg (· ≫ pullback.fst _ _) e
    simp only [pullback.lift_fst] at e'
    refine ⟨u ≫ pullback.fst _ _, ?_⟩
    apply pullback.hom_ext
    · simp
    · simp [e']
  have hm : Mono p.left := (pullback.isIso_diagonal_iff p.left).1 hd
  have hc : IsClosedImmersion p.left :=
    (IsClosedImmersion.iff_isProper_and_mono p.left).2 ⟨‹_›, hm⟩
  have hi : IsIso p.left := by
    refine isIso_of_isClosedImmersion Y.hom _ fun n ↦ ?_
    haveI := hq n
    exact ⟨inv (q n) ≫ pullback.fst _ _, by rw [Category.assoc, ← q1, IsIso.inv_hom_id_assoc]⟩
  have : IsIso ((Over.forget _).map p) := hi
  exact isIso_of_reflects_iso p (Over.forget _)

end GlobalTheory.IsoLimit
