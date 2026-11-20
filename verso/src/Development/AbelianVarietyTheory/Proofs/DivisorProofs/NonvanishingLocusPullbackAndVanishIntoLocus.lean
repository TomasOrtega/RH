import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocusPull

/- English proof (translation)
Establish `hu : ∀ j, IsUnit (s.f j)` using `fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by`. Establish `hy' : y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s` using `h ▸ trivial`. Conclude with `(Y.mem_basicOpen _ y hy).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen s hy).1 hy')`. Conclude with `⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩`.
-/
theorem exists_gen_of_nonzeroLocus_eq_top {Y : Scheme.{0}} {M : LB Y} (s : M.Sec) (h : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤) :
    ∃ t : LB.Gen M, t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have hy' : y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := h ▸ trivial
      exact (Y.mem_basicOpen _ y hy).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen s hy).1 hy')
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

/- English proof (translation)
Take `⟨L, hL, s, rfl, rfl⟩` from `h`. Conclude with `⟨_, pull_isLB hL f, GlobalTheory.secPull s f, rfl, GlobalTheory.nonzeroLocus_secPull s f⟩`.
-/
theorem isLocus_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V) :
    IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V) := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  exact ⟨_, pull_isLB hL f, GlobalTheory.secPull s f, rfl, GlobalTheory.nonzeroLocus_secPull s f⟩

/- English proof (translation)
Take `⟨L, hL, s, rfl, rfl⟩` from `h`. Establish `htop : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s f) = ⊤`. Rewrite using `[GlobalTheory.nonzeroLocus_secPull]`. Conclude with `top_unique fun y _ => hf y`. Conclude with `(cls_eq_zero_iff (pull_isLB hL f)).2 (exists_gen_of_nonzeroLocus_eq_top _ htop)`.
-/
theorem pull_eq_zero_of_isLocus {X Y : Scheme.{0}} (f : Y ⟶ X) {c : Pic X} {V : X.Opens} (h : IsLocus c V)
    (hf : ∀ y, f y ∈ V) : GlobalTheory.CechPic.pull f c = 0 := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  have htop : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s f) = ⊤ := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact top_unique fun y _ => hf y
  exact (cls_eq_zero_iff (pull_isLB hL f)).2 (exists_gen_of_nonzeroLocus_eq_top _ htop)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ f _ _ h => isLocus_pull f h, fun _ _ f _ _ h hf => pull_eq_zero_of_isLocus f h hf⟩`.
-/
theorem locus_pull :
    (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → IsLocus (GlobalTheory.CechPic.pull f c) (f ⁻¹ᵁ V)) ∧ (∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (c : Pic X) (V : X.Opens), IsLocus c V → (∀ y, f y ∈ V) → GlobalTheory.CechPic.pull f c = 0) :=
  ⟨fun _ _ f _ _ h => isLocus_pull f h, fun _ _ f _ _ h hf => pull_eq_zero_of_isLocus f h hf⟩

end GlobalTheory.LocusPull
