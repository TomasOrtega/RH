import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiProjectiveProperCoverStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropernessDescendsFgSubalgebraStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCoverStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

noncomputable def baseMap {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    pullback (π ≫ p) f ⟶ pullback p f :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by simp [pullback.condition])

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem baseMap_snd {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    baseMap π p f ≫ pullback.snd p f = pullback.snd (π ≫ p) f :=
  pullback.lift_snd _ _ _

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := pullback.snd p f) (h₂₂ := p) (v₁₃ := f) ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback p f).flip` and prove the remaining obligations. Rewrite using `[baseMap_snd]`. Conclude with `(IsPullback.of_hasPullback (π ≫ p) f).flip`.
-/
theorem baseMap_isPullback {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    IsPullback (baseMap π p f) (pullback.fst (π ≫ p) f) (pullback.fst p f) π := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p f) (h₂₂ := p) (v₁₃ := f) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p f).flip
  rw [baseMap_snd]
  exact (IsPullback.of_hasPullback (π ≫ p) f).flip

/- English proof (translation)
Establish `: IsProper (baseMap π p f)` using `MorphismProperty.of_isPullback (P := @IsProper) (baseMap_isPullback π p f).flip inferInstance`. Rewrite using `[← baseMap_snd π p f]`. Use `infer_instance`.
-/
theorem isProper_snd_comp {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S)
    [IsProper π] [IsProper (pullback.snd p f)] : IsProper (pullback.snd (π ≫ p) f) := by
  have : IsProper (baseMap π p f) :=
    MorphismProperty.of_isPullback (P := @IsProper) (baseMap_isPullback π p f).flip inferInstance
  rw [← baseMap_snd π p f]
  infer_instance

/- English proof (translation)
Set `g : pullback q (h ≫ f) ⟶ pullback q f` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ h) (by simp [pullback.condition])`. Establish `hg : g ≫ pullback.fst q f = pullback.fst q (h ≫ f)` using `pullback.lift_fst _ _ _`. Establish `hsq : IsPullback g (pullback.snd q (h ≫ f)) (pullback.snd q f) h`. Use `IsPullback.of_right (h₁₂ := pullback.fst q f) (h₂₂ := f) (v₁₃ := q) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q f)` and prove the remaining obligations. Rewrite using `[hg]`.

Conclude with `IsPullback.of_hasPullback q (h ≫ f)`. Conclude with `MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance`.
-/
theorem isProper_snd_of_comp {X S T T' : Scheme.{0}} (q : X ⟶ S) (f : T ⟶ S) (h : T' ⟶ T)
    [IsProper (pullback.snd q f)] : IsProper (pullback.snd q (h ≫ f)) := by
  let g : pullback q (h ≫ f) ⟶ pullback q f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ h) (by simp [pullback.condition])
  have hg : g ≫ pullback.fst q f = pullback.fst q (h ≫ f) :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback g (pullback.snd q (h ≫ f)) (pullback.snd q f) h := by
    refine IsPullback.of_right (h₁₂ := pullback.fst q f) (h₂₂ := f) (v₁₃ := q) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback q f)
    rw [hg]
    exact IsPullback.of_hasPullback q (h ≫ f)
  exact MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance

/- English proof (translation)
Take `⟨y, hy⟩` from `h`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.fst p f) (g := π) x y hy.symm`. Establish `hpb` using `baseMap_isPullback π p f`. Use `⟨hpb.isoPullback.inv z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz]`.
-/
theorem mem_range_baseMap {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S)
    (x : ↥(pullback p f)) (h : pullback.fst p f x ∈ Set.range π) :
    x ∈ Set.range (baseMap π p f) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst p f) (g := π) x y hy.symm
  have hpb := baseMap_isPullback π p f
  refine ⟨hpb.isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz]

/- English proof (translation)
Take `⟨n, Y, π, hπ, hcov⟩` from `GlobalTheory.T.quasi_projective_proper_cover k X p hs hl hq`. Establish `hi : ∀ i, ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R)))`. Introduce `i`. Use `(hπ i).1` as an intermediate fact. Conclude with `GlobalTheory.T.properness_descends_fg_subalgebra k V (Y i) (π i ≫ p) (hπ i).2 (isProper_snd_comp (π i) p _)`.

Use `choose Ri hRfg hRp using hi`. Set `R : Subalgebra k V` to `Finset.univ.sup Ri`. Establish `hFG : R.FG` using `Finset.sup_induction (p := Subalgebra.FG) Subalgebra.fg_bot (fun _ h _ h' => h.sup h') (fun i _ => hRfg i)`. Use `⟨R, hFG, ?_⟩` and prove the remaining obligations. Establish `hle : ∀ i, Ri i ≤ R` using `fun i => Finset.le_sup (Finset.mem_univ i)`.

Establish `hmap : ∀ i, spMap (algebraMap k R) = spMap (Subalgebra.inclusion (hle i)).toRingHom ≫ spMap (algebraMap k (Ri i))`. Introduce `i`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Establish `hprop : ∀ i, IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R)))`.

Introduce `i`. Use `hRp i` as an intermediate fact. Rewrite using `[hmap i]`. Conclude with `isProper_snd_of_comp _ _ _`. Use `GlobalTheory.T.proper_of_proper_cover (pullback p (spMap (algebraMap k R))) (Sp R) (pullback.snd p (spMap (algebraMap k R))) n (fun i => pullback (π i ≫ p) (spMap (algebraMap k R))) (fun i => baseMap (π i) p (spMap (algebraMap k R))) inferInstance inferInstance ?_ ?_` and prove the remaining obligations.

Introduce `i`. Rewrite using `[baseMap_snd]`. Conclude with `hprop i`. Introduce `x`. Take `⟨i, hi⟩` from `hcov (pullback.fst p (spMap (algebraMap k R)) x)`.

Conclude with `⟨i, mem_range_baseMap _ _ _ x hi⟩`.
-/
theorem isProper_descends (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V]
    (X : Scheme.{0}) (p : X ⟶ Sp k) (hs : IsSeparated p) (hl : LocallyOfFiniteType p)
    (hq : QuasiCompact p) (hP : IsProper (pullback.snd p (spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  obtain ⟨n, Y, π, hπ, hcov⟩ := GlobalTheory.T.quasi_projective_proper_cover k X p hs hl hq
  have hi : ∀ i, ∃ R : Subalgebra k V, R.FG ∧
      IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R))) := by
    intro i
    have := (hπ i).1
    exact GlobalTheory.T.properness_descends_fg_subalgebra k V (Y i) (π i ≫ p) (hπ i).2 (isProper_snd_comp (π i) p _)
  choose Ri hRfg hRp using hi
  let R : Subalgebra k V := Finset.univ.sup Ri
  have hFG : R.FG :=
    Finset.sup_induction (p := Subalgebra.FG) Subalgebra.fg_bot (fun _ h _ h' => h.sup h')
      (fun i _ => hRfg i)
  refine ⟨R, hFG, ?_⟩
  have hle : ∀ i, Ri i ≤ R := fun i => Finset.le_sup (Finset.mem_univ i)
  have hmap : ∀ i, spMap (algebraMap k R) =
      spMap (Subalgebra.inclusion (hle i)).toRingHom ≫ spMap (algebraMap k (Ri i)) := by
    intro i
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hprop : ∀ i, IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R))) := by
    intro i
    have := hRp i
    rw [hmap i]
    exact isProper_snd_of_comp _ _ _
  refine GlobalTheory.T.proper_of_proper_cover (pullback p (spMap (algebraMap k R))) (Sp R)
    (pullback.snd p (spMap (algebraMap k R))) n
    (fun i => pullback (π i ≫ p) (spMap (algebraMap k R)))
    (fun i => baseMap (π i) p (spMap (algebraMap k R))) inferInstance inferInstance ?_ ?_
  · intro i
    rw [baseMap_snd]
    exact hprop i
  · intro x
    obtain ⟨i, hi⟩ := hcov (pullback.fst p (spMap (algebraMap k R)) x)
    exact ⟨i, mem_range_baseMap _ _ _ x hi⟩

end GlobalTheory.CompanionTheory.Ar.Approx
