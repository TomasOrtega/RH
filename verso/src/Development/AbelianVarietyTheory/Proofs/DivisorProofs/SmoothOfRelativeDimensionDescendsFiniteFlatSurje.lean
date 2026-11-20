import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjRelDim

/- English proof (translation)
Set `y : Y` to `Classical.arbitrary Y`. Set `t` to `S.fromSpecResidueField (p y)`. Establish `hpb₂` using `IsPullback.of_hasPullback p t`. Establish `hpb₁` using `IsPullback.of_hasPullback f (pullback.fst p t)`. Establish `hpX : IsPullback (pullback.fst f (pullback.fst p t)) (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) (f ≫ p) t` using `hpb₁.paste_vert hpb₂`.

Establish `hgK : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t)` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpX hX`. Establish `hmK : SmoothOfRelativeDimension m (pullback.snd p t)` using `(smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback hpb₂ hY`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : p y ∈ Set.range t := by`. Rewrite using `[Scheme.range_fromSpecResidueField]`. Both sides reduce to the same expression.

Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback y w hw.symm`. Take `⟨a, -⟩` from `(pullback.snd f (pullback.fst p t)).surjective z`. Establish `: Nonempty ↥(pullback f (pullback.fst p t))` using `⟨a⟩`. Conclude with `GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := (p y |> S.residueField)) (pullback.snd f (pullback.fst p t)) (pullback.snd p t) hgK hmK`.
-/
theorem eq_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f] (p : Y ⟶ S)
    [Nonempty Y] {g m : ℕ} (hX : SmoothOfRelativeDimension g (f ≫ p)) (hY : SmoothOfRelativeDimension m p) :
    g = m := by
  let y : Y := Classical.arbitrary Y
  let t := S.fromSpecResidueField (p y)
  have hpb₂ := IsPullback.of_hasPullback p t
  have hpb₁ := IsPullback.of_hasPullback f (pullback.fst p t)
  have hpX : IsPullback (pullback.fst f (pullback.fst p t))
      (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) (f ≫ p) t := hpb₁.paste_vert hpb₂
  have hgK : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst p t) ≫ pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpX hX
  have hmK : SmoothOfRelativeDimension m (pullback.snd p t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback hpb₂ hY
  obtain ⟨w, hw⟩ : p y ∈ Set.range t := by
    rw [Scheme.range_fromSpecResidueField]; rfl
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y w hw.symm
  obtain ⟨a, -⟩ := (pullback.snd f (pullback.fst p t)).surjective z
  have : Nonempty ↥(pullback f (pullback.fst p t)) := ⟨a⟩
  exact GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := (p y |> S.residueField))
    (pullback.snd f (pullback.fst p t)) (pullback.snd p t) hgK hmK

/- English proof (translation)
Introduce `S A B g q hg hB hfin _ hsurj`. Use `choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim B.hom`. Establish `hn : ∀ y, n y = g` using `fun y => by`. Establish `: Nonempty (W y)` using `⟨⟨y, hW y⟩⟩`. Establish `hd'` using `hd y`.

Establish `: Surjective (q.left ∣_ W y)` using `IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _`. Establish `hX : SmoothOfRelativeDimension g ((q.left ∣_ W y) ≫ (W y).ι ≫ B.hom)`. Rewrite using `[← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q]`. Establish `: SmoothOfRelativeDimension (0 + g) ((q.left ⁻¹ᵁ W y).ι ≫ A.hom)` using `inferInstance`. Simplify using `using this`.

Conclude with `(eq_of_finite_surjective (q.left ∣_ W y) ((W y).ι ≫ B.hom) hX hd').symm`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension g)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_` and prove the remaining obligations. Rewrite using `[← hn x]`. Conclude with `hd x`.
-/
theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (S : Scheme.{0}) (A B : Over S) (g : ℕ) (q : A ⟶ B),
    SmoothOfRelativeDimension g A.hom → Smooth B.hom → IsFinite q.left → Flat q.left → Surjective q.left →
    SmoothOfRelativeDimension g B.hom := by
  intro S A B g q hg hB hfin _ hsurj
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim B.hom
  have hn : ∀ y, n y = g := fun y => by
    have : Nonempty (W y) := ⟨⟨y, hW y⟩⟩
    have hd' := hd y
    have : Surjective (q.left ∣_ W y) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
    have hX : SmoothOfRelativeDimension g ((q.left ∣_ W y) ≫ (W y).ι ≫ B.hom) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q]
      have : SmoothOfRelativeDimension (0 + g) ((q.left ⁻¹ᵁ W y).ι ≫ A.hom) := inferInstance
      simpa using this
    exact (eq_of_finite_surjective (q.left ∣_ W y) ((W y).ι ≫ B.hom) hX hd').symm
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FiniteSurjRelDim
