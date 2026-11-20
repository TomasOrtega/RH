import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

/- English proof (translation)
Introduce `S hS Z x z J J' hJ hJ'`. Establish `h0 : ∀ i ∉ (hs e).toFinset, Van I (s i) e` using `fun i hi => by`. Assume the negation of the conclusion as `h`. Conclude with `hi ((hs e).mem_toFinset.2 h)`. Establish `hx : x ≫ (U.gt e).pG.left = (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R I e)` using `(Category.assoc _ _ _).symm`.

Rewrite using `[hτ _ h0 Z x z J J' hJ hJ']`. Establish `hsum : ∀ δ, sval (F δ) (x ≫ (U.gt e).pG.left) z J = ∑ i ∈ (hs e).toFinset.filter (fun i => w i = δ), sval (s i) (x ≫ (U.gt e).pG.left) z J` using `fun δ => by`. Rewrite using `[hx]`. Use `hF e _ h0 δ Z (x ≫ (U.gt e).q.left) z J hJ` and compare the differences between its conclusion and the goal. Establish `hvan : ∀ δ ∉ S, sval (F δ) (x ≫ (U.gt e).pG.left) z J = 0` using `fun δ hδ => by`.

Rewrite using `[hx]`. Conclude with `hS δ hδ Z (x ≫ (U.gt e).q.left) z J hJ`. Establish `key : ∀ T : Finset D.toPre.X, (hs e).toFinset.image w ⊆ T → ∑ i ∈ (hs e).toFinset, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val = ∑ δ ∈ T, sval (F δ) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t δ) x z J).val` using `fun T hT => by`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := w) (t := T) (fun i hi => hT (Finset.mem_image_of_mem w hi))]`. Use `Finset.sum_congr rfl fun δ _ => ?_` and prove the remaining obligations.

Rewrite using `[hsum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Take `rfl` from `(Finset.mem_filter.1 hi).2`. Both sides reduce to the same expression. Rewrite using `[key _ (Finset.subset_union_left (s₂ := S))]`.

Use `(Finset.sum_subset Finset.subset_union_right fun δ _ hδ => ?_).symm` and prove the remaining obligations. Conclude with `(congrArg (· * _) (hvan δ hδ)).trans (zero_mul _)`.
-/
theorem texp_of_isSum {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β)
    (hs : Small I s) (hF : IsSum I s F) (hτ : TExp U τ s) : TExp U τ (w := id) F := by
  classical
  intro S hS Z x z J J' hJ hJ'
  have h0 : ∀ i ∉ (hs e).toFinset, Van I (s i) e := fun i hi => by
    by_contra h
    exact hi ((hs e).mem_toFinset.2 h)
  have hx : x ≫ (U.gt e).pG.left =
      (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R I e) := (Category.assoc _ _ _).symm
  rw [hτ _ h0 Z x z J J' hJ hJ']
  have hsum : ∀ δ, sval (F δ) (x ≫ (U.gt e).pG.left) z J =
      ∑ i ∈ (hs e).toFinset.filter (fun i => w i = δ), sval (s i) (x ≫ (U.gt e).pG.left) z J := fun δ => by
    rw [hx]
    convert hF e _ h0 δ Z (x ≫ (U.gt e).q.left) z J hJ
  have hvan : ∀ δ ∉ S, sval (F δ) (x ≫ (U.gt e).pG.left) z J = 0 := fun δ hδ => by
    rw [hx]
    exact hS δ hδ Z (x ≫ (U.gt e).q.left) z J hJ
  have key : ∀ T : Finset D.toPre.X, (hs e).toFinset.image w ⊆ T →
      ∑ i ∈ (hs e).toFinset, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val =
      ∑ δ ∈ T, sval (F δ) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t δ) x z J).val := fun T hT => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := T) (fun i hi => hT (Finset.mem_image_of_mem w hi))]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl
  rw [key _ (Finset.subset_union_left (s₂ := S))]
  refine (Finset.sum_subset Finset.subset_union_right fun δ _ hδ => ?_).symm
  exact (congrArg (· * _) (hvan δ hδ)).trans (zero_mul _)

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ U _ _ _ _ τ _ _ s F hs hF hτ` and use `texp_of_isSum U.toUnifPre τ s F hs hF hτ`.
-/
theorem texp_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U _ _ _ _ τ _ _ s F hs hF hτ => texp_of_isSum U.toUnifPre τ s F hs hF hτ

end GlobalTheory.TwFam
