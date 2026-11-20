import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

variable {X Y Z : Scheme.{0}}

/- English proof (translation)
Introduce `_ hy` and use `mem_pull.2 (mem_pull.1 hy).1`.
-/
theorem tensGen_le₁ (A B : LB X) (f : Y ⟶ X) (j : PUnit → A.ι × B.ι) :
    ((GlobalTheory.CechPic.tens A B).pull f).U j ≤ (A.pull f).U (fun _ => (j PUnit.unit).1) :=
  fun _ hy => mem_pull.2 (mem_pull.1 hy).1

/- English proof (translation)
Introduce `_ hy` and use `mem_pull.2 (mem_pull.1 hy).2`.
-/
theorem tensGen_le₂ (A B : LB X) (f : Y ⟶ X) (j : PUnit → A.ι × B.ι) :
    ((GlobalTheory.CechPic.tens A B).pull f).U j ≤ (B.pull f).U (fun _ => (j PUnit.unit).2) :=
  fun _ hy => mem_pull.2 (mem_pull.1 hy).2

def tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) :
    LB.Gen ((GlobalTheory.CechPic.tens A B).pull f) where
  s j := res (tensGen_le₁ A B f j) (a.s _) * res (tensGen_le₂ A B f j) (b.s _)

/- English proof (translation)
The claim follows from `(map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hj _) (gm_res r z _ hj _))`.
-/
theorem gm_tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) (r : Z ⟶ Y) (z : Z)
    (j : PUnit → A.ι × B.ι) (hj : r z ∈ ((GlobalTheory.CechPic.tens A B).pull f).U j) :
    gm r z _ ((tensGen A B f a b).s j) =
      gm r z ((A.pull f).U (fun _ => (j PUnit.unit).1)) (a.s _) *
      gm r z ((B.pull f).U (fun _ => (j PUnit.unit).2)) (b.s _) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hj _) (gm_res r z _ hj _))

/- English proof (translation)
Use `(GlobalTheory.CechPic.isGen_iff_germ _).2 fun y i j hi hj => ?_` and prove the remaining obligations. Establish `hi'` using `mem_pull.1 hi`. Establish `hj'` using `mem_pull.1 hj`. Establish `ai : y ∈ (A.pull f).U (fun _ => (i PUnit.unit).1)` using `mem_pull.2 hi'.1`. Establish `aj : y ∈ (A.pull f).U (fun _ => (j PUnit.unit).1)` using `mem_pull.2 hj'.1`.

Establish `bi : y ∈ (B.pull f).U (fun _ => (i PUnit.unit).2)` using `mem_pull.2 hi'.2`. Establish `bj : y ∈ (B.pull f).U (fun _ => (j PUnit.unit).2)` using `mem_pull.2 hj'.2`. Rewrite using `[gm_tensGen A B f a b (𝟙 Y) y i hi, gm_tensGen A B f a b (𝟙 Y) y j hj, gm_pull_g (GlobalTheory.CechPic.tens A B) f (𝟙 Y) y i j hi hj, GlobalTheory.CechPic.gm_tens A B (𝟙 Y ≫ f) y _ _ hi' hj', (GlobalTheory.CechPic.isGen_iff_germ a).1 ha y _ _ ai aj, (GlobalTheory.CechPic.isGen_if …`. Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem tensGen_isGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f))
    (ha : a.IsGen) (hb : b.IsGen) : (tensGen A B f a b).IsGen := by
  refine (GlobalTheory.CechPic.isGen_iff_germ _).2 fun y i j hi hj => ?_
  have hi' := mem_pull.1 hi
  have hj' := mem_pull.1 hj
  have ai : y ∈ (A.pull f).U (fun _ => (i PUnit.unit).1) := mem_pull.2 hi'.1
  have aj : y ∈ (A.pull f).U (fun _ => (j PUnit.unit).1) := mem_pull.2 hj'.1
  have bi : y ∈ (B.pull f).U (fun _ => (i PUnit.unit).2) := mem_pull.2 hi'.2
  have bj : y ∈ (B.pull f).U (fun _ => (j PUnit.unit).2) := mem_pull.2 hj'.2
  rw [gm_tensGen A B f a b (𝟙 Y) y i hi, gm_tensGen A B f a b (𝟙 Y) y j hj,
    gm_pull_g (GlobalTheory.CechPic.tens A B) f (𝟙 Y) y i j hi hj, GlobalTheory.CechPic.gm_tens A B (𝟙 Y ≫ f) y _ _ hi' hj',
    (GlobalTheory.CechPic.isGen_iff_germ a).1 ha y _ _ ai aj,
    (GlobalTheory.CechPic.isGen_iff_germ b).1 hb y _ _ bi bj,
    gm_pull_g A f (𝟙 Y) y _ _ ai aj, gm_pull_g B f (𝟙 Y) y _ _ bi bj]
  exact mul_mul_mul_comm _ _ _ _

/- English proof (translation)
The claim follows from `gm_tensGen A B f a b r z _ (hJ.mem _ r)`.
-/
theorem val_tensGen (A B : LB X) (f : Y ⟶ X) (a : LB.Gen (A.pull f)) (b : LB.Gen (B.pull f)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → A.ι × B.ι) (hJ : Good (GlobalTheory.CechPic.tens A B) z J) :
    val (L := GlobalTheory.CechPic.tens A B) (φ := fun _ : PUnit => f) (ε := fun _ => 1) (tensGen A B f a b) r z J =
      val (L := A) (φ := fun _ : PUnit => f) (ε := fun _ => 1) a r z (fun ψ => (J ψ).1) *
      val (L := B) (φ := fun _ : PUnit => f) (ε := fun _ => 1) b r z (fun ψ => (J ψ).2) :=
  gm_tensGen A B f a b r z _ (hJ.mem _ r)

/- English proof (translation)
Introduce `X A B R _ _ x eA eB hA hB hxA hxB`. Use `⟨tensGen A B x eA eB, tensGen_isGen A B x eA eB hA hB, ?_⟩` and prove the remaining obligations. Introduce `V _ _ _ hV ψ gam hg χ hχ`. Take `⟨a', ha', hva⟩` from `hxA V hV ψ gam hg χ hχ`. Take `⟨b', hb', hvb⟩` from `hxB V hV ψ gam hg χ hχ`.

Use `⟨tensGen A B χ a' b', tensGen_isGen A B χ a' b' ha' hb', fun z J hJ => ?_⟩` and prove the remaining obligations. Establish `hJA : Good A z (fun ψ => (J ψ).1)` using `fun ψ => (hJ ψ).1`. Establish `hJB : Good B z (fun ψ => (J ψ).2)` using `fun ψ => (hJ ψ).2`. Rewrite using `[val_tensGen A B x eA eB _ z J hJ, val_tensGen A B χ a' b' _ z J hJ, hva z _ hJA, hvb z _ hJB]`.
-/
theorem exists_tens_extAt : ∀ (X : Scheme.{0}) (A B : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (eA : LB.Gen (A.pull x)) (eB : LB.Gen (B.pull x)), eA.IsGen → eB.IsGen →
    GlobalTheory.TraitGen.ExtAt A x eA → GlobalTheory.TraitGen.ExtAt B x eB →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.tens A B).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.tens A B) x e := by
  intro X A B R _ _ x eA eB hA hB hxA hxB
  refine ⟨tensGen A B x eA eB, tensGen_isGen A B x eA eB hA hB, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  obtain ⟨a', ha', hva⟩ := hxA V hV ψ gam hg χ hχ
  obtain ⟨b', hb', hvb⟩ := hxB V hV ψ gam hg χ hχ
  refine ⟨tensGen A B χ a' b', tensGen_isGen A B χ a' b' ha' hb', fun z J hJ => ?_⟩
  have hJA : Good A z (fun ψ => (J ψ).1) := fun ψ => (hJ ψ).1
  have hJB : Good B z (fun ψ => (J ψ).2) := fun ψ => (hJ ψ).2
  rw [val_tensGen A B x eA eB _ z J hJ, val_tensGen A B χ a' b' _ z J hJ, hva z _ hJA, hvb z _ hJB]

end GlobalTheory.TraitGen
