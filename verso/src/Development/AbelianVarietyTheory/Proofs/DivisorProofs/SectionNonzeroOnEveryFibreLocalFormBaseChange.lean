import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals

/- English proof (translation)
Introduce `S G _ _ L δ σ i R _ ξ t hξ ht hσ r`. Establish `hP` using `isGrpPullback_pullback G ξ`. Take `⟨z, hz, hz'⟩` from `hσ (ξ r)`. Take `⟨y, rfl, hy⟩` from `Scheme.exists_preimage_of_isPullback hP.1 z r hz`. Take `⟨k, hb⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz'`.

Establish `hk : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k` using `G.left.basicOpen_le _ hb`. Establish `hle : (bL L ξ).L.U (fun _ => k.1) ≤ pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i)`. Introduce `x hx`. Use `⟨mem_pull.1 hx, mem_pull.2 ?_⟩` and prove the remaining obligations. Establish `e : G.hom (pullback.fst G.hom ξ x) = ξ (pullback.snd G.hom ξ x)`.

Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`. Use `show G.hom (pullback.fst G.hom ξ x) ∈ δ.U i`. Rewrite using `[e]`. Conclude with `hξ (Set.mem_univ _)`. Establish `hy1 : y ∈ (bL L ξ).L.U (fun _ => k.1)` using `mem_pull.2 hk.1`.

Establish `hy2` using `hle hy1`. Establish `hb' : pullback.fst G.hom ξ y ∈ G.left.basicOpen (σ.f (k.1, fun _ => i))`. Establish `hm : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k ⊓ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i)` using `⟨hk, hy2⟩`. Establish `e` using `congrArg G.left.basicOpen (σ.compat k (k.1, fun _ => i))`. Rewrite `e` using `[Scheme.basicOpen_mul]`.

Establish `e1` using `G.left.basicOpen_res (σ.f k) (homOfLE (inf_le_left : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op`. Establish `e2` using `G.left.basicOpen_res (σ.f (k.1, fun _ => i)) (homOfLE (inf_le_right : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op`. Establish `h1` using `e1.ge ⟨hm, hb⟩`. Establish `h2` using `(e.le h1).2`. Conclude with `(e2.le h2).2`.

Use `⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k.1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[ht (fun _ => k.1) hle]`. Conclude with `(Scheme.basicOpen_appLE (pullback.fst G.hom ξ) _ _ hle _).ge ⟨hy1, hb'⟩`.
-/
theorem nzFib_of_isLocSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S) (t : (KeyVals.bL L ξ).L.Sec),
    ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → NzFib σ → NzFib t := by
  intro S G _ _ L δ σ i R _ ξ t hξ ht hσ r
  have hP := isGrpPullback_pullback G ξ
  obtain ⟨z, hz, hz'⟩ := hσ (ξ r)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback hP.1 z r hz
  obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hk : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k := G.left.basicOpen_le _ hb
  have hle : (bL L ξ).L.U (fun _ => k.1) ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := by
    intro x hx
    refine ⟨mem_pull.1 hx, mem_pull.2 ?_⟩
    have e : G.hom (pullback.fst G.hom ξ x) = ξ (pullback.snd G.hom ξ x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    show G.hom (pullback.fst G.hom ξ x) ∈ δ.U i
    rw [e]
    exact hξ (Set.mem_univ _)
  have hy1 : y ∈ (bL L ξ).L.U (fun _ => k.1) := mem_pull.2 hk.1
  have hy2 := hle hy1
  have hb' : pullback.fst G.hom ξ y ∈ G.left.basicOpen (σ.f (k.1, fun _ => i)) := by
    have hm : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := ⟨hk, hy2⟩
    have e := congrArg G.left.basicOpen (σ.compat k (k.1, fun _ => i))
    rw [Scheme.basicOpen_mul] at e
    have e1 := G.left.basicOpen_res (σ.f k) (homOfLE (inf_le_left : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have e2 := G.left.basicOpen_res (σ.f (k.1, fun _ => i)) (homOfLE (inf_le_right : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have h1 := e1.ge ⟨hm, hb⟩
    have h2 := (e.le h1).2
    exact (e2.le h2).2
  refine ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k.1, ?_⟩⟩
  rw [ht (fun _ => k.1) hle]
  exact (Scheme.basicOpen_appLE (pullback.fst G.hom ξ) _ _ hle _).ge ⟨hy1, hb'⟩

end GlobalTheory.KeyVals

end
