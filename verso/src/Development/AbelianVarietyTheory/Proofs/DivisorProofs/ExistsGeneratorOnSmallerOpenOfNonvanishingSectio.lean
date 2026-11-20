import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GenRestrict

/- English proof (translation)
Introduce `Z L _ O O' hle u hu`. Establish `e : ∀ _k : PUnit, Z.homOfLE hle ≫ (fun _ : PUnit => O'.ι) _k = (fun _ : PUnit => O.ι) _k` using `fun _ => Scheme.homOfLE_ι Z hle`. Set `v : LB.Sec (L.pull O.ι)` to `PullbackSections.pullSecLC L _ _ _ (Z.homOfLE hle) e u`. Use `GlobalTheory.LocusPull.exists_gen_of_nonzeroLocus_eq_top v (top_unique fun z _ => ?_)` and prove the remaining obligations. Establish `heq : O'.ι (Z.homOfLE hle z) = O.ι z`.

Conclude with `congrArg (fun f : O.toScheme ⟶ Z => f z) (Scheme.homOfLE_ι Z hle)`. Establish `hz : O'.ι (Z.homOfLE hle z) ∈ O`. Rewrite using `[heq]`. Conclude with `(Scheme.Opens.ι_apply O z).symm ▸ z.2`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hu _ hz)`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩` and prove the remaining obligations. Use `show z ∈ O.toScheme.basicOpen ((Scheme.Hom.appLE (Z.homOfLE hle) _ _ _).hom (u.f k))`. Rewrite using `[Scheme.basicOpen_appLE]`. Use `⟨?_, hk⟩` and prove the remaining obligations. Establish `h1 : Z.homOfLE hle z ∈ (L.pull O'.ι).U k` using `Scheme.basicOpen_le _ _ hk`.

Use `mem_pull.2 ?_` and prove the remaining obligations. Rewrite using `[← heq]`. Conclude with `mem_pull.1 h1`.
-/
theorem exists_gen_restrict : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' →
    ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) →
    ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  intro Z L _ O O' hle u hu
  have e : ∀ _k : PUnit, Z.homOfLE hle ≫ (fun _ : PUnit => O'.ι) _k = (fun _ : PUnit => O.ι) _k :=
    fun _ => Scheme.homOfLE_ι Z hle
  let v : LB.Sec (L.pull O.ι) := PullbackSections.pullSecLC L _ _ _ (Z.homOfLE hle) e u
  refine GlobalTheory.LocusPull.exists_gen_of_nonzeroLocus_eq_top v (top_unique fun z _ => ?_)
  have heq : O'.ι (Z.homOfLE hle z) = O.ι z := by
    exact congrArg (fun f : O.toScheme ⟶ Z => f z) (Scheme.homOfLE_ι Z hle)
  have hz : O'.ι (Z.homOfLE hle z) ∈ O := by
    rw [heq]
    exact (Scheme.Opens.ι_apply O z).symm ▸ z.2
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu _ hz)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  show z ∈ O.toScheme.basicOpen ((Scheme.Hom.appLE (Z.homOfLE hle) _ _ _).hom (u.f k))
  rw [Scheme.basicOpen_appLE]
  refine ⟨?_, hk⟩
  have h1 : Z.homOfLE hle z ∈ (L.pull O'.ι).U k := Scheme.basicOpen_le _ _ hk
  refine mem_pull.2 ?_
  rw [← heq]
  exact mem_pull.1 h1

end GlobalTheory.GenRestrict
