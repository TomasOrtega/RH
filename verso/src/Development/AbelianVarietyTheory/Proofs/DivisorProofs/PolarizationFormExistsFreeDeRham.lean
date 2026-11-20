import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihila
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPolForm

/- English proof (translation)
Take `⟨h0, -, -, -, e, he⟩` from `P R A _ hA gA`. Take `⟨z, hz, -⟩` from `(isChern_existsUnique_and_iso R ⊥ (dp0 R) _ (A.hom ≫ 𝟙 _)).1 _ hLB`. Take `⟨n, a, b, hab⟩` from `PolExists.exists_sum_wedge (e.symm z)`. Establish `hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A` using `fun c ↦ by`. Express the relevant statement in the definitionally equal form `c ∈ prim (dp0 R) (𝟙 _) A`.

Rewrite using `[show prim (dp0 R) (𝟙 _) A = ⊤ from h0]`. Discharge the goal by the elementary cases of `trivial`. Set `a' : Fin n → primDR A` to `fun k ↦ ⟨a k, hm _⟩`. Set `b' : Fin n → primDR A` to `fun k ↦ ⟨b k, hm _⟩`. Establish `hz' : IsChern (dp0 R) (A.hom ≫ 𝟙 _) L (∑ k, CatCoh.cup _ (a' k).1 (b' k).1)`.

Establish `: z = ∑ k, CatCoh.cup _ (a k) (b k)`. Rewrite using `[← e.apply_symm_apply z, ← hab, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ ↦ he _ _`. Conclude with `this ▸ hz`. Conclude with `⟨_, n, a', b', hz', rfl⟩`.
-/
theorem exists_of_isLB (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (gA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (hLB : L.IsLB) :
    ∃ ψ : LinearMap.BilinForm R (HdR A), IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨h0, -, -, -, e, he⟩ := P R A _ hA gA
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso R ⊥ (dp0 R) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 R) (𝟙 _) A
    rw [show prim (dp0 R) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 R) (A.hom ≫ 𝟙 _) L (∑ k, CatCoh.cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, CatCoh.cup _ (a k) (b k) := by
      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  exact ⟨_, n, a', b', hz', rfl⟩

/- English proof (translation)
Introduce `P F _ _ 𝔠 R _ X c`. Conclude with `exists_of_isLB P X.A X.ab X.dim _ (pull_isLB (X.isLB c) _)`.
-/
theorem diag_polForm_exists : GlobalTheory.Published.AbelianDeRham.Free → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ := by
  intro P F _ _ 𝔠 R _ X c
  exact exists_of_isLB P X.A X.ab X.dim _ (pull_isLB (X.isLB c) _)

end GlobalTheory.DiagPolForm
