import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ S _ A B _ _ _ _ ψ a hA hB hψ hf he hs hker`. Establish `hsep : IsSeparated B.hom`. Use `hB.proper` as an intermediate fact. Use `infer_instance`. Establish `key : ∀ c : O, ∃ g' : B ⟶ B, IsMonHom g' ∧ ψ ≫ g' = a.act c ≫ ψ ∧ ∀ g'' : B ⟶ B, ψ ≫ g'' = a.act c ≫ ψ → g'' = g'`.

Introduce `c`. Use `a.hom c` as an intermediate fact. Use `GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S A B B ψ (a.act c ≫ ψ) hA hB hsep hψ hf he hs inferInstance ?_` and prove the remaining obligations. Introduce `k _ _ t x hx`. Rewrite using `[← Category.assoc]`.

Conclude with `hker k t x c hx`. Use `choose f hf1 hf2 hf3 using key`. Use `⟨⟨f, hf1, ?_, ?_, ?_⟩, fun c => (hf2 c).symm⟩` and prove the remaining obligations. Use `(hf3 1 _ ?_).symm` and prove the remaining obligations. Rewrite using `[a.one, Category.id_comp, Category.comp_id]`.

Introduce `x y`. Use `(hf3 _ _ ?_).symm` and prove the remaining obligations. Rewrite using `[← Category.assoc, hf2, Category.assoc, hf2, a.mul, Category.assoc]`. Introduce `x y`. Use `(hf3 _ _ ?_).symm` and prove the remaining obligations.

Rewrite using `[MonObj.comp_mul, hf2, hf2, a.add]`. Conclude with `(map_mul (IsMonHom.monoidHom ψ A) _ _).symm`.
-/
theorem exists_oAct_descend_of_etale_isogeny :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (a : OAct O A), IsAbelianScheme A → IsAbelianScheme B → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A) (c : O), x ≫ ψ = 1 → (x ≫ a.act c) ≫ ψ = 1) → ∃ b : OAct O B, ∀ c, a.act c ≫ ψ = ψ ≫ b.act c := by
  intro O _ S _ A B _ _ _ _ ψ a hA hB hψ hf he hs hker
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have key : ∀ c : O, ∃ g' : B ⟶ B, IsMonHom g' ∧ ψ ≫ g' = a.act c ≫ ψ ∧
      ∀ g'' : B ⟶ B, ψ ≫ g'' = a.act c ≫ ψ → g'' = g' := by
    intro c
    have := a.hom c
    refine GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S A B B ψ (a.act c ≫ ψ) hA hB hsep hψ hf he hs inferInstance ?_
    intro k _ _ t x hx
    rw [← Category.assoc]
    exact hker k t x c hx
  choose f hf1 hf2 hf3 using key
  refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, fun c => (hf2 c).symm⟩
  · refine (hf3 1 _ ?_).symm
    rw [a.one, Category.id_comp, Category.comp_id]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [← Category.assoc, hf2, Category.assoc, hf2, a.mul, Category.assoc]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [MonObj.comp_mul, hf2, hf2, a.add]
    exact (map_mul (IsMonHom.monoidHom ψ A) _ _).symm

end GlobalTheory
