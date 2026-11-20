import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem eighthPower_inj_exists : ∀ {S : Scheme.{0}} (P C : Over S) [GrpObj P] [IsCommMonObj P] [GrpObj C] (pr : Fin 8 → (P ⟶ C)) (hpr : ∀ a, IsMonHom (pr a)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ P, ∀ a, x ≫ pr a = y a), ∃ inj : Fin 8 → (C ⟶ P), (∀ a, IsMonHom (inj a)) ∧ (∀ a b, inj a ≫ pr b = if a = b then 𝟙 C else 1) ∧ ∏ a, (pr a ≫ inj a) = 𝟙 P := by
  intro S P C _ _ _ pr hpr huniv
  have hext : ∀ {T : Over S} (f g : T ⟶ P), (∀ b, f ≫ pr b = g ≫ pr b) → f = g :=
    fun f g h => (huniv _ (fun b => g ≫ pr b)).unique h (fun _ => rfl)
  choose inj hinj using fun a => (huniv C (fun b => if a = b then 𝟙 C else 1)).exists
  have hmon : ∀ a, IsMonHom (inj a) := by
    intro a
    constructor
    · apply hext
      intro b
      haveI := hpr b
      rw [Category.assoc, hinj a b, IsMonHom.one_hom (pr b)]
      split_ifs
      · simp
      · rw [MonObj.comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    · apply hext
      intro b
      haveI := hpr b
      simp only [Category.assoc]
      rw [hinj a b, IsMonHom.mul_hom (pr b), tensorHom_comp_tensorHom_assoc, hinj a b]
      split_ifs
      · simp
      · rw [MonObj.comp_one, ← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_one, MonObj.comp_one, _root_.one_mul]
  refine ⟨inj, hmon, hinj, ?_⟩
  apply hext
  intro b
  haveI := hpr b
  rw [Fin.prod_univ_eight]
  simp only [MonObj.mul_comp, Category.assoc, hinj, MonObj.comp_one, Category.id_comp, Category.comp_id]
  fin_cases b <;> simp

end GlobalTheory
