import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsFreeResolutionShortExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyLongExactMapsNaturalOfRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveRepGroupHomologyPosVanishes
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

def conjActHom {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) :
    A ⟶ Rep.res (MulAut.conj g).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ g, fun h => LinearMap.ext fun a => by
    change A.ρ g (A.ρ h a) = A.ρ (g * h * g⁻¹) (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjActHom_hom_apply {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) (a : A) :
    (conjActHom g A).hom a = A.ρ g a := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem conj_map_eq_id_zero (k G : Type) [CommRing k] [Group G] (g : G) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A) (hu : ∀ a, u.hom a = A.ρ g a) :
    groupHomology.map (MulAut.conj g).toMonoidHom u 0 = 𝟙 _ := by
  rw [← cancel_epi (groupHomology.H0π A), groupHomology.H0π_comp_map, Category.comp_id]
  ext a
  have hv : (groupHomology.H0π A).hom (A.ρ g a) = (groupHomology.H0π A).hom a := by
    rw [← groupHomology.coinvariantsMk_comp_H0Iso_inv]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    congr 1
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [← hv, ← hu]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_map_eq_id : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) →
    groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  intro k G _ _ g n
  induction n with
  | zero => exact conj_map_eq_id_zero k G g
  | succ n ih =>
    intro A u hu
    obtain ⟨ι, K, i, e, h, hS⟩ := exists_free_shortExact k G A
    have hP : IsZero (groupHomology (Rep.free k G ι) (n + 1)) :=
      GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G (Rep.free k G ι) inferInstance n
    have hmono := groupHomology.mono_δ_of_isZero hS n hP
    have hnat := (GlobalTheory.T.groupHomology_longExact_maps_natural_of_res k G G (MulAut.conj g).toMonoidHom _ _ hS hS
      (conjActHom g K) (conjActHom g (Rep.free k G ι)) u
      (fun a => by
        change (Rep.free k G ι).ρ g (i.hom a) = i.hom (K.ρ g a)
        exact (Rep.hom_comm_apply i g a).symm)
      (fun a => by
        change u.hom (e.hom a) = e.hom ((Rep.free k G ι).ρ g a)
        rw [hu]
        exact (Rep.hom_comm_apply e g a).symm) n).1
    rw [ih K (conjActHom g K) (fun _ => rfl), Category.comp_id] at hnat
    rw [← cancel_mono (groupHomology.δ hS (n + 1) n rfl), Category.id_comp]
    exact hnat.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.T.innerAut_acts_trivially_groupHomology : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G) (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) → groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  first
  | exact @GlobalTheory.HomStab.conj_map_eq_id
  | exact @GlobalTheory.HomStab.conj_map_eq_id_zero
  | exact @GlobalTheory.HomStab.conjActHom_hom_apply
end
