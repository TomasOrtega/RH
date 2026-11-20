import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsCuspidalSatakeAtPrimeToLevelOfNewform

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
/- English proof (translation)
Introduce `P hQ l _ Ω _ _ _ ι e V A κ g hl he hc hirr hdet hA hex hatt hgM σ hσ`. Take `⟨π, hreg, hπ, hsat⟩` from `_root_.GlobalTheory.T.exists_cuspidal_attached_satake_eq_hecke_poly_of_not_dvd P e g l Ω ι V he hatt hgM`. Take `⟨v, hv, hlv⟩` from `hA`. Take `⟨B, hB, hpoly⟩` from `hsat v hlv`. Take `⟨b, hb, hrel⟩` from `(hQ l hl Ω ι e he V π hc hirr hdet hreg hπ v A κ hlv hv hex (Or.inr ⟨B, hB⟩)).2 B hB σ hσ`.

Use `⟨(l : ℂ) ^ e * b, ?_, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[← hpoly, Polynomial.IsRoot, Polynomial.eval_multiset_prod]`. Use `Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map_of_mem _ hb, ?_⟩)` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `(eq_inv_of_mul_eq_one_left ?_).symm` and prove the remaining obligations.

Rewrite `hrel` using `[zpow_natCast]`. Take the linear combination `hrel`.
-/
theorem frobRoot_alt : _root_.UpperTheory.V.Af.Hypotheses' → LocQ → FrobRoot := by
  intro P hQ l _ Ω _ _ _ ι e V A κ g hl he hc hirr hdet hA hex hatt hgM σ hσ
  obtain ⟨π, hreg, hπ, hsat⟩ := _root_.GlobalTheory.T.exists_cuspidal_attached_satake_eq_hecke_poly_of_not_dvd P e g l Ω ι V he hatt hgM
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨B, hB, hpoly⟩ := hsat v hlv
  obtain ⟨b, hb, hrel⟩ :=
    (hQ l hl Ω ι e he V π hc hirr hdet hreg hπ v A κ hlv hv hex (Or.inr ⟨B, hB⟩)).2 B hB σ hσ
  refine ⟨(l : ℂ) ^ e * b, ?_, Or.inr ?_⟩
  · rw [← hpoly, Polynomial.IsRoot, Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map_of_mem _ hb, ?_⟩)
    simp
  · refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [zpow_natCast] at hrel
    linear_combination hrel
end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end
