import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.CommAlg.Hens

open Polynomial IsLocalRing

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap R C)` using `IsFractionRing.injective R C`. Establish `hdeg : (f.map (algebraMap R C)).degree ≠ 0`. Rewrite using `[hf.degree_map]`. Conclude with `(natDegree_pos_iff_degree_pos.mp hd).ne'`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root (f.map (algebraMap R C)) hdeg`.

Establish `hxa : aeval x f = 0`. Rewrite using `[aeval_def, ← Polynomial.eval_map]`. Conclude with `hx`. Establish `hint : IsIntegral R x` using `⟨f, hf, by rw [← aeval_def]; exact hxa⟩`. Take `⟨r, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`.

Use `⟨r, hinj ?_⟩` and prove the remaining obligations. Establish `hr0 : algebraMap R C (f.eval r) = aeval (algebraMap R C r) f` using `(aeval_algebraMap_apply_eq_algebraMap_eval r f).symm`. Rewrite using `[hr0, hxa, map_zero]`.
-/
theorem exists_isRoot_of_monic {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C]
    {f : R[X]} (hf : f.Monic) (hd : 0 < f.natDegree) : ∃ r : R, f.IsRoot r := by
  have hinj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  have hdeg : (f.map (algebraMap R C)).degree ≠ 0 := by
    rw [hf.degree_map]
    exact (natDegree_pos_iff_degree_pos.mp hd).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap R C)) hdeg
  have hxa : aeval x f = 0 := by
    rw [aeval_def, ← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral R x := ⟨f, hf, by rw [← aeval_def]; exact hxa⟩
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, hinj ?_⟩
  have hr0 : algebraMap R C (f.eval r) = aeval (algebraMap R C r) f :=
    (aeval_algebraMap_apply_eq_algebraMap_eval r f).symm
  rw [hr0, hxa, map_zero]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `f hf hn a₀ h`. Establish `: f = 1` using `hf.natDegree_eq_zero.mp hn`. Substitute `this` using the available equality.

Rewrite `h` using `[eval_one]`. Conclude with `absurd h (Ideal.ne_top_iff_one _ |>.mp (maximalIdeal.isMaximal R).ne_top)`. Consider the case `succ n ih`. Introduce `f hf hn a₀ h`. Take `⟨r, hr⟩` from `exists_isRoot_of_monic (C := C) hf (by omega)`.

Establish `hfac : (X - Polynomial.C r) * (f /ₘ (X - Polynomial.C r)) = f` using `mul_divByMonic_eq_iff_isRoot.mpr hr`. Establish `hgm : (f /ₘ (X - Polynomial.C r)).Monic` using `(monic_X_sub_C r).of_mul_monic_left (hfac.symm ▸ hf)`. Establish `hgd : (f /ₘ (X - Polynomial.C r)).natDegree = n`. Rewrite using `[natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]`. Both sides reduce to the same expression.

Rewrite `h` using `[← hfac, eval_mul, eval_sub, eval_X, eval_C]`. Break down `(maximalIdeal.isMaximal R).isPrime.mem_or_mem h with h1 | h1` into its components or cases. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Use `(maximalIdeal R).neg_mem h1` as an intermediate fact. Simplify using `using this`.

Take `⟨a, ha, ham⟩` from `ih _ hgm hgd a₀ h1`. Use `⟨a, ?_, ham⟩` and prove the remaining obligations. Rewrite using `[IsRoot.def, ← hfac, eval_mul, ha.eq_zero, mul_zero]`.
-/
theorem exists_root_near {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C] (n : ℕ) :
    ∀ (f : R[X]), f.Monic → f.natDegree = n → ∀ a₀ : R, f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  induction n with
  | zero =>
    intro f hf hn a₀ h
    have : f = 1 := hf.natDegree_eq_zero.mp hn
    subst this
    rw [eval_one] at h
    exact absurd h (Ideal.ne_top_iff_one _ |>.mp (maximalIdeal.isMaximal R).ne_top)
  | succ n ih =>
    intro f hf hn a₀ h
    obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hf (by omega)
    have hfac : (X - Polynomial.C r) * (f /ₘ (X - Polynomial.C r)) = f :=
      mul_divByMonic_eq_iff_isRoot.mpr hr
    have hgm : (f /ₘ (X - Polynomial.C r)).Monic := (monic_X_sub_C r).of_mul_monic_left (hfac.symm ▸ hf)
    have hgd : (f /ₘ (X - Polynomial.C r)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]; rfl
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h with h1 | h1
    · refine ⟨r, hr, ?_⟩
      have := (maximalIdeal R).neg_mem h1
      simpa using this
    · obtain ⟨a, ha, ham⟩ := ih _ hgm hgd a₀ h1
      refine ⟨a, ?_, ham⟩
      rw [IsRoot.def, ← hfac, eval_mul, ha.eq_zero, mul_zero]

/- English proof (translation)
Introduce `C _ _ R _ _ _ _ _`. Use `⟨⟨fun f hf a₀ h _ => exists_root_near (C := C) _ f hf rfl a₀ h⟩, ?_⟩` and prove the remaining obligations. Use `IsAlgClosed.of_exists_root _ fun p hp hirr => ?_` and prove the remaining obligations. Establish `hlift : p ∈ lifts (residue R)` using `(lifts_iff_coeff_lifts p).mpr fun n => residue_surjective (p.coeff n)`. Take `⟨q, hq, hqd, hqm⟩` from `lifts_and_natDegree_eq_and_monic hlift hp`.

Establish `hpos : 0 < q.natDegree`. Rewrite using `[hqd]`. Conclude with `hirr.natDegree_pos`. Take `⟨r, hr⟩` from `exists_isRoot_of_monic (C := C) hqm hpos`. Use `⟨residue R r, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hq, eval_map_apply, hr.eq_zero, map_zero]`.
-/
theorem henselian_and_residueField_isAlgClosed : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C],
    HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  intro C _ _ R _ _ _ _ _
  refine ⟨⟨fun f hf a₀ h _ => exists_root_near (C := C) _ f hf rfl a₀ h⟩, ?_⟩
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hlift : p ∈ lifts (residue R) :=
    (lifts_iff_coeff_lifts p).mpr fun n => residue_surjective (p.coeff n)
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hp
  have hpos : 0 < q.natDegree := by
    rw [hqd]; exact hirr.natDegree_pos
  obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hqm hpos
  refine ⟨residue R r, ?_⟩
  rw [← hq, eval_map_apply, hr.eq_zero, map_zero]

end GlobalTheory.CompanionTheory.CommAlg.Hens
