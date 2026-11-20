import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonHomExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomLocalizationAwayOfRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMultiplicativeGroupOpenNonvanishingPolynomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS.ArcInf

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩`.
-/
theorem smConn_gm (k : Type) [Field k] : SmConn (Gm (Sp k)) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

noncomputable def selfIso (k : Type) [CommRing k] : algOver k k ≅ 𝟙_ (Over (Sp k)) :=
  Over.isoMk (Iso.refl _) (by
    show 𝟙 _ ≫ 𝟙 _ = spMap (algebraMap k k)
    rw [Category.comp_id]
    exact (Spec.map_id _).symm)

/- English proof (translation)
Establish `h` using `Polynomial.aeval_algHom_apply (x.comp (IsScalarTower.toAlgHom k (Polynomial k) B)) Polynomial.X q`. Rewrite `h` using `[Polynomial.aeval_X_left_apply, Polynomial.coe_aeval_eq_eval]`. Conclude with `h.symm`.
-/
theorem algHom_algebraMap_eq_eval {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B] (x : B →ₐ[k] k) (q : Polynomial k) :
    x (algebraMap (Polynomial k) B q) = q.eval (x (algebraMap (Polynomial k) B Polynomial.X)) := by
  have h := Polynomial.aeval_algHom_apply (x.comp (IsScalarTower.toAlgHom k (Polynomial k) B))
    Polynomial.X q
  rw [Polynomial.aeval_X_left_apply, Polynomial.coe_aeval_eq_eval] at h
  exact h.symm

/- English proof (translation)
Introduce `k _ _ G _ A _ _ j ε r f Pd P ψ hG hc hPd hP hψ hmul`. Take `⟨χ, hχ⟩` from `GlobalTheory.T.exists_algHom_localizationAway_of_rational_points' k A r f Pd P ψ hc.2.2.1 hPd hψ`. Take `⟨jj, hjj, hjm⟩` from `GlobalTheory.T.exists_multiplicativeGroup_open_nonvanishing_polynomial k Pd`. Establish `hq : Polynomial.X * Pd ≠ 0` using `mul_ne_zero Polynomial.X_ne_zero hPd`. Establish `hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd)))` using `IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hq)`.

Establish `hnt : Nontrivial (Localization.Away (Polynomial.X * Pd))` using `hinj.nontrivial`. Establish `hu : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd)) (Polynomial.X * Pd))` using `IsLocalization.Away.algebraMap_isUnit _`. Establish `hpt : ∀ x : Localization.Away (Polynomial.X * Pd) →ₐ[k] k, x (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 ∧ Pd.eval (x (algebraMap (Polynomial k) _ Polynomial.X)) ≠ 0 ∧ x.comp χ = ψ (x (algebraMap (Polynomial k) _ Polynomial.X))`. Introduce `x`. Establish `h` using `(hu.map x).ne_zero`.

Rewrite `h` using `[algHom_algebraMap_eq_eval, Polynomial.eval_mul, Polynomial.eval_X]`. Establish `h1` using `left_ne_zero_of_mul h`. Establish `h2` using `right_ne_zero_of_mul h`. Use `⟨h1, h2, hc.hom_ext fun i => mul_right_cancel₀ h2 ?_⟩` and prove the remaining obligations. Rewrite using `[hψ _ h1 h2, AlgHom.comp_apply, ← algHom_algebraMap_eq_eval x Pd, ← map_mul, hχ, algHom_algebraMap_eq_eval x (P i)]`.

Take `⟨F, hF, hFj⟩` from `GlobalTheory.GenericHom.exists_monHom_extension k (Gm (Sp k)) G (algOver k (Localization.Away (Polynomial.X * Pd))) (smConn_gm k) hG jj (algOverHom χ ≫ j) hjj (inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away (Polynomial.X * Pd))))) (by`. Introduce `x y z h`. Take `⟨x', hx⟩` from `algOverHom_surjective ((selfIso k).hom ≫ x)`. Take `⟨y', hy⟩` from `algOverHom_surjective ((selfIso k).hom ≫ y)`. Take `⟨z', hz⟩` from `algOverHom_surjective ((selfIso k).hom ≫ z)`.

Establish `h'` using `hjm x' y' z' (by`. Rewrite using `[hx, hy, hz, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, h])`. Take `⟨a1, a2, a3⟩` from `hpt x'`. Take `⟨b1, b2, b3⟩` from `hpt y'`. Take `⟨c1, c2, c3⟩` from `hpt z'`.

Establish `hm` using `hmul _ _ a1 b1 a2 b2 (h' ▸ c2)`. Rewrite `hm` using `[h', ← a3, ← b3, ← c3, algOverHom_comp, algOverHom_comp, algOverHom_comp, hx, hy, hz]`. Simplify using `only [Category.assoc] at hm`. Rewrite `hm` using `[← MonObj.comp_mul]`. Conclude with `(cancel_epi (selfIso k).hom).1 hm)`.

Use `⟨F, hF, fun h1 => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hP`. Establish `e : χ = (Algebra.ofId k _).comp ε`. Apply `eq_of_comp_eq hc.1` to reduce the goal to its premises. Rewrite using `[← hFj, h1, MonObj.comp_one, algOverHom_comp, Category.assoc, hc.2.1, MonObj.comp_one]`.

Establish `h2` using `hχ i`. Rewrite `h2` using `[e, AlgHom.comp_apply, hc.2.2.2, _root_.map_zero, zero_mul]`. Conclude with `hi (hinj (h2.symm.trans (_root_.map_zero _).symm))`.
-/
theorem exists_oneParameter_of_rational_family : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), SmConn G → IsChart G j ε f → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t * t') ≠ 0 → (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t * t')) ≫ j) → ∃ F : Gm (Sp k) ⟶ G, IsMonHom F ∧ F ≠ 1 := by
  intro k _ _ G _ A _ _ j ε r f Pd P ψ hG hc hPd hP hψ hmul
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_algHom_localizationAway_of_rational_points' k A r f Pd P ψ hc.2.2.1 hPd hψ
  obtain ⟨jj, hjj, hjm⟩ := GlobalTheory.T.exists_multiplicativeGroup_open_nonvanishing_polynomial k Pd
  have hq : Polynomial.X * Pd ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hPd
  have hinj : Function.Injective
      (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hq)
  have hnt : Nontrivial (Localization.Away (Polynomial.X * Pd)) := hinj.nontrivial
  have hu : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd))
      (Polynomial.X * Pd)) := IsLocalization.Away.algebraMap_isUnit _
  have hpt : ∀ x : Localization.Away (Polynomial.X * Pd) →ₐ[k] k,
      x (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 ∧
      Pd.eval (x (algebraMap (Polynomial k) _ Polynomial.X)) ≠ 0 ∧
      x.comp χ = ψ (x (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro x
    have h := (hu.map x).ne_zero
    rw [algHom_algebraMap_eq_eval, Polynomial.eval_mul, Polynomial.eval_X] at h
    have h1 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    refine ⟨h1, h2, hc.hom_ext fun i => mul_right_cancel₀ h2 ?_⟩
    rw [hψ _ h1 h2, AlgHom.comp_apply, ← algHom_algebraMap_eq_eval x Pd, ← map_mul, hχ,
      algHom_algebraMap_eq_eval x (P i)]
  obtain ⟨F, hF, hFj⟩ := GlobalTheory.GenericHom.exists_monHom_extension k (Gm (Sp k)) G
    (algOver k (Localization.Away (Polynomial.X * Pd))) (smConn_gm k) hG jj (algOverHom χ ≫ j) hjj
    (inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away (Polynomial.X * Pd))))) (by
      intro x y z h
      obtain ⟨x', hx⟩ := algOverHom_surjective ((selfIso k).hom ≫ x)
      obtain ⟨y', hy⟩ := algOverHom_surjective ((selfIso k).hom ≫ y)
      obtain ⟨z', hz⟩ := algOverHom_surjective ((selfIso k).hom ≫ z)
      have h' := hjm x' y' z' (by
        rw [hx, hy, hz, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, h])
      obtain ⟨a1, a2, a3⟩ := hpt x'
      obtain ⟨b1, b2, b3⟩ := hpt y'
      obtain ⟨c1, c2, c3⟩ := hpt z'
      have hm := hmul _ _ a1 b1 a2 b2 (h' ▸ c2)
      rw [h', ← a3, ← b3, ← c3, algOverHom_comp, algOverHom_comp, algOverHom_comp, hx, hy, hz] at hm
      simp only [Category.assoc] at hm
      rw [← MonObj.comp_mul] at hm
      exact (cancel_epi (selfIso k).hom).1 hm)
  refine ⟨F, hF, fun h1 => ?_⟩
  obtain ⟨i, hi⟩ := hP
  have e : χ = (Algebra.ofId k _).comp ε := by
    apply eq_of_comp_eq hc.1
    rw [← hFj, h1, MonObj.comp_one, algOverHom_comp, Category.assoc, hc.2.1, MonObj.comp_one]
  have h2 := hχ i
  rw [e, AlgHom.comp_apply, hc.2.2.2, _root_.map_zero, zero_mul] at h2
  exact hi (hinj (h2.symm.trans (_root_.map_zero _).symm))

end GlobalTheory.SS.ArcInf
