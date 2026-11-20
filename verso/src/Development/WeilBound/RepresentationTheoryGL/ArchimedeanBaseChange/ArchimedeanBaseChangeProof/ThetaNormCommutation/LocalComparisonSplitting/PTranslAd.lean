import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem translad_map_PhiU (n : ℕ) {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) :
    GeneralLinearGroup.map p (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  change p ((PhiU n R).val i j) = (PhiU n S).val i j
  rw [phiU_val, phiU_val]
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem translad_thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  rw [thetaR_val, ← map_inv (thetaR σ n) g, thetaR_val, inv_inv]
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, hσ]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem translad_central (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E)
    (hu : IsTransl u) : u⁻¹ * PhiU n E ∈ Subgroup.center (GL (Fin n) E) := by
  have hcc : ∀ x, conjE E (conjE E x) = x := fun x => IsCMField.complexConj_apply_apply (K := E) x
  refine Subgroup.mem_center_iff.mpr fun h => ?_
  have h2 : thetaE E n (thetaE E n h) = h := translad_thetaR_thetaR (conjE E) hcc n h
  have h1 := hu.1 (thetaE E n h)
  rw [h2] at h1
  have h3 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
    rw [show thE E n (thetaE E n h) = thetaGL n (conjE E) (thetaE E n h) from rfl, thetaGL_eq]
    exact congrArg (fun x => PhiU n E * x * (PhiU n E)⁻¹) h2
  rw [h3] at h1
  calc h * (u⁻¹ * PhiU n E) = u⁻¹ * (u * h * u⁻¹) * PhiU n E := by group
    _ = u⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹) * PhiU n E := by rw [h1]
    _ = u⁻¹ * PhiU n E * h := by group

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable.

Chain the equalities or inequalities of the calculation.
-/
theorem translAd_holds : TranslAd := by
  intro E _ _ _ n u hu g
  have hz := GeneralLinearGroup.map_center_le (algebraMap E (Ad E)) (translad_central E n u hu)
  rw [Subgroup.mem_comap, map_mul, map_inv, translad_map_PhiU] at hz
  have hr : ratGL E n u = GeneralLinearGroup.map (algebraMap E (Ad E)) u := rfl
  rw [hr, thetaGL_eq]
  change PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹ =
    GeneralLinearGroup.map (algebraMap E (Ad E)) u * thetaR (conjAd E) n g *
      (GeneralLinearGroup.map (algebraMap E (Ad E)) u)⁻¹
  have hcomm := Subgroup.mem_center_iff.mp hz (thetaR (conjAd E) n g)
  generalize thetaR (conjAd E) n g = T at hcomm ⊢
  generalize GeneralLinearGroup.map (algebraMap E (Ad E)) u = U at hcomm ⊢
  generalize PhiU n (Ad E) = P at hcomm ⊢
  calc P * T * P⁻¹ = U * ((U⁻¹ * P) * T) * (U⁻¹ * P)⁻¹ * U⁻¹ := by group
    _ = U * (T * (U⁻¹ * P)) * (U⁻¹ * P)⁻¹ * U⁻¹ := by rw [hcomm]
    _ = U * T * U⁻¹ := by group

end PositivityTheory.Rg.BcB.G8

end
