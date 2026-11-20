import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial

/- English proof (translation)
Establish `h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) = fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ K (Fin n)).coeff i)`. Use function extensionality and compare the values at `M`. Conclude with `(Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm`. Rewrite using `[h]`. Conclude with `(MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))`.
-/
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

/- English proof (translation)
Introduce `_ F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw`. Establish `hD` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' (Filter.eventually_cofinite.1 hw)`. Establish `hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly`. Introduce `g`. Use extensionality with `i`.

Establish `h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i` using `(contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))`. Establish `h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i` using `(contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))`. Use `congrFun (Continuous.ext_on hD h1 h2 ?_) g` and prove the remaining obligations. Introduce and unpack `σ ⟨v, hv, -, A, hA, hσ⟩`. Take `⟨B, hB, hB'⟩` from `not_not.1 hv`.

Establish `h` using `((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm`. Establish `h'` using `Polynomial.map_injective ι.toRingHom ι.injective h`. Simplify using `only [h']`. Take `⟨P, hP⟩` from `Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)`. Conclude with `⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩`.
-/
theorem UpperTheory.V.Af.isoOfFrob :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IsoOfFrob := by
  intro _ F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
