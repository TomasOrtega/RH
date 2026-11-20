import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfield
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGalois
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.SplitAttUniq

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
Take `⟨N, hN0, hN⟩` from `GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield E`. Establish `hne : (((l * N : ℕ) : 𝓞 E)) ≠ 0` using `Nat.cast_ne_zero.2 (mul_ne_zero hl.ne_zero hN0)`. Establish `hT : (S ∪ {w : HeightOneSpectrum (𝓞 E) | ((l * N : ℕ) : 𝓞 E) ∈ w.asIdeal}).Finite` using `hS.union (GlobalTheory.HeckeSplit.finite_setOf_mem_asIdeal E _ hne)`. Establish `hD` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hT`. Establish `hD'` using `hD.preimage (Homeomorph.inv (G E Ω)).isOpenMap`.

Use `hD'.mono ?_` and prove the remaining obligations. Introduce and unpack `g ⟨v, hv, hd, A, hA, hσ⟩`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or] at hv`. Establish `hlN : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∧ ((N : ℕ) : 𝓞 E) ∉ v.asIdeal`. Apply the tactic sequence `constructor <;> intro h <;> apply hv.2 <;> rw [Nat.cast_mul]`.

Conclude with `v.asIdeal.mul_mem_right _ h`. Conclude with `v.asIdeal.mul_mem_left _ h`. Establish `hu` using `hN E v hlN.2`. Conclude with `⟨v, hv.1, UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E v hu hd, hlN.1, A, hA, hσ⟩`.
-/
theorem dense_splitFrobInv_away (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) (hl : l.Prime) (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) :
    Dense {g : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ S ∧ IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) g⁻¹} := by
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield E
  have hne : (((l * N : ℕ) : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 (mul_ne_zero hl.ne_zero hN0)
  have hT : (S ∪ {w : HeightOneSpectrum (𝓞 E) | ((l * N : ℕ) : 𝓞 E) ∈ w.asIdeal}).Finite :=
    hS.union (GlobalTheory.HeckeSplit.finite_setOf_mem_asIdeal E _ hne)
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hT
  have hD' := hD.preimage (Homeomorph.inv (G E Ω)).isOpenMap
  refine hD'.mono ?_
  rintro g ⟨v, hv, hd, A, hA, hσ⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hv
  have hlN : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∧ ((N : ℕ) : 𝓞 E) ∉ v.asIdeal := by
    constructor <;> intro h <;> apply hv.2 <;> rw [Nat.cast_mul]
    · exact v.asIdeal.mul_mem_right _ h
    · exact v.asIdeal.mul_mem_left _ h
  have hu := hN E v hlN.2
  exact ⟨v, hv.1, UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E v hu hd, hlN.1, A, hA, hσ⟩

/- English proof (translation)
Establish `hcp : ∀ g : G E Ω, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly`. Introduce `g`. Use extensionality with `i`. Establish `h1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i` using `(contCoeff a i).comp (Units.continuous_val.comp hc)`. Establish `h2 : Continuous fun g : G E Ω => (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i` using `(contCoeff a i).comp (Units.continuous_val.comp hc')`.

Use `congrFun (Continuous.ext_on hD h1 h2 ?_) g` and prove the remaining obligations. Introduce `σ hσ`. Simplify using `only [he σ hσ]`. Take `⟨P, hP⟩` from `Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' hcp`. Conclude with `⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩`.
-/
theorem repIso_of_dense {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
    (r r' : G E Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (D : Set (G E Ω)) (hD : Dense D)
    (he : ∀ g ∈ D, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    UpperTheory.V.Af.RepIso r r' := by
  have hcp : ∀ g : G E Ω, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc)
    have h2 : Continuous fun g : G E Ω => (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc')
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    intro σ hσ
    simp only [he σ hσ]
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' hcp
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.SplitAttUniq
