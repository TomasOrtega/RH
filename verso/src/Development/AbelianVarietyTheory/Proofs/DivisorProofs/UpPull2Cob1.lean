import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

namespace Katz

namespace ExtCoeff

variable {O E : Type} [CommRing O] [CommRing E] {d : ℕ}

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`.
-/
theorem hasSubst_XL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`.
-/
theorem hasSubst_XR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

/- English proof (translation)
Unfold `inL`. Rewrite using `[map_subst hasSubst_XL]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `map_X h _`.
-/
theorem map_inL (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inL f) = inL (map h f) := by
  unfold inL
  rw [map_subst hasSubst_XL]
  congr 1
  funext i
  exact map_X h _

/- English proof (translation)
Unfold `inR`. Rewrite using `[map_subst hasSubst_XR]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `map_X h _`.
-/
theorem map_inR (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inR f) = inR (map h f) := by
  unfold inR
  rw [map_subst hasSubst_XR]
  congr 1
  funext i
  exact map_X h _

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) hf`.
-/
theorem inL_const {f : MvPowerSeries (Fin d) O} (hf : constantCoeff f = 0) :
    constantCoeff (inL f) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) hf

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) hf`.
-/
theorem inR_const {f : MvPowerSeries (Fin d) O} (hf : constantCoeff f = 0) :
    constantCoeff (inR f) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) hf

/- English proof (translation)
Unfold `pull2 at2`. Rewrite using `[map_subst (CobCob.elim_has (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i)))]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Consider the cases of `j with`.

Consider the case `inl i => exact (map_inL h (φ i)).symm`. Consider the case `inr i => exact (map_inR h (φ i)).symm`.
-/
theorem map_pull2 (h : O →+* E) (φ : Fin d → MvPowerSeries (Fin d) O)
    (t : MvPowerSeries (Fin d ⊕ Fin d) O) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    pull2 (fun i => map h (φ i)) (map h t) = map h (pull2 φ t) := by
  unfold pull2 at2
  rw [map_subst (CobCob.elim_has (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i)))]
  congr 1
  funext j
  cases j with
  | inl i => exact (map_inL h (φ i)).symm
  | inr i => exact (map_inR h (φ i)).symm

/- English proof (translation)
Unfold `cob1`. Rewrite using `[map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ), map_inL, map_inR]`.
-/
theorem map_formalGroupLawCoboundaryOne_eq (h : O →+* E) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (s : MvPowerSeries (Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    cob1 (fun i => map h (μ i)) (map h s) = map h (cob1 μ s) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ), map_inL, map_inR]

/- English proof (translation)
Introduce `O E _ _ _ d`. Conclude with `⟨fun φ t hφ => map_pull2 (algebraMap O E) φ t hφ, fun μ s hμ => map_formalGroupLawCoboundaryOne_eq (algebraMap O E) μ s hμ⟩`.
-/
theorem up_pull2_cob1 : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ), (∀ (φ : Fin d → MvPowerSeries (Fin d) O) (t : MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, constantCoeff (φ i) = 0) → pull2 (up E φ) (map (algebraMap O E) t) = map (algebraMap O E) (pull2 φ t)) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (s : MvPowerSeries (Fin d) O), (∀ i, constantCoeff (μ i) = 0) → cob1 (up E μ) (map (algebraMap O E) s) = map (algebraMap O E) (cob1 μ s) := by
  intro O E _ _ _ d
  exact ⟨fun φ t hφ => map_pull2 (algebraMap O E) φ t hφ,
    fun μ s hμ => map_formalGroupLawCoboundaryOne_eq (algebraMap O E) μ s hμ⟩

end ExtCoeff

end Katz

end GlobalTheory
