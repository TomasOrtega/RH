import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisLatticeOfInverseAdelicMatrixFami
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalBasisLatticeOfInverseAdelicMatrixFami.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_localBasis_lattice_of_inverse_adelicMatrixFamily : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K), IsAdelic A → ∀ P : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
  first | exact @GlobalTheory.LocMatBasis.exists_locBasis_inv | exact GlobalTheory.LocMatBasis.exists_locBasis_inv | (intros; apply GlobalTheory.LocMatBasis.exists_locBasis_inv <;> assumption)
