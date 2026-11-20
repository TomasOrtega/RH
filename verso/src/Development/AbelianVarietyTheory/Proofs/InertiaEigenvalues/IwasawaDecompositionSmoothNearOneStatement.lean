import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwasawaDecompositionSmoothNearOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIwasawaDecompositionSmoothNearOne.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.iwasawa_decomposition_smooth_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N), ∃ (p : Lie E N → parab (Cinf E) e) (k : Lie E N → Kinf E N), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (p y).1.val) (oneL E N) ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (k y).1) (oneL E N) ∧ p (oneL E N) = 1 ∧ k (oneL E N) = 1 ∧ ∀ᶠ y in nhds (oneL E N), Matrix.of y = (p y).1.val * (k y).1 := by
  first | exact @GlobalTheory.SmoothIwasawaNear.exists_local_iwasawa | exact GlobalTheory.SmoothIwasawaNear.exists_local_iwasawa | (intros; apply GlobalTheory.SmoothIwasawaNear.exists_local_iwasawa <;> assumption)
