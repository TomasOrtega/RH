import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityPerfectPairFiniteModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocalPair.local_pair` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalDualityPerfectPairFiniteModules.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.localDuality_perfect_pair_finite_modules : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  first | exact @GlobalTheory.LocalPair.local_pair | exact GlobalTheory.LocalPair.local_pair | (intros; apply GlobalTheory.LocalPair.local_pair <;> assumption)
