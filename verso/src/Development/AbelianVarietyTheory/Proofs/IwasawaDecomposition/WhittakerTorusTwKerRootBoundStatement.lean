import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.whittaker_torus_twKer_rootBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWhittakerTorusTwKerRootBound.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.whittaker_torus_twKer_rootBound' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (l : Module.Dual ℂ V), IsFunctional ψ ρ l → ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = n) (i j : Fin n), i.val + 1 = a → j.val = a → ∀ x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1, ∃ r : kˣ, ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i : k) / t j) := by
  first | exact @GlobalTheory.whittaker_torus_twKer_rootBound | exact GlobalTheory.whittaker_torus_twKer_rootBound | (intros; apply GlobalTheory.whittaker_torus_twKer_rootBound <;> assumption)
