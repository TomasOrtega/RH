import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionCompGeneralLinearGroupMapOfFie
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IndField.multiProd_comp_glMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FParabolicInductionCompGeneralLinearGroupMapOfFie.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.parabolicInduction_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → (∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x) → ∀ {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.multiProd e σ).comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) (GlobalTheory.SmGL.multiProd e fun a => (σ a).comp (Matrix.GeneralLinearGroup.map (n := m a) i.symm.toRingHom))) := by
  first | exact @GlobalTheory.IndField.multiProd_comp_glMap | exact GlobalTheory.IndField.multiProd_comp_glMap | (intros; apply GlobalTheory.IndField.multiProd_comp_glMap <;> assumption)
