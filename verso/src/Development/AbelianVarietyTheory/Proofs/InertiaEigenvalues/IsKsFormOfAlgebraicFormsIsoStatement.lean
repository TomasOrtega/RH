import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
open NumberField Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isKsForm_of_formsIso` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsKsFormOfAlgebraicFormsIso.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isKsForm_of_algebraicFormsIso : ∀ {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G'),
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  first | exact @GlobalTheory.isKsForm_of_formsIso | exact GlobalTheory.isKsForm_of_formsIso | (intros; apply GlobalTheory.isKsForm_of_formsIso <;> assumption)
