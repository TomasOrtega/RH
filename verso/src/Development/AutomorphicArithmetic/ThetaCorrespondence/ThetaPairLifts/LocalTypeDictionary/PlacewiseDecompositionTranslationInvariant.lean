import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KTypeClassTranslate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KTypeClassTranslateStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
/- English proof (translation)
Introduce `D θ hθ hp N U W _ _ ρ τ g hg`. Use `haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _`. Establish `hP` using `N.M.fr_unit τ`. Establish `hJ` using `N.M.fr_gram τ`. Use `haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1`.

Establish `hσ : Std (N.M.ε τ) (N.M.σ τ)` using `std_of_isDS hp.harishChandraModules (N.M.ds τ)`. Establish `hk : (N.M.fr τ)⁻¹ * g * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)` using `conj_inv_mem hP hJ hg`. Establish `comm : ∀ τ', τ' ≠ τ → ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'), atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) * atTau θ N.V τ' h = atTau θ N.V τ' h * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)` using `fun τ' hne h hh => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm hne) _ hk h hh`. Use `⟨rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `f hf`.

Conclude with `hf.comp (continuous_mul_right _)`. Introduce `f f' _ _`. Both sides reduce to the same expression. Introduce `c f _`. Both sides reduce to the same expression.

Introduce and unpack `f ⟨⟨a1, a2, a3⟩, a4⟩`. Use `⟨⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ N.V f a1 τ _ hk, GlobalTheory.Cusp.isCuspFun_rTr a2 _, fun τ' => GlobalTheory.CuspGKForms.isTypeAt_rTr hθ (a3 τ') hk⟩, fun k hkU hkf x => ?_⟩` and prove the remaining obligations. Simplify using `only [rTr]`. Rewrite using `[mul_assoc x, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc x]`. Conclude with `a4 k hkU hkf _`.

Introduce `τ' hne f _ hf x`. Establish `e : (fun k => rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)) f (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) = fun k => f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)` using `funext fun k => by`. Simplify using `only [rTr, GlobalTheory.Published.AutFin.kAt]`. Rewrite using `[mul_assoc x, mul_assoc x, comm τ' hne _ (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k)]`. Use `show (fun k => _) ∈ _`.

Rewrite using `[e]`. Conclude with `hf _`. Introduce `τ' hne h hh f _`. Use function extensionality and compare the values at `x`. Simplify using `only [rTr]`.

Rewrite using `[mul_assoc x, mul_assoc x, comm τ' hne h hh]`. Introduce `τ' hne X hX f _`. Use function extensionality and compare the values at `x`. Simplify using `only [Rder, rTr, oneP]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Rewrite using `[mul_assoc x, mul_assoc x, comm τ' hne _ (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit N.V τ') hX t)]`. Introduce `φ _ x S v ℓ C hS _ h`. Conclude with `h.translate hσ.1 hS hg fun y hy => by`. Simplify using `only [res, rTr, at_mul hθ hP hJ hy hg, mul_assoc x]`.
-/
theorem placeDecomposition_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), ∀ g ∈ UJset (N.M.ε τ), HasCtp θ N U (TyOf θ N ρ) τ (N.M.σ τ g) := by
  intro D θ hθ hp N U W _ _ ρ τ g hg
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hk : (N.M.fr τ)⁻¹ * g * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := conj_inv_mem hP hJ hg
  have comm : ∀ τ', τ' ≠ τ → ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'),
      atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) * atTau θ N.V τ' h =
        atTau θ N.V τ' h * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) :=
    fun τ' hne h hh => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm hne) _ hk h hh
  refine ⟨rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    exact hf.comp (continuous_mul_right _)
  · intro f f' _ _
    rfl
  · intro c f _
    rfl
  · rintro f ⟨⟨a1, a2, a3⟩, a4⟩
    refine ⟨⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ N.V f a1 τ _ hk, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => GlobalTheory.CuspGKForms.isTypeAt_rTr hθ (a3 τ') hk⟩, fun k hkU hkf x => ?_⟩
    simp only [rTr]
    rw [mul_assoc x, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc x]
    exact a4 k hkU hkf _
  · intro τ' hne f _ hf x
    have e : (fun k => rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)) f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) =
        fun k => f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) *
          GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) := funext fun k => by
      simp only [rTr, GlobalTheory.Published.AutFin.kAt]
      rw [mul_assoc x, mul_assoc x, comm τ' hne _
        (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k)]
    show (fun k => _) ∈ _
    rw [e]
    exact hf _
  · intro τ' hne h hh f _
    funext x
    simp only [rTr]
    rw [mul_assoc x, mul_assoc x, comm τ' hne h hh]
  · intro τ' hne X hX f _
    funext x
    simp only [Rder, rTr, oneP]
    congr 1
    funext t
    rw [mul_assoc x, mul_assoc x, comm τ' hne _
      (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit N.V τ') hX t)]
  · intro φ _ x S v ℓ C hS _ h
    exact h.translate hσ.1 hS hg fun y hy => by
      simp only [res, rTr, at_mul hθ hP hJ hy hg, mul_assoc x]
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.placewise_decomposition_translation_invariant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), ∀ g ∈ UJset (N.M.ε τ), HasCtp θ N U (TyOf θ N ρ) τ (N.M.σ τ g) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate <;> assumption)
end
