import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralFiniteRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralFiniteRelationStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ThetaFinRelDef
open GlobalTheory.SquareComm
open scoped ComplexOrder
/- English proof (translation)
Introduce `_ D ψ θ hψ hθ M X A B χ χ' ω hω hsig ν 𝓕 hF`. Establish `hω' : IsWeilDatumO ψ M X χ χ' ω` using `hω`. Establish `hpd : ∀ τ, (gramAt D M τ).PosDef` using `fun τ => GlobalTheory.Core.CoefGram.posDef_of_hasSignature _ (hsig τ)`. Establish `hcc : GlobalTheory.Unf.CoCpt M` using `(GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D M).2 hpd`. Establish `hth : ∀ Φ ∈ algF ψ θ false A B, IsThetaFunO ψ M X Φ` using `fun Φ hΦ => GlobalTheory.SquareComm.ThetaLeft.isThetaFunO_of_mem_algF hψ hθ A B hΦ`.

Establish `hleft` using `GlobalTheory.SquareComm.ThetaLeft.main D ψ θ hθ M X A B χ χ' ω hω`. Establish `hsub : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ - Ψ) = thetaKO ω g k Φ - thetaKO ω g k Ψ` using `by intros; simp [thetaKO, map_sub]`. Establish `hadd : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ + Ψ) = thetaKO ω g k Φ + thetaKO ω g k Ψ` using `by intros; simp [thetaKO, map_add]`. Establish `hsmul : ∀ g k (c : ℂ) (Φ : WO M X → ℂ), thetaKO ω g k (c • Φ) = c * thetaKO ω g k Φ` using `by intros; simp [thetaKO, map_smul]`. Establish `hzero : ∀ g k, thetaKO ω g k (0 : WO M X → ℂ) = 0` using `by intros; simp [thetaKO]`.

Establish `hint : ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν`. Introduce `Φ hΦ h`. Conclude with `(GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D M hcc _ ⟨fun γ hγ g => hleft Φ hΦ γ hγ g h, (hω'.om_cont Φ (hth Φ hΦ) 0).comp (Continuous.prodMk_left h)⟩).2.2 ⟨ν, 𝓕, hF.1, hF.2⟩`. Introduce `Φ hΦ`. It suffices to establish `key : (∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν) ∧ thetaInt ω ν 𝓕 Φ = 0 from key.2`.

Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, -, Ψ, hΨ, rfl⟩` from `hx`. Establish `e : ∀ g k, thetaKO ω g k (ω (u, 1) Ψ) = thetaKO ω (g * u) k Ψ` using `fun g k => by`. Unfold `thetaKO`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`. Establish `tr` using `fun k => integral_rightTranslate hF (f := fun g => thetaKO ω g k Ψ) (fun γ hγ g => hleft Ψ hΨ γ hγ g k) u`. Establish `i1 : ∀ k, IntegrableOn (fun g => thetaKO ω g k (ω (u, 1) Ψ)) 𝓕 ν` using `fun k => by`. Simplify using `only [e]`. Conclude with `(tr k).1.2 (hint Ψ hΨ k)`.

Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hsub]`. Conclude with `(i1 k).sub (hint Ψ hΨ k)`. Use function extensionality and compare the values at `k`. Simplify using `only [thetaInt, hsub, Pi.zero_apply]`.

Rewrite using `[integral_sub (i1 k) (hint Ψ hΨ k)]`. Simplify using `only [e]`. Rewrite using `[(tr k).2, sub_self]`. Consider the case `zero`. Conclude with `⟨fun k => by simp only [hzero]; exact integrableOn_zero, by funext k; simp [thetaInt, hzero]⟩`.

Consider the case `add x y _ _ hx hy`. Use `⟨fun k => by simp only [hadd]; exact (hx.1 k).add (hy.1 k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Use `integral_add (hx.1 k) (hy.1 k)` as an intermediate fact. Establish `ex` using `congrFun hx.2 k`.

Establish `ey` using `congrFun hy.2 k`. Simplify using `only [thetaInt, Pi.zero_apply] at ex ey`. Simplify using `only [thetaInt, hadd, Pi.zero_apply, this, ex, ey, add_zero]`. Consider the case `smul c x _ hx`. Use `⟨fun k => by simp only [hsmul]; exact (hx.1 k).const_mul c, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Establish `ex` using `congrFun hx.2 k`. Simplify using `only [thetaInt, Pi.zero_apply] at ex`. Simplify using `only [thetaInt, hsmul, Pi.zero_apply, integral_const_mul, ex, mul_zero]`.
-/
theorem theta_integral_finite_relation_eq_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  intro _ D ψ θ hψ hθ M X A B χ χ' ω hω hsig ν 𝓕 hF
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hpd : ∀ τ, (gramAt D M τ).PosDef := fun τ => GlobalTheory.Core.CoefGram.posDef_of_hasSignature _ (hsig τ)
  have hcc : GlobalTheory.Unf.CoCpt M := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D M).2 hpd
  have hth : ∀ Φ ∈ algF ψ θ false A B, IsThetaFunO ψ M X Φ := fun Φ hΦ =>
    GlobalTheory.SquareComm.ThetaLeft.isThetaFunO_of_mem_algF hψ hθ A B hΦ
  have hleft := GlobalTheory.SquareComm.ThetaLeft.main D ψ θ hθ M X A B χ χ' ω hω
  have hsub : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ - Ψ) = thetaKO ω g k Φ - thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_sub]
  have hadd : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ + Ψ) = thetaKO ω g k Φ + thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_add]
  have hsmul : ∀ g k (c : ℂ) (Φ : WO M X → ℂ), thetaKO ω g k (c • Φ) = c * thetaKO ω g k Φ := by
    intros; simp [thetaKO, map_smul]
  have hzero : ∀ g k, thetaKO ω g k (0 : WO M X → ℂ) = 0 := by
    intros; simp [thetaKO]
  have hint : ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
    intro Φ hΦ h
    exact (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D M hcc _
      ⟨fun γ hγ g => hleft Φ hΦ γ hγ g h, (hω'.om_cont Φ (hth Φ hΦ) 0).comp (Continuous.prodMk_left h)⟩).2.2
      ⟨ν, 𝓕, hF.1, hF.2⟩
  intro Φ hΦ
  suffices key : (∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν) ∧ thetaInt ω ν 𝓕 Φ = 0 from key.2
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, -, Ψ, hΨ, rfl⟩ := hx
    have e : ∀ g k, thetaKO ω g k (ω (u, 1) Ψ) = thetaKO ω (g * u) k Ψ := fun g k => by
      unfold thetaKO
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    have tr := fun k => integral_rightTranslate hF (f := fun g => thetaKO ω g k Ψ)
      (fun γ hγ g => hleft Ψ hΨ γ hγ g k) u
    have i1 : ∀ k, IntegrableOn (fun g => thetaKO ω g k (ω (u, 1) Ψ)) 𝓕 ν := fun k => by
      simp only [e]; exact (tr k).1.2 (hint Ψ hΨ k)
    refine ⟨fun k => ?_, ?_⟩
    · simp only [hsub]; exact (i1 k).sub (hint Ψ hΨ k)
    · funext k
      simp only [thetaInt, hsub, Pi.zero_apply]
      rw [integral_sub (i1 k) (hint Ψ hΨ k)]
      simp only [e]
      rw [(tr k).2, sub_self]
  | zero =>
    exact ⟨fun k => by simp only [hzero]; exact integrableOn_zero, by funext k; simp [thetaInt, hzero]⟩
  | add x y _ _ hx hy =>
    refine ⟨fun k => by simp only [hadd]; exact (hx.1 k).add (hy.1 k), ?_⟩
    funext k
    have := integral_add (hx.1 k) (hy.1 k)
    have ex := congrFun hx.2 k
    have ey := congrFun hy.2 k
    simp only [thetaInt, Pi.zero_apply] at ex ey
    simp only [thetaInt, hadd, Pi.zero_apply, this, ex, ey, add_zero]
  | smul c x _ hx =>
    refine ⟨fun k => by simp only [hsmul]; exact (hx.1 k).const_mul c, ?_⟩
    funext k
    have ex := congrFun hx.2 k
    simp only [thetaInt, Pi.zero_apply] at ex
    simp only [thetaInt, hsmul, Pi.zero_apply, integral_const_mul, ex, mul_zero]
end GlobalTheory.ThetaFinRelDef
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | exact _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | (intros; apply _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  first | exact @_root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | exact _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | (intros; apply _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero <;> assumption)
end
