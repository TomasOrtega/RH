import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

/- English proof (translation)
Introduce `D ψ θ hθ ε M X A B χS χT ω eS eT hW hexp Pi rf rl p hp`. Establish `hW' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε)` using `hW`. Establish `hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B` using `fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩`. Establish `e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h)`. Introduce `h`.

Use `show ω ((ofSgn ε M) 1, h) = ω (1, h)`. Rewrite using `[map_one]`. Establish `hL` using `fun f τ (hf : IsFinF ψ θ ε A B f) => GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (ω.toSgn ε) f τ (eS τ) (eT τ) hθ hW' (hexp τ).1 (hexp τ).2 hf`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf τ Y hY P`.

Use `hp.eql τ Y hY _ (hmem f P hf) _ (hmem f _ hf) ?_` and prove the remaining obligations. Introduce `z`. Establish `h` using `(hL f τ hf).2 Y hY P z`. Simplify using `only [e1] at h`. Establish `e2 : actT ε A B eS τ Y P = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + ((eS τ : ℂ) * Y.trace) • P`.

Rewrite using `[actT, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]`. Rewrite using `[e2]`. Conclude with `h`. Introduce `f hf P hP`. Establish `hle : coinv ε A B eT ≤ LinearMap.ker (p ∘ₗ fockF ψ θ ε A B f)`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, Z, hZ, P₀, rfl⟩`. Establish `hZ' : Z ∈ lieAt (sgn ε M) τ` using `by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ`. Use `show p (fockF ψ θ ε A B f (actS ε A B eT τ Z P₀)) = 0`. Use `hp.invl τ Z hZ _ (hmem f P₀ hf) _ (hmem f _ hf) ?_` and prove the remaining obligations.

Introduce `z`. Establish `h` using `(hL f τ hf).1 Z hZ' P₀ z`. Establish `e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1)`. Introduce `t`. Use `show ω ((ofSgn ε M) (oneP θ (sgn ε M) τ Z t), 1) = _`.

Unfold `oneP`. Rewrite using `[GlobalTheory.SgnIdent.atTau_sgn θ hθ]`. Simplify using `only [e] at h`. Establish `e3 : actS ε A B eT τ Z P₀ = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P₀ + (-((eT τ : ℂ) * Z.trace)) • P₀`. Rewrite using `[actS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul, sub_eq_add_neg]`.

Rewrite using `[e3]`. Conclude with `h`. Conclude with `hle hP`. Introduce `h hh f hf`. Use `⟨ω (1, h) f, ?_, fun P => ?_⟩` and prove the remaining obligations.

Take `⟨hth, hvac⟩` from `hf`. Establish `e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z (ω (1, h) f) = ω (1, h) (Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z f)`. Introduce `τ z`. Rewrite using `[← e1, GlobalTheory.OrientedHeis.om_dRho hW' hθ 1 h τ z hth, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ X hh, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ (sgn ε M) (inv_mem (one_mem _)), Matrix.one_mul, Matrix.mul_one]`. Use `⟨?_, fun τ z => ?_⟩` and prove the remaining obligations.

Rewrite using `[← e1]`. Conclude with `hW'.om_pres _ f hth`. Establish `h0` using `hvac τ z`. Unfold `annih at h0 ⊢`. Rewrite using `[e, e, ← map_smul, ← map_add, h0, map_zero]`.

Establish `ht` using `GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χS χT (ω.toSgn ε) hW' θ hθ 1 (one_mem _) h hh (frSgn ε A).cart B.cart A.onb B.onb f P hf.1`. Rewrite `ht` using `[e1]`. Rewrite using `[← hp.eqf h hh _ (hmem f P hf)]`. Conclude with `congrArg p ht`.
-/
theorem oriented_maps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  intro D ψ θ hθ ε M X A B χS χT ω eS eT hW hexp Pi rf rl p hp
  have hW' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := by
    intro h
    show ω ((ofSgn ε M) 1, h) = ω (1, h)
    rw [map_one]
  have hL := fun f τ (hf : IsFinF ψ θ ε A B f) =>
    GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (ω.toSgn ε) f τ (eS τ) (eT τ) hθ hW'
      (hexp τ).1 (hexp τ).2 hf
  refine ⟨?_, ?_, ?_⟩
  · intro f hf τ Y hY P
    refine hp.eql τ Y hY _ (hmem f P hf) _ (hmem f _ hf) ?_
    intro z
    have h := (hL f τ hf).2 Y hY P z
    simp only [e1] at h
    have e2 : actT ε A B eS τ Y P =
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + ((eS τ : ℂ) * Y.trace) • P := by
      rw [actT, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [e2]
    exact h
  · intro f hf P hP
    have hle : coinv ε A B eT ≤ LinearMap.ker (p ∘ₗ fockF ψ θ ε A B f) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨τ, Z, hZ, P₀, rfl⟩
      have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
      show p (fockF ψ θ ε A B f (actS ε A B eT τ Z P₀)) = 0
      refine hp.invl τ Z hZ _ (hmem f P₀ hf) _ (hmem f _ hf) ?_
      intro z
      have h := (hL f τ hf).1 Z hZ' P₀ z
      have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
        intro t
        show ω ((ofSgn ε M) (oneP θ (sgn ε M) τ Z t), 1) = _
        unfold oneP
        rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
      simp only [e] at h
      have e3 : actS ε A B eT τ Z P₀ =
          GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P₀ +
            (-((eT τ : ℂ) * Z.trace)) • P₀ := by
        rw [actS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul, sub_eq_add_neg]
      rw [e3]
      exact h
    exact hle hP
  · intro h hh f hf
    refine ⟨ω (1, h) f, ?_, fun P => ?_⟩
    · obtain ⟨hth, hvac⟩ := hf
      have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z (ω (1, h) f) =
          ω (1, h) (Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z f) := by
        intro τ z
        rw [← e1, GlobalTheory.OrientedHeis.om_dRho hW' hθ 1 h τ z hth, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ X hh,
          GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ (sgn ε M) (inv_mem (one_mem _)), Matrix.one_mul, Matrix.mul_one]
      refine ⟨?_, fun τ z => ?_⟩
      · rw [← e1]; exact hW'.om_pres _ f hth
      · have h0 := hvac τ z
        unfold annih at h0 ⊢
        rw [e, e, ← map_smul, ← map_add, h0, map_zero]
    · have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χS χT (ω.toSgn ε) hW' θ hθ 1 (one_mem _) h hh
        (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
      rw [e1] at ht
      rw [← hp.eqf h hh _ (hmem f P hf)]
      exact congrArg p ht

end GlobalTheory.RealQuot
