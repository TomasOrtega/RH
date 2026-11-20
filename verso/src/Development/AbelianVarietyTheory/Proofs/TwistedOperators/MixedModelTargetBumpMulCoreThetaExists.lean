import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordsConjHermitianAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.MixAdj

/- English proof (translation)
Set `e : Mx D m n ≃ₜ Mx D m n` to `{ toFun := fun x => c • x, invFun := fun x => c' • x, left_inv := fun x => by simp only [smul_smul, hc, one_smul], right_inv := fun x => by simp only [smul_smul, hc', one_smul], continuous_toFun := continuous_const_smul c, continuous_invFun := continuous_const_smul c' }`. Establish `hinf : ∀ u : Mx D m n, u.map (infPart D) = 0 → (c • u).map (infPart D) = 0` using `fun u hu => by`. Use extensionality with `i j`. Use `congrArg (fun M : Matrix _ _ _ => M i j) hu` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at this`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, this, mul_zero, Matrix.zero_apply]`. Establish `hfin : ∀ u : Mx D m n, u.map (finPart D) = 0 → (c • u).map (finPart D) = 0` using `fun u hu => by`. Use extensionality with `i j`. Use `congrArg (fun M : Matrix _ _ _ => M i j) hu` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at this`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, this, mul_zero, Matrix.zero_apply]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Complex.continuous_conj.comp (hβ.cont.comp (continuous_const_smul c))`. Conclude with `(hβ.supp.comp_homeomorph e).comp_left (map_zero (starRingEnd ℂ))`. Take `⟨U, hU, hper⟩` from `hβ.level`.

Use `⟨U.comap (DistribMulAction.toAddMonoidHom (Mx D m n) c), hU.preimage (continuous_const_smul c), ?_⟩` and prove the remaining obligations. Introduce `u hu hu0 x`. Simplify using `only [smul_add]`. Rewrite using `[hper (c • u) hu (hinf u hu0)]`. Introduce `k l hl hl0 w`.

Establish `h0 : ContDiff ℝ ∞ fun t => β (c • w + ((DistribMulAction.toAddMonoidHom (Mx D m n) c).comp l) t)` using `hβ.smooth k ((DistribMulAction.toAddMonoidHom (Mx D m n) c).comp l) ((continuous_const_smul c).comp hl) (fun t => hfin _ (hl0 t)) (c • w)`. Establish `h` using `(Complex.conjCLE.contDiff (n := ∞)).comp h0`. Use `h using 2 with t` and compare the differences between its conclusion and the goal. Simplify using `[smul_add]`.
-/
theorem isBump_conj_smul {D : D7} {m n : ℕ} (c c' : AE D) (hc : c' * c = 1) (hc' : c * c' = 1) {β : Mx D m n → ℂ} (hβ : IsBump β) :
    IsBump (fun x : Mx D m n => starRingEnd ℂ (β (c • x))) := by
  let e : Mx D m n ≃ₜ Mx D m n :=
    { toFun := fun x => c • x, invFun := fun x => c' • x,
      left_inv := fun x => by simp only [smul_smul, hc, one_smul],
      right_inv := fun x => by simp only [smul_smul, hc', one_smul],
      continuous_toFun := continuous_const_smul c, continuous_invFun := continuous_const_smul c' }
  have hinf : ∀ u : Mx D m n, u.map (infPart D) = 0 → (c • u).map (infPart D) = 0 := fun u hu => by
    ext i j
    have := congrArg (fun M : Matrix _ _ _ => M i j) hu
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, this, mul_zero, Matrix.zero_apply]
  have hfin : ∀ u : Mx D m n, u.map (finPart D) = 0 → (c • u).map (finPart D) = 0 := fun u hu => by
    ext i j
    have := congrArg (fun M : Matrix _ _ _ => M i j) hu
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, this, mul_zero, Matrix.zero_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_conj.comp (hβ.cont.comp (continuous_const_smul c))
  · exact (hβ.supp.comp_homeomorph e).comp_left (map_zero (starRingEnd ℂ))
  · obtain ⟨U, hU, hper⟩ := hβ.level
    refine ⟨U.comap (DistribMulAction.toAddMonoidHom (Mx D m n) c), hU.preimage (continuous_const_smul c), ?_⟩
    intro u hu hu0 x
    simp only [smul_add]
    rw [hper (c • u) hu (hinf u hu0)]
  · intro k l hl hl0 w
    have h0 : ContDiff ℝ ∞ fun t => β (c • w + ((DistribMulAction.toAddMonoidHom (Mx D m n) c).comp l) t) :=
      hβ.smooth k ((DistribMulAction.toAddMonoidHom (Mx D m n) c).comp l)
        ((continuous_const_smul c).comp hl) (fun t => hfin _ (hl0 t)) (c • w)
    have h := (Complex.conjCLE.contDiff (n := ∞)).comp h0
    convert h using 2 with t
    simp [smul_add]

/- English proof (translation)
Introduce `D ψ hψ S T T₀ ρ d v β g hβ hg`. Take `⟨μ', 𝓕', hcov, -, -, -, hsw⟩` from `GlobalTheory.MixSwap.mixS_cj_dagger D ψ hψ S T T₀ ρ d v.μ v.𝓕 v.covol`. Establish `hadj` using `fun X Y : HSp D => (GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ X Y).2.2.1`. Establish `hx` using `GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D`. Establish `hc : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1` using `by rw [← map_mul, inv_mul_cancel₀ hx, map_one]`.

Establish `hc' : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel₀ hx, map_one]`. Establish `hβ'` using `isBump_conj_smul (incA D D.host.xi0) (incA D D.host.xi0⁻¹) hc hc' hβ`. Establish `hg' : IsThetaFunO ψ T₀ S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T₀ S) g)` using `(hadj S T₀ g).2 hg`. Take `⟨Φ', hΦ', hmix⟩` from `GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core D ψ hψ T T₀ S ρ d ⟨μ', 𝓕', hcov⟩ _ _ hβ' hg'`. Use `⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T) Φ', (hadj T S Φ').2 hΦ', fun y => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hsw (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T) Φ') y`. Rewrite `h1` using `[GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj _ _ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger T S)]`. Establish `h2` using `hmix (incA D D.host.xi0⁻¹ • y)`. Simplify using `only at h2`. Rewrite `h1` using `[h2, smul_smul, hc', one_smul]`.

Use function extensionality and compare the values at `z`. Establish `h3` using `congrFun h1 (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T₀ z)`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger, map_mul, Complex.conj_conj] at h3`. Establish `h4` using `congrArg (starRingEnd ℂ) h3`. Simplify using `only [map_mul, Complex.conj_conj] at h4`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, ← h4]`.
-/
theorem mixT_bump_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank) (β : Mx D S.rank ρ → ℂ) (g : WO S T₀ → ℂ), IsBump β → IsThetaFunO ψ S T₀ g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ y, d.mixT S ψ v.μ v.𝓕 Φ y = β y • g := by
  intro D ψ hψ S T T₀ ρ d v β g hβ hg
  obtain ⟨μ', 𝓕', hcov, -, -, -, hsw⟩ := GlobalTheory.MixSwap.mixS_cj_dagger D ψ hψ S T T₀ ρ d v.μ v.𝓕 v.covol
  have hadj := fun X Y : HSp D => (GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ X Y).2.2.1
  have hx := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hc : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  have hc' : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  have hβ' := isBump_conj_smul (incA D D.host.xi0) (incA D D.host.xi0⁻¹) hc hc' hβ
  have hg' : IsThetaFunO ψ T₀ S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T₀ S) g) := (hadj S T₀ g).2 hg
  obtain ⟨Φ', hΦ', hmix⟩ := GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core D ψ hψ T T₀ S ρ d ⟨μ', 𝓕', hcov⟩ _ _ hβ' hg'
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T) Φ', (hadj T S Φ').2 hΦ', fun y => ?_⟩
  have h1 := hsw (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T) Φ') y
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj _ _ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger T S)] at h1
  have h2 := hmix (incA D D.host.xi0⁻¹ • y)
  simp only at h2
  rw [h2, smul_smul, hc', one_smul] at h1
  funext z
  have h3 := congrFun h1 (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T₀ z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger, map_mul,
    Complex.conj_conj] at h3
  have h4 := congrArg (starRingEnd ℂ) h3
  simp only [map_mul, Complex.conj_conj] at h4
  rw [Pi.smul_apply, smul_eq_mul, ← h4]

end GlobalTheory.MixAdj
