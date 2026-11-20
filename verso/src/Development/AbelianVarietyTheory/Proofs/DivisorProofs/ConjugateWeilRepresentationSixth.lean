import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Rebase

open GlobalTheory.ConjLiftUnique

/- English proof (translation)
Establish `hk : ∀ τ, ∃ k ∈ Formalism.REAL.Kset (M.ε τ), B τ = onb M τ * k` using `fun τ => by`. Take `⟨k, hk, -, k2, -⟩` from `exists_kset (M.fr_unit τ) (M.fr_gram τ) (hO τ) (hB τ)`. Use `⟨k, hk, k2.trans ?_⟩` and prove the remaining obligations. Unfold `onb`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), Matrix.mul_one]`.

Use `choose k hk hBk using hk`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ P, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f P = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (s P) := by`. Take `rfl : B = fun τ => onb M τ * k τ` from `funext hBk`. Establish `h` using `GlobalTheory.FockSubst.pureTensorO_subst D ψ θ V W S M BV f k (fun τ b a => if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) hω.std hθ hV hf hk fun _ _ _ => rfl`. Generalize the expression as in `MvPolynomial.aeval (R := ℂ) (S₁ := MvPolynomial (FVar D W.rank V.rank) ℂ) _ = s at h`.

Conclude with `⟨s.toLinearMap, h⟩`. Establish `e0 : ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io.compr₂ s x w) = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w)` using `fun x w => (hs _).symm`. Use `⟨io.compr₂ s, ⟨fun u hu x w => by rw [e0, e0, hio.1 u hu], fun τ k hk v u hu w => by rw [e0, e0, hio.2.1 τ k hk v u hu], ?_⟩, fun x w => (e0 x w).symm⟩` and prove the remaining obligations. Establish `t1` using `GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M) B hf`. Set `F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W` to `io.compr₂ ((pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f).codRestrict _ t1)`.

Establish `f1 : ∀ x w, (F x w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w)` using `fun _ _ => rfl`. Use `clear_value F`. Establish `hF : Eqv θ ω F` using `⟨fun u hu x w => by rw [f1, f1, hio.1 u hu], fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩`. Take `⟨v₀, w₀, n1, n2, e⟩` from `hio.2.2`. Take `⟨v₁, l, n3, hl, e1⟩` from `exists_move hω hθ kV kW hV h1 h2 hF hf hv hB hO Δ n1 ((f1 _ w₀).trans (congrArg _ e))`.

Establish `l0 : l ≠ 0` using `fun h => by simp [h] at hl`. Use `⟨v₁, l⁻¹ • w₀, n3, by rw [norm_smul, norm_inv, hl, n2, inv_one, one_mul], hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, e0, ← f1, e1, smul_smul, inv_mul_cancel₀ l0, one_smul]`.
-/
theorem rebase_gen {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) 1) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (cart M τ)) f)
    {BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    {p : D.what₂.Tau → ℕ} (hB : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (B τ) (p τ))
    (hO : ∀ τ, IsONBasis (gramAt D W τ) (cart M τ) (onb M τ) (p τ))
    (hinj : Function.Injective (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f)) {Δ : PolF D W.rank V.rank}
    {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank}
    (hio : IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f) Δ io) :
    ∃ io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
      IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f) Δ io' ∧
      ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io' x w) := by
  classical
  have hk : ∀ τ, ∃ k ∈ Formalism.REAL.Kset (M.ε τ), B τ = onb M τ * k := fun τ => by
    obtain ⟨k, hk, -, k2, -⟩ := exists_kset (M.fr_unit τ) (M.fr_gram τ) (hO τ) (hB τ)
    refine ⟨k, hk, k2.trans ?_⟩
    unfold onb
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), Matrix.mul_one]
  choose k hk hBk using hk
  obtain ⟨s, hs⟩ : ∃ s : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ P,
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f P =
        pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (s P) := by
    obtain rfl : B = fun τ => onb M τ * k τ := funext hBk
    have h := GlobalTheory.FockSubst.pureTensorO_subst D ψ θ V W S M BV f k
      (fun τ b a => if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) hω.std hθ hV hf hk fun _ _ _ => rfl
    generalize MvPolynomial.aeval (R := ℂ) (S₁ := MvPolynomial (FVar D W.rank V.rank) ℂ) _ = s at h
    exact ⟨s.toLinearMap, h⟩
  have e0 : ∀ x w, pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) f (io.compr₂ s x w) =
      pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun x w => (hs _).symm
  refine ⟨io.compr₂ s, ⟨fun u hu x w => by rw [e0, e0, hio.1 u hu],
    fun τ k hk v u hu w => by rw [e0, e0, hio.2.1 τ k hk v u hu], ?_⟩, fun x w => (e0 x w).symm⟩
  have t1 := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M) B hf
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W :=
    io.compr₂ ((pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f).codRestrict _ t1)
  have f1 : ∀ x w, (F x w).1 = pureTensorO ψ θ V W (fun _ => 1) (cart M) BV B f (io x w) := fun _ _ => rfl
  clear_value F
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, l, n3, hl, e1⟩ := exists_move hω hθ kV kW hV h1 h2 hF hf hv hB hO Δ n1 ((f1 _ w₀).trans (congrArg _ e))
  have l0 : l ≠ 0 := fun h => by simp [h] at hl
  refine ⟨v₁, l⁻¹ • w₀, n3, by rw [norm_smul, norm_inv, hl, n2, inv_one, one_mul], hinj ?_⟩
  rw [map_smul, map_smul, e0, ← f1, e1, smul_smul, inv_mul_cancel₀ l0, one_smul]

end GlobalTheory.GalOne.Rebase

end
