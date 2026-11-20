import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.BcMatch

/- English proof (translation)
Introduce `L _ _ _ n K K' _ _ f e W₀ W W' _ _ _ _ _ _ ρ₀ ρ ρ' hb hm`. Take `⟨ι, _, _, b₀, b₁, hb⟩` from `hb`. Take `⟨κ, _, _, c₀, c', hc⟩` from `hm`. Use `set P : Matrix ι κ K := b₀.toMatrix c₀ with hP`. Use `set Q : Matrix κ ι K := c₀.toMatrix b₀ with hQ`.

Establish `hPQ : P * Q = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip b₀ c₀`. Establish `hQP : Q * P = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip c₀ b₀`. Establish `hPQf : P.map f * Q.map f = 1` using `by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ f.map_zero f.map_one]`. Establish `hQPf : Q.map f * P.map f = 1` using `by rw [← Matrix.map_mul, hQP, Matrix.map_one _ f.map_zero f.map_one]`. Set `std` to `Pi.basisFun K' κ`.

Set `E : (κ → K') ≃ₗ[K'] W` to `LinearEquiv.ofLinear (Matrix.toLin std b₁ (P.map f)) (Matrix.toLin b₁ std (Q.map f)) (by rw [← Matrix.toLin_mul, hPQf, Matrix.toLin_one]) (by rw [← Matrix.toLin_mul, hQPf, Matrix.toLin_one])`. Set `d : Module.Basis κ K' W` to `std.map E`. Establish `hd1 : b₁.toMatrix d = P.map f`. Use extensionality with `i j`. Rewrite using `[Module.Basis.toMatrix_apply]`.

Establish `: d j = ∑ k, (P.map f) k j • b₁ k` using `by show E (std j) = _`. Conclude with `Matrix.toLin_self _ _ _ _`. Rewrite using `[this, Module.Basis.repr_sum_self]`. Establish `hd2 : d.toMatrix b₁ = Q.map f`. Use extensionality with `j i`.

Rewrite using `[Module.Basis.toMatrix_apply]`. Simplify using `[d, E, std, Matrix.toLin_self, Pi.single_apply]`. Use `⟨κ, inferInstance, inferInstance, d, c', fun γ => ?_⟩` and prove the remaining obligations. Rewrite using `[hc γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d b₁ d b₁ (ρ γ), hd1, hd2, hb γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c₀ b₀ c₀ b₀ (ρ₀ γ), ← hP, ← hQ]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]`.

Both sides reduce to the same expression.
-/
theorem bcmatch_main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  intro L _ _ _ n K K' _ _ f e W₀ W W' _ _ _ _ _ _ ρ₀ ρ ρ' hb hm
  obtain ⟨ι, _, _, b₀, b₁, hb⟩ := hb
  obtain ⟨κ, _, _, c₀, c', hc⟩ := hm
  set P : Matrix ι κ K := b₀.toMatrix c₀ with hP
  set Q : Matrix κ ι K := c₀.toMatrix b₀ with hQ
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₀ c₀
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c₀ b₀
  have hPQf : P.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ f.map_zero f.map_one]
  have hQPf : Q.map f * P.map f = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ f.map_zero f.map_one]
  let std := Pi.basisFun K' κ
  let E : (κ → K') ≃ₗ[K'] W := LinearEquiv.ofLinear (Matrix.toLin std b₁ (P.map f)) (Matrix.toLin b₁ std (Q.map f))
    (by rw [← Matrix.toLin_mul, hPQf, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, hQPf, Matrix.toLin_one])
  let d : Module.Basis κ K' W := std.map E
  have hd1 : b₁.toMatrix d = P.map f := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    have : d j = ∑ k, (P.map f) k j • b₁ k := by
      show E (std j) = _
      exact Matrix.toLin_self _ _ _ _
    rw [this, Module.Basis.repr_sum_self]
  have hd2 : d.toMatrix b₁ = Q.map f := by
    ext j i
    rw [Module.Basis.toMatrix_apply]
    simp [d, E, std, Matrix.toLin_self, Pi.single_apply]
  refine ⟨κ, inferInstance, inferInstance, d, c', fun γ => ?_⟩
  rw [hc γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d b₁ d b₁ (ρ γ), hd1, hd2, hb γ,
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c₀ b₀ c₀ b₀ (ρ₀ γ), ← hP, ← hQ]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  rfl

end GlobalTheory.BcMatch
