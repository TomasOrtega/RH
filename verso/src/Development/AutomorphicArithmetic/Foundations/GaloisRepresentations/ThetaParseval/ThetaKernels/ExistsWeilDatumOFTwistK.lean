import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ χS χT νS νT om ho hνS hνT rS rT`. Establish `hcm` using `hB.cm`. Establish `hun` using `hB.unram`. Take `⟨a, aval, arat, acont⟩` from `exists_muF (σ := σ) hcm hun hS.2 νT⁻¹ (heckeF_inv hνT) (fun t => by rw [MonoidHom.inv_apply, triv_of_resEtaF rT, inv_one])`. Take `⟨b, bval, brat, bcont⟩` from `exists_muF (σ := σ) hcm hun hT.2 νS hνS (triv_of_resEtaF rS)`.

Set `om' : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)` to `{ toFun := fun p => ((a p.1 * b p.2 : Circle) : ℂ) • om p map_one' := by simp map_mul' := fun p q => by`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul, smul_mul_smul_comm, Circle.coe_mul]`. Use `congr 1`. Use `ring }`. Establish `happ : ∀ p f, om' p f = ((a p.1 * b p.2 : Circle) : ℂ) • om p f` using `fun p f => rfl`.

Establish `hval : ∀ g h x y, IsRootF σ JS g x → IsRootF σ JT h y → ((a g * b h : Circle) : ℂ) = (((νT x)⁻¹ * νS y : Circle) : ℂ)`. Introduce `g h x y hx hy`. Rewrite using `[aval g x hx, bval h y hy, MonoidHom.inv_apply]`. Use `⟨om', ⟨ho.std, heckeF_mul ho.hecS hνS, heckeF_mul ho.hecT hνT, resEtaF_mul ho.resS rS, resEtaF_mul ho.resT rT, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `p f hf`.

Rewrite using `[happ]`. Conclude with `thetaOF_smul _ (ho.om_pres p f hf)`. Introduce `g h w₀ f hf`. Rewrite using `[happ, happ, heisOF_smul, ho.om_heis g h w₀ f hf]`. Introduce `γ hγ γ' hγ' f hf`.

Rewrite using `[happ]`. Express the relevant statement in the definitionally equal form `((a γ * b γ' : Circle) : ℂ) * om (γ, γ') f 0 = f 0`. Rewrite using `[arat γ hγ, brat γ' hγ', mul_one, Circle.coe_one, one_mul]`. Conclude with `ho.om_aut γ hγ γ' hγ' f hf`. Introduce `f hf w`.

Conclude with `(continuous_subtype_val.comp ((acont.comp continuous_fst).mul (bcont.comp continuous_snd))).mul (ho.om_cont f hf w)`. Introduce `μ 𝓕 hμ h𝓕 p f hf`. Rewrite using `[← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]`. Use `lintegral_congr fun w => ?_` and prove the remaining obligations. Establish `hn : ‖om' p f w‖ = ‖om p f w‖`.

Rewrite using `[happ, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]`. Rewrite using `[← ofReal_norm, ← ofReal_norm, hn]`. Introduce `e he g h hg hh x y hx hy`. Take `⟨r, hr, H⟩` from `ho.om_split e he g h hg hh x y hx hy`. Use `⟨r, hr, fun ℓ hℓ f hf => ?_⟩` and prove the remaining obligations.

Rewrite using `[happ, map_smul, H ℓ hℓ f hf, hval g h x y (root_of_detAt hS.2 he g hg x hx) (root_of_detAt hT.2 he h hh y hy)]`. Simplify using `only [splitFacOF, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_weilDatumOF_twist_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ χS χT νS νT om ho hνS hνT rS rT
  have hcm := hB.cm
  have hun := hB.unram
  obtain ⟨a, aval, arat, acont⟩ := exists_muF (σ := σ) hcm hun hS.2 νT⁻¹ (heckeF_inv hνT)
    (fun t => by rw [MonoidHom.inv_apply, triv_of_resEtaF rT, inv_one])
  obtain ⟨b, bval, brat, bcont⟩ := exists_muF (σ := σ) hcm hun hT.2 νS hνS (triv_of_resEtaF rS)
  let om' : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ) :=
    { toFun := fun p => ((a p.1 * b p.2 : Circle) : ℂ) • om p
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, smul_mul_smul_comm, Circle.coe_mul]
        congr 1
        ring }
  have happ : ∀ p f, om' p f = ((a p.1 * b p.2 : Circle) : ℂ) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsRootF σ JS g x → IsRootF σ JT h y →
      ((a g * b h : Circle) : ℂ) = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval g x hx, bval h y hy, MonoidHom.inv_apply]
  refine ⟨om', ⟨ho.std, heckeF_mul ho.hecS hνS, heckeF_mul ho.hecT hνT, resEtaF_mul ho.resS rS,
    resEtaF_mul ho.resT rT, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p f hf
    rw [happ]
    exact thetaOF_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisOF_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ]
    change ((a γ * b γ' : Circle) : ℂ) * om (γ, γ') f 0 = f 0
    rw [arat γ hγ, brat γ' hγ', mul_one, Circle.coe_one, one_mul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact (continuous_subtype_val.comp ((acont.comp continuous_fst).mul (bcont.comp continuous_snd))).mul
      (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (root_of_detAt hS.2 he g hg x hx) (root_of_detAt hT.2 he h hh y hy)]
    simp only [splitFacOF, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
end GlobalTheory.WeilTwistF
end
end
