import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartParabolicCentralizerIffBlockDiagonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexLeviSubgroupUnipotentConjIntegrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegralStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

/- English proof (translation)
Introduce `E _ _ n w f _ k hk x`. Unfold `GlobalTheory.LeviDesc.cavg`. Rewrite using `[← GlobalTheory.TwOrbConj.avg_left (fun k' : GlobalTheory.LFun.KGL w n => f ((k' : GLw n w)⁻¹ * x * k')) ⟨k, hk⟩]`. Use `congr 1`. Use function extensionality and compare the values at `k'`.

Use `congr 1`. Simplify using `only [Subgroup.coe_mul, _root_.mul_inv_rev]`. Use `group`.
-/
theorem cavg_conj_KGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (k⁻¹ * x * k) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f x := by
  intro E _ _ n w f _ k hk x
  unfold GlobalTheory.LeviDesc.cavg
  rw [← GlobalTheory.TwOrbConj.avg_left (fun k' : GlobalTheory.LFun.KGL w n => f ((k' : GLw n w)⁻¹ * x * k')) ⟨k, hk⟩]
  congr 1
  funext k'
  congr 1
  simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
  group

/- English proof (translation)
Introduce `E _ _ _ n a ha w f hf m hsep hγ`. Take `⟨s, π, u, hs, hu, hπs, hinj, hker, hKs, hKπ, hKu⟩` from `GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent E n a (n - a) (Nat.add_sub_cancel' ha) w`. Establish `hγs : (⟨blk (Nat.add_sub_cancel' ha) w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) = s m` using `Subtype.ext (hs m).symm`. Establish `hfin` using `GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m hsep hγ`. Establish `hcent` using `GlobalTheory.T.mem_twisted_centralizer_block_iff E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ`.

Establish `hcpt` using `GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ`. Rewrite `hfin`, `hcent`, `hcpt`, the goal using `[hγs]`. Establish `hrhs : GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f = fun m' => hint (intMat a (n - a) w) (fun X => (fun p : GlobalTheory.LeviDesc.parP a n w => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (p : GLw n w)) ((u X)⁻¹ * s m' * u X))`. Use function extensionality and compare the values at `m'`. Unfold `GlobalTheory.LeviDesc.orbN`.

Use `congrArg (hint (intMat a (n - a) w)) (funext fun X => ?_)` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]`. Rewrite using `[hrhs]`. Use `GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding _ _ _ s π u hπs hinj hker _ _ (intMat a (n - a) w) hKs hKπ hKu m ?_ ?_ ?_ ?_ _ ?_ hfin` and prove the remaining obligations. Introduce `p`.

Rewrite using `[hcent]`. Simplify using `only [Subtype.ext_iff, hs]`. Introduce `p`. Rewrite using `[hcpt]`. Simplify using `only [Subtype.ext_iff, hs]`.

Introduce `q`. Conclude with `GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart E a (n - a) w m q`. Introduce `X`. Take `⟨U, hU, hUi, hUk⟩` from `GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral E n a (n - a) (Nat.add_sub_cancel' ha) w (Multiplicative.toAdd X)`. Use `⟨U, hU, hUi, fun k hk => ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]`. Conclude with `hUk k hk`. Introduce `k hk x`. Simplify using `only [Subgroup.coe_mul, InvMemClass.coe_inv]`.

Conclude with `cavg_conj_KGL E n w f hf _ (Subgroup.mem_subgroupOf.1 hk) _`.
-/
theorem twistedOrbitalIntegral_parabolic_unfolding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  intro E _ _ _ n a ha w f hf m hsep hγ
  obtain ⟨s, π, u, hs, hu, hπs, hinj, hker, hKs, hKπ, hKu⟩ := GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent E n a (n - a) (Nat.add_sub_cancel' ha) w
  have hγs : (⟨blk (Nat.add_sub_cancel' ha) w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) = s m := Subtype.ext (hs m).symm
  have hfin := GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m hsep hγ
  have hcent := GlobalTheory.T.mem_twisted_centralizer_block_iff E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  have hcpt := GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  rw [hγs] at hfin hcent hcpt ⊢
  have hrhs : GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f = fun m' => hint (intMat a (n - a) w) (fun X =>
      (fun p : GlobalTheory.LeviDesc.parP a n w => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (p : GLw n w)) ((u X)⁻¹ * s m' * u X)) := by
    funext m'
    unfold GlobalTheory.LeviDesc.orbN
    refine congrArg (hint (intMat a (n - a) w)) (funext fun X => ?_)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
  rw [hrhs]
  refine GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding _ _ _ s π u hπs hinj hker _ _ (intMat a (n - a) w) hKs hKπ hKu m ?_ ?_ ?_ ?_ _ ?_ hfin
  · intro p
    rw [hcent]
    simp only [Subtype.ext_iff, hs]
  · intro p
    rw [hcpt]
    simp only [Subtype.ext_iff, hs]
  · intro q
    exact GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart E a (n - a) w m q
  · intro X
    obtain ⟨U, hU, hUi, hUk⟩ := GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral E n a (n - a) (Nat.add_sub_cancel' ha) w (Multiplicative.toAdd X)
    refine ⟨U, hU, hUi, fun k hk => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
    exact hUk k hk
  · intro k hk x
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact cavg_conj_KGL E n w f hf _ (Subgroup.mem_subgroupOf.1 hk) _

end GlobalTheory.LeviDesc
