import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

/- English proof (translation)
Introduce `hI hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw B hB`. Establish `hF` using `GlobalTheory.automorphicFormsFiniteGL`. Establish `hA` using `hI.hk`. Take `⟨κ, m, hκ, hu, hcs⟩` from `GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw`. Take `⟨art, hart, hμ⟩` from `(GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt GlobalTheory.globalArtinReciprocity_holds).1 E Ω`.

Establish `hκp : GlobalTheory.HeckeGal.IsAlgPos κ m` using `GlobalTheory.HeckeGal.isAlgPos_of_isAlg hκ`. Take `⟨μ, ⟨hμc, hL⟩, -⟩` from `hμ l ι κ m hκp`. Establish `htc : Continuous (UpperTheory.V.Af.tw r μ)` using `UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc`. Establish `hW : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ)` using `⟨htc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩`. Establish `hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w))`.

Rewrite `hB`, the goal using `[CG.hasSat_mk]`. Conclude with `GlobalTheory.SphGal.hasSatGL_twist E a π κ w B hu hB`. Establish `hcl : ClauseAt .dR (π.twist κ) ι (UpperTheory.V.Af.tw r μ) w` using `hC E Ω l ι a ha (π.twist κ) _ hcs (UpperTheory.V.Af.tw r μ) hW w hw _ hB'`. Use `show ClauseAt .dR π ι r w`. Introduce `P AI hT A hAw O _ _ _ Bw hj`.

Take `⟨hdR', hJ'⟩` from `hcl P AI hT A hAw O Bw hj`. Establish `hμic : Continuous (μ⁻¹)` using `hμc.inv`. Establish `hch` using `GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hA E Ω l P AI hT ι art hart κ⁻¹ (-m) μ⁻¹ (GlobalTheory.GalChar.isAlgPos_inv hκp) hμic hL.inv w A hAw O Bw hj`. Establish `key` using `GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a ((UpperTheory.V.Af.tw r μ).comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype) (μ⁻¹.comp (Dec (F := E) A).subtype) (fun g => by`. Express the relevant statement in the definitionally equal form `((r g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) = (((μ g.1)⁻¹ : (Qbar l)ˣ) : Qbar l) • ((UpperTheory.V.Af.tw r μ g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))`.

Rewrite using `[UpperTheory.V.Af.tw_val, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul])`. Use `⟨key.1 hdR' hch.1, fun τ LL' τ' hτ J hJ => ?_⟩` and prove the remaining obligations. Use `set m0 := m (ι.toRingHom.comp τ) with hm0`. Establish `e : expo κ (ι.toRingHom.comp τ) = m0` using `(GlobalTheory.CuspRep.InfType.expo_of_infType E κ).1 m hκ _`. Establish `hinf : (CG.mk (π.twist κ)).infChar (ι.toRingHom.comp τ) = ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (· + (m0 : ℂ))`.

Rewrite using `[← e]`. Conclude with `((GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) _).twist κ).infChar_eq`. Establish `h1` using `hJ' τ LL' τ' hτ (J.map (· - m0)) (by`. Rewrite using `[hinf, Multiset.map_map, Multiset.map_map]`. Establish `e1 : ((CG.mk π).infChar (ι.toRingHom.comp τ)).map ((fun z : ℂ => ((a : ℂ) - 1) / 2 - z) ∘ (· + (m0 : ℂ))) = (((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z : ℂ => ((a : ℂ) - 1) / 2 - z)).map (· - (m0 : ℂ))`.

Rewrite using `[Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, ← hJ, Multiset.map_map]`.

Use `Multiset.map_congr rfl fun n _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Use `push_cast`. Use the proof step `ring)`. Establish `h2` using `key.2.2.2 τ _ _ h1 (hch.2.2.2 τ LL' τ' hτ)`.

Establish `e2 : (J.map (· - m0)).map (· + -((-m) (ι.toRingHom.comp τ))) = J`. Rewrite using `[Multiset.map_map]`. Use `conv_rhs => rw [← Multiset.map_id J]`. Use `Multiset.map_congr rfl fun n _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Pi.neg_apply, neg_neg, id, hm0]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[e2]`. Conclude with `h2`.
-/
theorem holdsS_good_dR_of_csd : Inputs → SphericalLevelCondition .csd .dR → SphericalLevelCondition .good .dR := by
  intro hI hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw B hB
  have hF := GlobalTheory.automorphicFormsFiniteGL
  have hA := hI.hk
  obtain ⟨κ, m, hκ, hu, hcs⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  have hκp : GlobalTheory.HeckeGal.IsAlgPos κ m := GlobalTheory.HeckeGal.isAlgPos_of_isAlg hκ
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι κ m hκp
  have htc : Continuous (UpperTheory.V.Af.tw r μ) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a r μ hr.1 hμc
  have hW : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨htc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hL⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B hu hB
  have hcl : ClauseAt .dR (π.twist κ) ι (UpperTheory.V.Af.tw r μ) w :=
    hC E Ω l ι a ha (π.twist κ) _ hcs (UpperTheory.V.Af.tw r μ) hW w hw _ hB'
  show ClauseAt .dR π ι r w
  intro P AI hT A hAw O _ _ _ Bw hj
  obtain ⟨hdR', hJ'⟩ := hcl P AI hT A hAw O Bw hj
  have hμic : Continuous (μ⁻¹) := hμc.inv
  have hch := GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 hA E Ω l P AI hT ι art hart κ⁻¹ (-m) μ⁻¹
    (GlobalTheory.GalChar.isAlgPos_inv hκp) hμic hL.inv w A hAw O Bw hj
  have key := GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a
    ((UpperTheory.V.Af.tw r μ).comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)
    (μ⁻¹.comp (Dec (F := E) A).subtype) (fun g => by
      change ((r g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) =
        (((μ g.1)⁻¹ : (Qbar l)ˣ) : Qbar l) • ((UpperTheory.V.Af.tw r μ g.1 : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))
      rw [UpperTheory.V.Af.tw_val, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul])
  refine ⟨key.1 hdR' hch.1, fun τ LL' τ' hτ J hJ => ?_⟩
  set m0 := m (ι.toRingHom.comp τ) with hm0
  have e : expo κ (ι.toRingHom.comp τ) = m0 := (GlobalTheory.CuspRep.InfType.expo_of_infType E κ).1 m hκ _
  have hinf : (CG.mk (π.twist κ)).infChar (ι.toRingHom.comp τ) =
      ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (· + (m0 : ℂ)) := by
    rw [← e]
    exact ((GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) _).twist κ).infChar_eq
  have h1 := hJ' τ LL' τ' hτ (J.map (· - m0)) (by
    rw [hinf, Multiset.map_map, Multiset.map_map]
    have e1 : ((CG.mk π).infChar (ι.toRingHom.comp τ)).map ((fun z : ℂ => ((a : ℂ) - 1) / 2 - z) ∘ (· + (m0 : ℂ))) =
        (((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z : ℂ => ((a : ℂ) - 1) / 2 - z)).map (· - (m0 : ℂ)) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]
      ring
    rw [e1, ← hJ, Multiset.map_map]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring)
  have h2 := key.2.2.2 τ _ _ h1 (hch.2.2.2 τ LL' τ' hτ)
  have e2 : (J.map (· - m0)).map (· + -((-m) (ι.toRingHom.comp τ))) = J := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id J]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply, Pi.neg_apply, neg_neg, id, hm0]
    ring
  rw [e2] at h2
  exact h2

end GlobalTheory.RoadU
