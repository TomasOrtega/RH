import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TwoAtCharZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.SchurSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensSimple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSchur

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Set `E : Subrepresentation (twist (ρ.comp f) χ) ≃o Subrepresentation ρ` to `{ toFun := fun S => ⟨S.toSubmodule, fun h v hv => by`. Take `⟨g, rfl⟩` from `hf h`. Establish `h1` using `S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)`. Rewrite `h1` using `[twist_apply, smul_smul, Units.inv_mul, one_smul]`.

Conclude with `h1⟩`. Use `invFun := fun S => ⟨S.toSubmodule, fun g v hv => by`. Rewrite using `[twist_apply]`. Conclude with `S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (f g) hv)⟩`. Use `left_inv := fun _ => rfl`.

Use `right_inv := fun _ => rfl`. Use the proof step `map_rel_iff' := Iff.rfl }`. Conclude with `E.isSimpleOrder_iff.2 hi`. Introduce `T hT`. Use `hs T fun h v => ?_` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `hf h`. Establish `h1` using `hT g v`. Rewrite `h1` using `[twist_apply, twist_apply, map_smul]`. Conclude with `smul_right_injective V (χ g).ne_zero h1`.
-/
private theorem irr_twist {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (f : G →* H) (hf : Function.Surjective f) (χ : G →* ℂˣ) (hi : ρ.IsIrreducible) (hs : Schur ρ) :
    (twist (ρ.comp f) χ).IsIrreducible ∧ Schur (twist (ρ.comp f) χ) := by
  constructor
  · let E : Subrepresentation (twist (ρ.comp f) χ) ≃o Subrepresentation ρ :=
      { toFun := fun S => ⟨S.toSubmodule, fun h v hv => by
          obtain ⟨g, rfl⟩ := hf h
          have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rw [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1
          exact h1⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          rw [twist_apply]
          exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (f g) hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact E.isSimpleOrder_iff.2 hi
  · intro T hT
    refine hs T fun h v => ?_
    obtain ⟨g, rfl⟩ := hf h
    have h1 := hT g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact smul_right_injective V (χ g).ne_zero h1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `K _ _ w σ₁ σ₂ u₁ u₂`. Establish `hT` using `tensSimple σ₁.ρ σ₂.ρ σ₁.irred (schurSm 2 w σ₁.ρ σ₁.smooth σ₁.irred) σ₂.irred`. Establish `hsurj : Function.Surjective (lev₂ w)`. Introduce `g`. Use `⟨⟨leviEmb _ _ (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2) g), leviEmb_mem_parab _ _ _⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).symm (leviProj _ _ _) = g`. Rewrite using `[leviProj_leviEmb, MulEquiv.symm_apply_apply]`. Establish `hR` using `irr_twist _ (lev₂ w) hsurj (dl w) hT.1 (hT.2 (schurSm 2 w σ₂.ρ σ₂.smooth σ₂.irred))`. Use `haveI : CharZero (w.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective`. Establish `hI : (smInd (PW w) (rhoW w σ₁ σ₂)).IsIrreducible` using `UpperTheory.Lit.Mix.twoAt_charZero (w.adicCompletion K) 2 2 _ _ σ₁.ρ σ₂.ρ σ₁.smooth σ₁.irred u₁ σ₂.smooth σ₂.irred u₂`.

Use `⟨⟨_, ⟨GlobalTheory.SplitFlip.isCompact_KO, GlobalTheory.SplitFlip.isOpen_KO⟩, fun g => ?_⟩, fun N hN => ?_, hR.1, hR.2, hI, schurSm (2 + 2) w _ (isSmooth_smoothRep _) hI⟩` and prove the remaining obligations. Take `⟨p, k, hk, e⟩` from `GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two (stdSum (rfl : 2 + 2 = 2 + 2))) g`. Conclude with `⟨p, p.2, k, hk, e⟩`. Take `⟨U, h1, -, h2⟩` from `GlobalTheory.LocalThetaGL.compact_open_basis (k := w.adicCompletion K) (Fin (2 + 2)) N hN`. Conclude with `⟨U, h1, h2⟩`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.locDat :
    ∀ {K : Type} [Field K] [NumberField K] (w : Pl K) (σ₁ σ₂ : SmIrr (Gw 2 w)), IsUnitarisable σ₁.ρ → IsUnitarisable σ₂.ρ → LocOk (PW w) (rhoW w σ₁ σ₂) := by
  intro K _ _ w σ₁ σ₂ u₁ u₂
  have hT := tensSimple σ₁.ρ σ₂.ρ σ₁.irred (schurSm 2 w σ₁.ρ σ₁.smooth σ₁.irred) σ₂.irred
  have hsurj : Function.Surjective (lev₂ w) := by
    intro g
    refine ⟨⟨leviEmb _ _ (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2) g), leviEmb_mem_parab _ _ _⟩, ?_⟩
    change (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).symm (leviProj _ _ _) = g
    rw [leviProj_leviEmb, MulEquiv.symm_apply_apply]
  have hR := irr_twist _ (lev₂ w) hsurj (dl w) hT.1 (hT.2 (schurSm 2 w σ₂.ρ σ₂.smooth σ₂.irred))
  haveI : CharZero (w.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  have hI : (smInd (PW w) (rhoW w σ₁ σ₂)).IsIrreducible :=
    UpperTheory.Lit.Mix.twoAt_charZero (w.adicCompletion K) 2 2 _ _ σ₁.ρ σ₂.ρ σ₁.smooth σ₁.irred u₁ σ₂.smooth σ₂.irred u₂
  refine ⟨⟨_, ⟨GlobalTheory.SplitFlip.isCompact_KO, GlobalTheory.SplitFlip.isOpen_KO⟩, fun g => ?_⟩, fun N hN => ?_, hR.1, hR.2, hI,
    schurSm (2 + 2) w _ (isSmooth_smoothRep _) hI⟩
  · obtain ⟨p, k, hk, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two (stdSum (rfl : 2 + 2 = 2 + 2))) g
    exact ⟨p, p.2, k, hk, e⟩
  · obtain ⟨U, h1, -, h2⟩ := GlobalTheory.LocalThetaGL.compact_open_basis (k := w.adicCompletion K) (Fin (2 + 2)) N hN
    exact ⟨U, h1, h2⟩
