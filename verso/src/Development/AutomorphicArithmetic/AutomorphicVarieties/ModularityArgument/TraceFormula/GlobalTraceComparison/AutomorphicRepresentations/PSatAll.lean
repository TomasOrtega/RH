import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Use `GlobalTheory.EulerTwU.gl_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.EulerTwU.pc_thF]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Rewrite using `[pLoc_locGL, pLoc_locGL]`.

Establish `h' : GlobalTheory.EulerTw.cPl E v ≠ GlobalTheory.EulerTw.cPl E w` using `fun e => h (by rw [← GlobalTheory.EulerTwU.cPl_cPl v, e, GlobalTheory.EulerTwU.cPl_cPl])`. Rewrite using `[pLoc_locGL_of_ne h', pLoc_locGL_of_ne h]`. Conclude with `(congrArg (thetaGL n (RingHom.id _)) (map_one _)).trans (map_one _)`.
-/
private theorem twist_loc (w : Pl E) (g : GLw n (GlobalTheory.EulerTw.cPl E w)) :
    thF E n (locGL E n (GlobalTheory.EulerTw.cPl E w) g) = locGL E n w (thetaGL n (RingHom.id _)
      (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g)) := by
  refine GlobalTheory.EulerTwU.gl_ext fun v => ?_
  rw [GlobalTheory.EulerTwU.pc_thF]
  by_cases h : v = w
  · subst h
    rw [pLoc_locGL, pLoc_locGL]
  · have h' : GlobalTheory.EulerTw.cPl E v ≠ GlobalTheory.EulerTw.cPl E w := fun e =>
      h (by rw [← GlobalTheory.EulerTwU.cPl_cPl v, e, GlobalTheory.EulerTwU.cPl_cPl])
    rw [pLoc_locGL_of_ne h', pLoc_locGL_of_ne h]
    exact (congrArg (thetaGL n (RingHom.id _)) (map_one _)).trans (map_one _)

/- English proof (translation)
Establish `e : thetaGL n (RingHom.id _) (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) = PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹`. Rewrite using `[GlobalTheory.CompanionTheory.ConjSat.flipGL_eq]`. Both sides reduce to the same expression. Rewrite using `[← e, ← twist_loc w g, GlobalTheory.EulerTwU.thF_thF]`. Both sides reduce to the same expression.
-/
private theorem twist_conj (w : Pl E) (g : GLw n (GlobalTheory.ThetaSatake.cw w)) :
    thF E n (locGL E n w (PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹)) =
      locGL E n (GlobalTheory.ThetaSatake.cw w) g := by
  have e : thetaGL n (RingHom.id _) (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) =
      PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹ := by
    rw [GlobalTheory.CompanionTheory.ConjSat.flipGL_eq]
    rfl
  rw [← e, ← twist_loc w g, GlobalTheory.EulerTwU.thF_thF]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi in
/- English proof (translation)
Introduce `E _ _ _ n π w B y hy h0`. Establish `hne : (⟨y, hy⟩ : π.V) ≠ 0` using `fun e => h0 (congrArg Subtype.val e)`. Use `⟨fun hB hf => ?_, fun hB hf => ?_⟩` and prove the remaining obligations. Rewrite `hB` using `[CG.hasSat_mk]`. Establish `hx : (⟨y, hy⟩ : π.V) ∈ fixed (π.locRep w) (KGL w n)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)`.

Conclude with `(hB.2 _ hx hne).map (ρ' := rw' n w false) π.V.subtype (fun _ _ => rfl) h0`. Rewrite `hB` using `[CG.hasSat_mk]`. Set `σ : Representation ℂ (GLw n w) π.V` to `π.finPart.comp (jw n w true)`. Set `k` to `PhiU n (w.adicCompletion E)`. Set `T : π.V ≃ₗ[ℂ] π.V` to `LinearEquiv.ofLinear (σ k⁻¹) (σ k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)`.

Establish `hs : HasSatGL w σ (B.map (·⁻¹))` using `GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w) (conjLoc_spec _ w).2.2 (GlobalTheory.ThetaSatake.absNorm_cw w).symm T (fun g x => ?_) hB`. Establish `hx : (⟨y, hy⟩ : π.V) ∈ fixed σ (KGL w n)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)`. Conclude with `(hs.2 _ hx hne).map (ρ' := rw' n w true) π.V.subtype (fun _ _ => rfl) h0`. Establish `e : π.locRep (GlobalTheory.ThetaSatake.cw w) g = σ (k * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * k⁻¹)`. Express the relevant statement in the definitionally equal form `π.finPart (locGL E n (GlobalTheory.ThetaSatake.cw w) g) = π.finPart (thF E n (locGL E n w _))`.

Rewrite using `[twist_conj]`. Express the relevant statement in the definitionally equal form `σ (GlobalTheory.CompanionTheory.ConjSat.flipGL w g) (σ k⁻¹ x) = σ k⁻¹ (π.locRep (GlobalTheory.ThetaSatake.cw w) g x)`. Rewrite using `[e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Use `group`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.satAll_pf :
    SatAll := by
  intro E _ _ _ n π w B y hy h0
  have hne : (⟨y, hy⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine ⟨fun hB hf => ?_, fun hB hf => ?_⟩
  · rw [CG.hasSat_mk] at hB
    have hx : (⟨y, hy⟩ : π.V) ∈ fixed (π.locRep w) (KGL w n) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
    exact (hB.2 _ hx hne).map (ρ' := rw' n w false) π.V.subtype (fun _ _ => rfl) h0
  · rw [CG.hasSat_mk] at hB
    let σ : Representation ℂ (GLw n w) π.V := π.finPart.comp (jw n w true)
    let k := PhiU n (w.adicCompletion E)
    let T : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear (σ k⁻¹) (σ k)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    have hs : HasSatGL w σ (B.map (·⁻¹)) :=
      GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w) (conjLoc_spec _ w).2.2
        (GlobalTheory.ThetaSatake.absNorm_cw w).symm T (fun g x => ?_) hB
    · have hx : (⟨y, hy⟩ : π.V) ∈ fixed σ (KGL w n) :=
        GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
      exact (hs.2 _ hx hne).map (ρ' := rw' n w true) π.V.subtype (fun _ _ => rfl) h0
    · have e : π.locRep (GlobalTheory.ThetaSatake.cw w) g = σ (k * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * k⁻¹) := by
        change π.finPart (locGL E n (GlobalTheory.ThetaSatake.cw w) g) = π.finPart (thF E n (locGL E n w _))
        rw [twist_conj]
      change σ (GlobalTheory.CompanionTheory.ConjSat.flipGL w g) (σ k⁻¹ x) = σ k⁻¹ (π.locRep (GlobalTheory.ThetaSatake.cw w) g x)
      rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group

end
