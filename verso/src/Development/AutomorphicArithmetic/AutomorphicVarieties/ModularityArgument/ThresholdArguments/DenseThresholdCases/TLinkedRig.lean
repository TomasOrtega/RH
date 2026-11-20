import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TRigPtOf

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
/- English proof (translation)
Introduce `hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed`. Establish `hP : _root_.UpperTheory.V.Af.Hypotheses'` using `hH.toClassicalTheorems`. Establish `hN` using `hP.litN`. Establish `hA : GlobalTheory.Published.GlobalArtinReciprocity` using `hN.aut.art`. Establish `hC : Pa.CohP` using `⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩`.

Establish `hLoc : W.LocCFTAll` using `W.locCFT hA hC`. Establish `hB0 : W.ProModularRingExists` using `W.b0Ex (W.phiAll hC)`. Take `⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩` from `hseed`. Establish `hker : η.ker = Base.galOf ℚ K Ω`. Rewrite using `[← hD.η_ker]`.

Use extensionality with `s`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]`. Conclude with `Iff.rfl` after adjusting the coercions. Use `haveI := hD.imag`. Take `⟨κ, hκ⟩` from `_root_.UpperTheory.V.Sd.twist_of_printed_results hP K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc`.

Take `⟨hk3, hk2⟩` from `Pr.kaOf (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hP) Ω l ι c N e ψ η σ g₁ B M H L Φ k`. Take `⟨ka, hk2, -⟩` from `hk2 K hker κ hκ`. Take `⟨c₁, hle, hL, hv3, hv2, f, hf⟩` from `Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1`. Use `haveI := Pr.coefIs l c₁`. Take `⟨R₂⟩` from `Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl) hok hbig hle hf hk2 hv2`.

Take `⟨R₃⟩` from `Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl) hok hbig hle hf hk3 hv3`. Conclude with `⟨_root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hL hk3, ka, hk2, _root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hL hk2⟩`.
-/
theorem UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.LinkedRigAlt := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok hbig hseed
  have hP : _root_.UpperTheory.V.Af.Hypotheses' := hH.toClassicalTheorems
  have hN := hP.litN
  have hA : GlobalTheory.Published.GlobalArtinReciprocity := hN.aut.art
  have hC : Pa.CohP :=
    ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hLoc : W.LocCFTAll := W.locCFT hA hC
  have hB0 : W.ProModularRingExists := W.b0Ex (W.phiAll hC)
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  have hker : η.ker = Base.galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := _root_.UpperTheory.V.Sd.twist_of_printed_results hP K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := Pr.kaOf (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hP) Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, -⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  haveI := Pr.coefIs l c₁
  obtain ⟨R₂⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl)
    hok hbig hle hf hk2 hv2
  obtain ⟨R₃⟩ := Pr.cRealEx hA hLoc W.levEx hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3
  exact ⟨_root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hL hk3,
    ka, hk2, _root_.UpperTheory.V.Th.rigPtOf_alt hA hAd Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hL hk2⟩
end
