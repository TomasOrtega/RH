import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DownCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private tf algClo cyc_cont cyc_conj from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DownCsd
open UpperTheory.GalN.V UpperTheory.V.Af
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base
attribute [local instance] tf
open UpperTheory.V.Z.Win in
/- English proof (translation)
Introduce `hP K L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol l _ ι n hn r σ hσ hr hpair hirr hI hF hKp haut`. Take `⟨P, hPr⟩` from `hpair`. Take `⟨j, hj⟩` from `hσ`. Use `haveI : IsAlgClosure K Ω := algClo K Ω`. Use `haveI : IsAlgClosure L Ω := algClo L Ω`.

Use `haveI : IsAlgClosure (maximalRealSubfield K) Ω := algClo (maximalRealSubfield K) Ω`. Set `c : G (maximalRealSubfield K) Ω` to `AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by`. Apply `j.injective` to reduce the goal to its premises. Use `(hj _).trans ?_` and prove the remaining obligations. Conclude with `(mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))`.

Establish `hc : IsConjEl c` using `⟨j, hj⟩`. Establish `hpc : IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P` using `fun s s' hs => hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)`. Establish `halg : IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ)))`. Use `(_root_.UpperTheory.V.Af.algOfCyc_s hP (maximalRealSubfield K) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`.

Use `⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]`. Establish `hN` using `_root_.UpperTheory.GalN.V.csdN'_alt hP.toClassicalTheorems hn haut`. Establish `hpol : Sol.Pol ι r` using `⟨maximalRealSubfield K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, c, P, halg, fun a b ha hb => by rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, cyc_conj l ha hb], hc, hpc⟩`. It suffices to establish `h0 : AutCsd0 ι r from _root_.UpperTheory.GalN.V.mkCsd'_alt h0 fun hc' => _root_.UpperTheory.V.Z.Win.Dn.down'_alt L hP hsol hn hc' hirr hpol h0.c0 hF hI hKp (hN.2 (hc'.comp (continuous_restrictScalarsHom K L Ω)))`.

Use `_root_.UpperTheory.GalN.V.csdOf0_alt hP (maximalRealSubfield K) K Ω inferInstance l ι n hn r c P hc ?_ hpc` and prove the remaining obligations. Use `(_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hP (maximalRealSubfield K) K L Ω hsol ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ (Or.inr inferInstance) l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg (fun a b ha hb => ?_) ⟨c, P, hc, ?_⟩).2 …` and prove the remaining obligations. Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Rewrite using `[MonoidHom.zpow_apply, MonoidHom.zpow_apply, cyc_conj l ha hb]`. Conclude with `hpc`.
-/
theorem UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt := by
  intro hP K L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol l _ ι n hn r σ hσ hr hpair hirr hI hF hKp haut
  obtain ⟨P, hPr⟩ := hpair
  obtain ⟨j, hj⟩ := hσ
  haveI : IsAlgClosure K Ω := algClo K Ω
  haveI : IsAlgClosure L Ω := algClo L Ω
  haveI : IsAlgClosure (maximalRealSubfield K) Ω := algClo (maximalRealSubfield K) Ω
  let c : G (maximalRealSubfield K) Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))
  have hc : IsConjEl c := ⟨j, hj⟩
  have hpc : IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P := fun s s' hs =>
    hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have halg : IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP (maximalRealSubfield K) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt hP.toClassicalTheorems hn haut
  have hpol : Sol.Pol ι r := ⟨maximalRealSubfield K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, c, P, halg, fun a b ha hb => by rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, cyc_conj l ha hb], hc, hpc⟩
  suffices h0 : AutCsd0 ι r from _root_.UpperTheory.GalN.V.mkCsd'_alt h0 fun hc' => _root_.UpperTheory.V.Z.Win.Dn.down'_alt L hP hsol hn hc' hirr hpol h0.c0 hF hI hKp
    (hN.2 (hc'.comp (continuous_restrictScalarsHom K L Ω)))
  refine _root_.UpperTheory.GalN.V.csdOf0_alt hP (maximalRealSubfield K) K Ω inferInstance l ι n hn r c P hc ?_ hpc
  refine (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hP (maximalRealSubfield K) K L Ω hsol ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ (Or.inr inferInstance)
    l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg (fun a b ha hb => ?_) ⟨c, P, hc, ?_⟩).2
    ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP L Ω l ι n _).2.2 haut)
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, cyc_conj l ha hb]
  · exact hpc
end
