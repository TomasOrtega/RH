import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHypothesesOfAttached
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.FrobDualOfTripleAttN

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.TripleGal
/- English proof (translation)
Distinguish the cases in `hl : v ∈ placesOver D.host.E (D.ntw.l i)`. Conclude with `⟨GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump D bkP i s hJ v hl, GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump D bkP i s hT (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s hA) hJ v hl⟩`. Distinguish the cases in `hS : v ∈ Spl (X := D.ntw) i`. Break down `hS.1 with hg | hp` into its components or cases. Take `⟨k, hk⟩` from `Set.mem_iUnion.1 hg`.

Conclude with `GlobalTheory.T.noInv_at_type_primes D i s h2 k (fun e => hl (e ▸ hk)) v hk`. Conclude with `GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s hA) v (Finset.mem_coe.1 hp)`. Take `⟨ι, hι⟩` from `_root_.GlobalTheory.TripleGal.pure_of_tripleAtt_n D bkP i s hA`. Conclude with `_root_.GlobalTheory.PurityInvariants.noInv_of_pure_n D i s ι hι v hl hS`.
-/
theorem noInv_all_places_alt (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hT : ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) (h2 : ValuationStabilityAtRing D.ntw i s)
    (hA : _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) (hJ : NoJump bkP i s) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  by_cases hl : v ∈ placesOver D.host.E (D.ntw.l i)
  · exact ⟨GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump D bkP i s hJ v hl, GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump D bkP i s hT (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s hA) hJ v hl⟩
  by_cases hS : v ∈ Spl (X := D.ntw) i
  · rcases hS.1 with hg | hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hg
      exact GlobalTheory.T.noInv_at_type_primes D i s h2 k (fun e => hl (e ▸ hk)) v hk
    · exact GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s hA) v (Finset.mem_coe.1 hp)
  · obtain ⟨ι, hι⟩ := _root_.GlobalTheory.TripleGal.pure_of_tripleAtt_n D bkP i s hA
    exact _root_.GlobalTheory.PurityInvariants.noInv_of_pure_n D i s ι hι v hl hS
/- English proof (translation)
Introduce `D bkP hF hT h2 hA`. Establish `hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s` using `fun i hi s => by`. Take `⟨ι, J, h, h'⟩` from `_root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)`. Conclude with `GlobalTheory.T.noHodgeJump_of_goodJumpMultiset D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h'`. Use `⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩` and prove the remaining obligations.

Take `⟨ι, J, h, h'⟩` from `_root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)`. Conclude with `GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount D bkP i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGa …`. Conclude with `GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt_n D bkP i s (hA i hi s))`. Conclude with `GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly D i s (h2 i hi s) (GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense D hF i s (_root_.GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt_n D bkP i s (hA i hi s)))`.
-/
theorem adm1_adm8_selfDual_noJump_of_tripleAttN : ∀ (D : D7) (bkP : BlochKatoReduction.BK D), GlobalTheory.TypeLeaf.FrobDense D → (∀ i, D.ntw.NonzeroIndexPlace i → (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI))) → BlochKatoReduction.adm2 D → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) → BlochKatoReduction.adm1 bkP ∧ BlochKatoReduction.adm8 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump bkP i s := by
  intro D bkP hF hT h2 hA
  have hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s := fun i hi s => by
    obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact GlobalTheory.T.noHodgeJump_of_goodJumpMultiset D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h'
  refine ⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩
  · obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount D bkP i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s))
      (_root_.GlobalTheory.TripleGal.noInv_all_places_alt D bkP i s (hT i hi) (h2 i hi s) (hA i hi s) (hJ i hi s))
      (GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h')
  · exact GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt_n D bkP i s (hA i hi s))
  · exact GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly D i s (h2 i hi s) (GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense D hF i s (_root_.GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt_n D bkP i s (hA i hi s)))
end GlobalTheory.TripleGal
end
