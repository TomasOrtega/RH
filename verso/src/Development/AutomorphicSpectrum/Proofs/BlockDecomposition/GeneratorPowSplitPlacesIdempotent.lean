import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowersDiagonalAtTBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (MOk SplitPlaceGeneratorPowers SplitPowersOfIdempotents)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SplitPlacePowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem not_mem_T_of_mem_S₀ (d : LocData E n) (hm : MOk d) {w : Pl E} (hS : w ∈ d.S₀) : w ∉ d.T := fun hT =>
  (hm.T w hT).1 (hm.S w hS).1

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gU_S (d : LocData E n) (hd : d.Ok) (hm : MOk d) {w : Pl E} (hS : w ∈ d.S₀) (k : ℕ) :
    d.gU (k + 1) w = fun u : UL n w => PositivityTheory.Rg.BcB.F.MS.gpow (d.e w) k u.1 := by
  have hT := not_mem_T_of_mem_S₀ d hm hS
  obtain ⟨hsp, -, hlv⟩ := hm.S w hS
  obtain ⟨-, -, -, -, -, hf⟩ := hd.K' w hS
  have hU : UL n w = ⊤ := if_pos hsp
  have hKU : d.KU w = (d.K' w).subgroupOf (UL n w) := by
    unfold LocData.KU
    rw [if_neg hT, if_pos hS]
  have hg : d.g₀ w = fun y => d.e w y.1 := by
    unfold LocData.g₀
    rw [if_neg hT, if_pos hS]
  unfold LocData.gU
  rw [hKU, hg]
  induction k with
  | zero =>
    funext y
    have hidx : ((d.K' w).subgroupOf (UL n w)).relIndex (KL n w) ≠ 0 :=
      GlobalTheory.CompanionTheory.FmPowP.relIndex_ne_of_open hlv.1 (GlobalTheory.LocFinU.isCompact_KL n w)
    exact GlobalTheory.CompanionTheory.MatchPow.conv_unit hlv.2.1 hidx (f := fun y : UL n w => d.e w y.1) (fun k hk x => by
      have h2 : (k : GLw n w) ∈ d.K' w := Subgroup.mem_subgroupOf.1 hk
      simpa using hf.2.2.2 1 (Subgroup.one_mem _) _ h2 x.1) y
  | succ k ih =>
    show lconv _ (lpow _ _ (k + 1)) = _
    rw [ih]
    funext u
    have h := congrFun (GlobalTheory.CompanionTheory.CtMulSplit.lconv_eq_gconv hU (fun y : UL n w => d.e w y.1)
      (fun v : UL n w => PositivityTheory.Rg.BcB.F.MS.gpow (d.e w) k (v : GLw n w))) u.1
    rw [GlobalTheory.CompanionTheory.CtMulSplit.toSub_val hU] at h
    simp only [GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU] at h
    exact h

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem generator_pow_split_places : SplitPlaceGeneratorPowers := fun _ _ _ _ _ d hd hm _ hS N u => congrFun (gU_S d hd hm hS N) u

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem generator_pow_split_places_of_idempotent : SplitPowersOfIdempotents := fun _ => generator_pow_split_places

end GlobalTheory.CompanionTheory.SplitPlacePowers

end
