import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeterssonFormProportionalClassSumAllLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalThetaCorrespondenceInertPlaceOfHoweStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHeckeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.TwoSidedInert

/- English proof (translation)
Establish `h : dualLab ∘ dualLab = id`. Use function extensionality and compare the values at `d`. Simplify using `[dualLab, List.map_reverse]`. Unfold `dualC`. Rewrite using `[← Finsupp.mapDomain_comp, h, Finsupp.mapDomain_id]`.
-/
theorem dualC_dualC (c : List ℤ →₀ ℂ) : dualC (dualC c) = c := by

  have h : dualLab ∘ dualLab = id := by
    funext d
    simp [dualLab, List.map_reverse]
  unfold dualC
  rw [← Finsupp.mapDomain_comp, h, Finsupp.mapDomain_id]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact fun c => ⟨fun _ => c, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩`. Consider the case `succ n ih`. Introduce `c`. Take `⟨c₁, hc₁⟩` from `h n c`.

Take `⟨cs, hcs, hQ⟩` from `ih c₁`. Use `⟨fun k => if k ≤ n then cs k else c, by simp, fun k hk => ?_⟩` and prove the remaining obligations. Break down `Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl` into its components or cases. Simplify using `only [if_pos hk.le, if_pos (Nat.succ_le_of_lt hk)]`. Conclude with `hQ k hk`.

Simplify `hc₁` using `[hcs]`.
-/
theorem exists_down {C : Type} (Q : ℕ → C → C → Prop) (h : ∀ k c', ∃ c, Q k c c') (n : ℕ) :
    ∀ c, ∃ cs : ℕ → C, cs n = c ∧ ∀ k, k < n → Q k (cs k) (cs (k + 1)) := by
  induction n with
  | zero => exact fun c => ⟨fun _ => c, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    intro c
    obtain ⟨c₁, hc₁⟩ := h n c
    obtain ⟨cs, hcs, hQ⟩ := ih c₁

    refine ⟨fun k => if k ≤ n then cs k else c, by simp, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · simp only [if_pos hk.le, if_pos (Nat.succ_le_of_lt hk)]
      exact hQ k hk
    · simpa [hcs] using hc₁

/- English proof (translation)
Use `choose f hf using h`. Conclude with `⟨fun k => Nat.rec (motive := fun _ => C) c0 (fun k c => f k c) k, rfl, fun k => hf k _⟩`.
-/
theorem exists_up {C : Type} (Q : ℕ → C → C → Prop) (h : ∀ k c, ∃ c', Q k c c') (c0 : C) :
    ∃ cs : ℕ → C, cs 0 = c0 ∧ ∀ k, Q k (cs k) (cs (k + 1)) := by
  choose f hf using h
  exact ⟨fun k => Nat.rec (motive := fun _ => C) c0 (fun k c => f k c) k, rfl, fun k => hf k _⟩

/- English proof (translation)
Introduce `hHowe D G _ _ Pl0 T A Ks _ _ _ R F hLift hCore hSchur t P hGood hconj hFix`. Establish `hY : ∀ k, k + 1 < D.R.m → SphCorr R.ψ (R.ωY t k) P` using `fun k hk => GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ _ _ _ _ (R.ωY t k) P (hCore.chain.ωY t k hk) hconj (hFix.1 k hk)`. Establish `hX : SphCorr R.ψ (R.ωX t) P` using `GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ _ _ _ _ (R.ωX t) P (hCore.chain.ωX t) hconj hFix.2.1`. Establish `hP : ∀ i, SphCorr R.ψ (R.ωP i t) P` using `fun i => GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ _ _ _ _ (R.ωP i t) P (hCore.thP.ωP i t) hconj (hFix.2.2 i)`. Use `⟨⟨fun cX => ?_, fun c0 => ?_⟩, fun i => ⟨fun cV => ?_, fun cW => ?_⟩⟩` and prove the remaining obligations.

Take `⟨cm, hcm⟩` from `hX.2.1 (dualC cX)`. Take `⟨cs, hcs, hQ⟩` from `exists_down (fun k c c' => k + 1 < D.R.m → Match R.ψ (R.ωY t k) P c (dualC c')) (fun k c' => by`. Distinguish the cases in `hk : k + 1 < D.R.m`. Conclude with `((hY k hk).2.1 (dualC c')).imp fun c hc _ => hc`. Conclude with `⟨c', fun h => absurd h hk⟩) (D.R.m - 1) cm`.

Use `⟨cs 0, GlobalTheory.T.matchE_of_chainStep_matches R F hLift hCore hSchur t P hGood hFix cX cs ?_ fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[hcs]`. Conclude with `hcm`. Conclude with `hQ k (by omega) hk`. Take `⟨cs, hcs0, hQ⟩` from `exists_up (fun k c c' => k + 1 < D.R.m → Match R.ψ (R.ωY t k) P c (dualC c')) (fun k c => by`.

Distinguish the cases in `hk : k + 1 < D.R.m`. Take `⟨cT, hcT⟩` from `(hY k hk).2.2 c`. Conclude with `⟨dualC cT, fun _ => by rw [dualC_dualC]; exact hcT⟩`. Conclude with `⟨c, fun h => absurd h hk⟩) c0`. Take `⟨cT, hcT⟩` from `hX.2.2 (cs (D.R.m - 1))`.

Use `⟨dualC cT, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcs0]`. Use `GlobalTheory.T.matchE_of_chainStep_matches R F hLift hCore hSchur t P hGood hFix (dualC cT) cs ?_ fun k hk => hQ k hk` and prove the remaining obligations. Rewrite using `[dualC_dualC]`. Conclude with `hcT`.

Take `⟨cW, hcW⟩` from `(hP i).2.2 (dualC cV)`. Conclude with `⟨cW, GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hCore hSchur i t P hGood (hFix.2.2 i) cV cW hcW⟩`. Take `⟨cS, hcS⟩` from `(hP i).2.1 cW`. Use `⟨dualC cS, GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hCore hSchur i t P hGood (hFix.2.2 i) (dualC cS) cW ?_⟩` and prove the remaining obligations. Rewrite using `[dualC_dualC]`.

Conclude with `hcS`.
-/
theorem twoSided_of_inert : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → conjPl P = P → FixAll R t P → TwoSided R t P := by
  intro hHowe D G _ _ Pl0 T A Ks _ _ _ R F hLift hCore hSchur t P hGood hconj hFix

  have hY : ∀ k, k + 1 < D.R.m → SphCorr R.ψ (R.ωY t k) P := fun k hk =>
    GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ _ _ _ _ (R.ωY t k) P (hCore.chain.ωY t k hk) hconj (hFix.1 k hk)
  have hX : SphCorr R.ψ (R.ωX t) P :=
    GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ _ _ _ _ (R.ωX t) P (hCore.chain.ωX t) hconj hFix.2.1
  have hP : ∀ i, SphCorr R.ψ (R.ωP i t) P := fun i =>
    GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ _ _ _ _ (R.ωP i t) P (hCore.thP.ωP i t) hconj (hFix.2.2 i)
  refine ⟨⟨fun cX => ?_, fun c0 => ?_⟩, fun i => ⟨fun cV => ?_, fun cW => ?_⟩⟩
  ·
    obtain ⟨cm, hcm⟩ := hX.2.1 (dualC cX)
    obtain ⟨cs, hcs, hQ⟩ := exists_down
      (fun k c c' => k + 1 < D.R.m → Match R.ψ (R.ωY t k) P c (dualC c'))
      (fun k c' => by
        by_cases hk : k + 1 < D.R.m
        · exact ((hY k hk).2.1 (dualC c')).imp fun c hc _ => hc
        · exact ⟨c', fun h => absurd h hk⟩) (D.R.m - 1) cm
    refine ⟨cs 0, GlobalTheory.T.matchE_of_chainStep_matches R F hLift hCore hSchur t P hGood hFix cX cs ?_ fun k hk => ?_⟩
    · rw [hcs]; exact hcm
    · exact hQ k (by omega) hk
  ·
    obtain ⟨cs, hcs0, hQ⟩ := exists_up
      (fun k c c' => k + 1 < D.R.m → Match R.ψ (R.ωY t k) P c (dualC c'))
      (fun k c => by
        by_cases hk : k + 1 < D.R.m
        · obtain ⟨cT, hcT⟩ := (hY k hk).2.2 c
          exact ⟨dualC cT, fun _ => by rw [dualC_dualC]; exact hcT⟩
        · exact ⟨c, fun h => absurd h hk⟩) c0
    obtain ⟨cT, hcT⟩ := hX.2.2 (cs (D.R.m - 1))
    refine ⟨dualC cT, ?_⟩
    rw [← hcs0]
    refine GlobalTheory.T.matchE_of_chainStep_matches R F hLift hCore hSchur t P hGood hFix (dualC cT) cs ?_ fun k hk => hQ k hk
    rw [dualC_dualC]; exact hcT
  · obtain ⟨cW, hcW⟩ := (hP i).2.2 (dualC cV)
    exact ⟨cW, GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hCore hSchur i t P hGood (hFix.2.2 i) cV cW hcW⟩
  · obtain ⟨cS, hcS⟩ := (hP i).2.1 cW
    refine ⟨dualC cS, GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hCore hSchur i t P hGood (hFix.2.2 i) (dualC cS) cW ?_⟩
    rw [dualC_dualC]; exact hcS

end GlobalTheory.Hk3.TwoSidedInert

end
