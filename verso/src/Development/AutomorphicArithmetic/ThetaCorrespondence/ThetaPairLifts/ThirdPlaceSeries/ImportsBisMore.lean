import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.MuTameQS
/- English proof (translation)
Introduce `hL D P S hS i w hw hSQ`. Establish `hj` using `D.nd.j_range i`. Set `j : Fin D.R.m` to `⟨D.nd.j i - 1, by omega⟩`. Establish `hjj : j.1 + 1 = D.nd.j i` using `by simp only [j]; omega`. Establish `hc` using `hS.mu i w hw j hjj`.

Establish `hc' : IsComp (P.tp.tup (D.nd.mu i) j) w ((P.tp.tup (D.nd.mu i) j).loc w)` using `⟨GlobalTheory.HeckeComp.smooth_loc _ w, fun _ => rfl⟩`. Establish `hmu : (S i w hw).mu = (P.tp.tup (D.nd.mu i) j).loc w` using `GlobalTheory.HeckeComp.eq_of_isComp hc' hc`. Rewrite using `[hmu]`. Use `⟨isTame_loc (tameAt_mul ((P.cf.isMu0 j).tame w) (P.tp.xi_tame _ w)), fun hg => ?_⟩` and prove the remaining obligations. Use `not_isUnram_loc fun hU => ?_` and prove the remaining obligations.

Establish `hm0 : (P.cf.mu0 j).UnrAt w` using `(P.cf.isMu0 j).unr w fun k hk => hg k hk`. Establish `hX : (P.tp.xi (D.nd.mu i)).UnrAt w` using `unrAt_of_mul_left hm0 hU`. Rewrite `hX` using `[D.nd.mu_w i, P.tp.xi_tw, CharFrame.delAt, D.nd.w_l i]`. Establish `hpsi` using `P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)`. Rewrite `hpsi` using `[D.nd.w_l i, ← P.Q_eq i]`.

Establish `hnl : w ∉ placesOver D.host.E (D.nd.l i)` using `D.nd.SQ_l i w hSQ`. Break down `hSQ with hwS | hwQ` into its components or cases. Establish `hwQ : w ∉ D.nd.Q i` using `Finset.disjoint_left.1 (D.nd.SQ_disj i) hwS`. Establish `hp : (P.tp.psi (D.nd.w i)).UnrAt w` using `(hpsi.ram w).2 hwQ`. Establish `hd` using `(D.nd.S_def i w).1 hwS`.

Break down `hd.1 with h0 | h1 | hq` into its components or cases. Conclude with `hg 0 h0`. Conclude with `hg 1 h1`. Use `split_ifs at hX hq with hl`. Establish `hdu` using `unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del' * _ = _) ▸ hX)`.

Use `(P.cf.isDel'.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx` as an intermediate fact. Evaluate the numerical expressions using `at this`. Establish `hdu` using `unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del * _ = _) ▸ hX)`. Use `(P.cf.isDel.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx` as an intermediate fact. Evaluate the numerical expressions using `at this`.

Establish `hwS : w ∉ D.nd.S i` using `fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hwQ`. Establish `hd : (CharFrame.delAt P.cf (D.nd.l i)).UnrAt w`. Unfold `CharFrame.delAt`. Use `split_ifs with hl`. Use `P.cf.isDel'.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)` and prove the remaining obligations.

Rewrite using `[if_pos hl]`. Conclude with `ho`. Use `P.cf.isDel.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)` and prove the remaining obligations. Rewrite using `[if_neg hl]`. Conclude with `ho`.

Establish `hX' : (CharFrame.delAt P.cf (D.nd.l i) * P.tp.psi (D.nd.w i)).UnrAt w`. Unfold `CharFrame.delAt`. Conclude with `hX`. Conclude with `(hpsi.ram w).1 (unrAt_of_mul_left hd hX') hwQ`.
-/
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu ∧ ((∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu) := by
  intro hL D P S hS i w hw hSQ
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i w hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) w ((P.tp.tup (D.nd.mu i) j).loc w) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ w, fun _ => rfl⟩
  have hmu : (S i w hw).mu = (P.tp.tup (D.nd.mu i) j).loc w := GlobalTheory.HeckeComp.eq_of_isComp hc' hc
  rw [hmu]
  refine ⟨isTame_loc (tameAt_mul ((P.cf.isMu0 j).tame w) (P.tp.xi_tame _ w)), fun hg => ?_⟩
  refine not_isUnram_loc fun hU => ?_
  have hm0 : (P.cf.mu0 j).UnrAt w := (P.cf.isMu0 j).unr w fun k hk => hg k hk
  have hX : (P.tp.xi (D.nd.mu i)).UnrAt w := unrAt_of_mul_left hm0 hU
  rw [D.nd.mu_w i, P.tp.xi_tw, CharFrame.delAt, D.nd.w_l i] at hX
  have hpsi := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i, ← P.Q_eq i] at hpsi
  have hnl : w ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i w hSQ
  rcases hSQ with hwS | hwQ
  ·
    have hwQ : w ∉ D.nd.Q i := Finset.disjoint_left.1 (D.nd.SQ_disj i) hwS
    have hp : (P.tp.psi (D.nd.w i)).UnrAt w := (hpsi.ram w).2 hwQ
    have hd := (D.nd.S_def i w).1 hwS
    rcases hd.1 with h0 | h1 | hq
    · exact hg 0 h0
    · exact hg 1 h1
    · split_ifs at hX hq with hl
      · have hdu := unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del' * _ = _) ▸ hX)
        have := (P.cf.isDel'.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx
        norm_num at this
      · have hdu := unrAt_of_mul_left hp ((mul_comm _ _ : P.cf.del * _ = _) ▸ hX)
        have := (P.cf.isDel.ine w hq 1).1 fun x hx => by rw [pow_one]; exact hdu x hx
        norm_num at this
  ·
    have hwS : w ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hwQ
    have hd : (CharFrame.delAt P.cf (D.nd.l i)).UnrAt w := by
      unfold CharFrame.delAt
      split_ifs with hl
      · refine P.cf.isDel'.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)
        rw [if_pos hl]; exact ho
      · refine P.cf.isDel.unr w fun ho => hwS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr ?_), hnl⟩)
        rw [if_neg hl]; exact ho
    have hX' : (CharFrame.delAt P.cf (D.nd.l i) * P.tp.psi (D.nd.w i)).UnrAt w := by
      unfold CharFrame.delAt; exact hX
    exact (hpsi.ram w).1 (unrAt_of_mul_left hd hX') hwQ
end GlobalTheory.MuTameQS
end
