import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceSplitCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ValInert
/- English proof (translation)
Introduce `_ hL D P X _ _ _ _ i hμ j hj w hG hI c hc`. Establish `hcw` using `conjSelf D w hI`. Establish `hLv : X.R.toLevCh.Is X.A.μ0` using `X.recR.base.lev`. Take `⟨hg, -, -⟩` from `(GlobalTheory.GoodPrimes.good_primes X.R X.F hLv).2.1 _ w hG`. Establish `hm0 : (X.R.C.mu0 j).UnrAt w` using `(X.R.C.isMu0 j).unr w fun k hk => hg (by`.

Establish `hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal` using `hk`. Rewrite using `[Nat.cast_mul]`. Use `fin_cases k`. Conclude with `Ideal.mul_mem_right _ _ hk'`. Conclude with `Ideal.mul_mem_left _ _ hk')`.

Establish `hxu : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w`. Assume the negation of the conclusion as `h`. Break down `(hLv.Q_ram _ w).1 h with h | ⟨PP, h, hc⟩` into its components or cases. Conclude with `(hG w (Or.inr h)).1 rfl`. Conclude with `(hG PP (Or.inr h)).2 hc`.

Establish `hxi : X.R.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i)`. Rewrite using `[X.recR.tupXi _ hμ, xi_eq X.cfEq X.Tp P.tp X.tpEq]`. Establish `hmu : (P.chr.e1 (D.naut.muC i)).1 = X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i))`. Rewrite using `[P.chr.muC i j hj, hxi, X.cfEq]`. Both sides reduce to the same expression.

Establish `hu : D.naut.unr (D.naut.locG (D.naut.muC i) w)` using `(P.chr.unr_iff _ w).2 (by rw [hmu]; exact hm0.mul hxu)`. Take `⟨a, ha⟩` from `Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu).trans (D.naut.locG_dim _ w))`. Establish `haa : a = a⁻¹`. Establish `e` using `(D.naut.csd_unr (D.naut.muC i) w w (D.naut.muC_csd i) hcw hu).2`. Rewrite `e` using `[ha, Multiset.map_singleton]`.

Conclude with `Multiset.singleton_inj.1 e`. Establish `hns` using `notSplit D w hcw`. Establish `heu` using `(D.naut.etaTinv_def w).1`. Establish `hee : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(-1 : ℂ)⁻¹}`. Rewrite using `[(D.naut.etaTinv_def w).2, D.naut.etaT_inert w hns, Multiset.map_singleton]`.

Establish `hc1 : c = a * (-1 : ℂ)⁻¹`. Rewrite `hc` using `[D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu heu (D.naut.locG_dim _ w) hee, ha, Multiset.map_singleton]`. Conclude with `(Multiset.singleton_inj.1 hc).symm`. Establish `hcc : c = c⁻¹`. Establish `h1 : (-1 : ℂ)⁻¹ = -1` using `by norm_num`.

Rewrite using `[hc1, mul_inv, inv_inv, ← haa, h1]`. Establish `hte : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) * X.R.C.eta⁻¹`. Rewrite using `[P.chr.tw, hmu, P.chr.etaTinv, X.cfEq]`. Establish `hut : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w` using `(P.chr.unr_iff _ w).1 (by rw [D.naut.locG_tw]; exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu heu)`. Establish `hc2` using `P.chr.frob _ w hut`.

Rewrite `hc2` using `[hc]`. Establish `hc3 : c = (((X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ : ℂˣ) : ℂ)⁻¹`. Rewrite using `[Multiset.singleton_inj.1 hc2, hte]`. Simplify using the standard rewrite rules. Establish `hv : GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w = (X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹`.

Rewrite using `[← GlobalTheory.LFun.val_eq_of_chrEq (hLv.mu0 j) w, ← GlobalTheory.LFun.val_eq_of_chrEq (hLv.xi _) w, ← GlobalTheory.LFun.val_eq_of_chrEq hLv.eta w]`. Use `first`. Consider the case `rfl`. Consider the case `(simp only [GlobalTheory.DownLift.valV, GlobalTheory.DownLift.chiV, Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, GlobalTheory.LFun.val, GlobalTheory.LFun.locChar]; ext; simp)`. Consider the case `(unfold GlobalTheory.DownLift.valV GlobalTheory.DownLift.chiV Formalism.IndefR.Lift.chrTh Formalism.IndefR.Links.LevCh.mu Formalism.IndefR.Lift.tup GlobalTheory.LFun.val GlobalTheory.LFun.locChar; simp)`.

Rewrite using `[hv, hcc, hc3, inv_inv]`.
-/
theorem val_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ c : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} → c = (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) := by
  intro _ hL D P X _ _ _ _ i hμ j hj w hG hI c hc
  have hcw := conjSelf D w hI
  have hLv : X.R.toLevCh.Is X.A.μ0 := X.recR.base.lev
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes X.R X.F hLv).2.1 _ w hG
  have hm0 : (X.R.C.mu0 j).UnrAt w := (X.R.C.isMu0 j).unr w fun k hk => hg (by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk')
  have hxu : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra h
    rcases (hLv.Q_ram _ w).1 h with h | ⟨PP, h, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr h)).2 hc
  have hxi : X.R.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq X.cfEq X.Tp P.tp X.tpEq]
  have hmu : (P.chr.e1 (D.naut.muC i)).1 = X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) := by
    rw [P.chr.muC i j hj, hxi, X.cfEq]
    rfl
  have hu : D.naut.unr (D.naut.locG (D.naut.muC i) w) := (P.chr.unr_iff _ w).2 (by rw [hmu]; exact hm0.mul hxu)
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu).trans (D.naut.locG_dim _ w))
  have haa : a = a⁻¹ := by
    have e := (D.naut.csd_unr (D.naut.muC i) w w (D.naut.muC_csd i) hcw hu).2
    rw [ha, Multiset.map_singleton] at e
    exact Multiset.singleton_inj.1 e
  have hns := notSplit D w hcw
  have heu := (D.naut.etaTinv_def w).1
  have hee : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(-1 : ℂ)⁻¹} := by
    rw [(D.naut.etaTinv_def w).2, D.naut.etaT_inert w hns, Multiset.map_singleton]
  have hc1 : c = a * (-1 : ℂ)⁻¹ := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu heu (D.naut.locG_dim _ w) hee, ha, Multiset.map_singleton] at hc
    exact (Multiset.singleton_inj.1 hc).symm
  have hcc : c = c⁻¹ := by
    have h1 : (-1 : ℂ)⁻¹ = -1 := by norm_num
    rw [hc1, mul_inv, inv_inv, ← haa, h1]
  have hte : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 =
      X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, hmu, P.chr.etaTinv, X.cfEq]
  have hut : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w :=
    (P.chr.unr_iff _ w).1 (by rw [D.naut.locG_tw]; exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu heu)
  have hc2 := P.chr.frob _ w hut
  rw [hc] at hc2
  have hc3 : c = (((X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ : ℂˣ) : ℂ)⁻¹ := by
    rw [Multiset.singleton_inj.1 hc2, hte]
    simp
  have hv : GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w =
      (X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ := by
    rw [← GlobalTheory.LFun.val_eq_of_chrEq (hLv.mu0 j) w, ← GlobalTheory.LFun.val_eq_of_chrEq (hLv.xi _) w,
      ← GlobalTheory.LFun.val_eq_of_chrEq hLv.eta w]
    first
      | rfl
      | (simp only [GlobalTheory.DownLift.valV, GlobalTheory.DownLift.chiV, Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, GlobalTheory.LFun.val, GlobalTheory.LFun.locChar]; ext; simp)
      | (unfold GlobalTheory.DownLift.valV GlobalTheory.DownLift.chiV Formalism.IndefR.Lift.chrTh Formalism.IndefR.Links.LevCh.mu Formalism.IndefR.Lift.tup GlobalTheory.LFun.val GlobalTheory.LFun.locChar; simp)
  rw [hv, hcc, hc3, inv_inv]
end GlobalTheory.ValInert
end
