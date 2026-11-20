import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselAwayPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedPrim
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedPrimIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
noncomputable section
namespace GlobalTheory.MiTop.LineAtT
variable {D : D7}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.MiTop.LineAtT
set_option maxHeartbeats 800000 in
open GlobalTheory.MiTop.LineAtT GlobalTheory.MiTop.Scale GlobalTheory.GoodPos GlobalTheory.IwaPlace GlobalTheory.FinPlLoc in
/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP v hv hTv c hc`. Take `⟨k, _, _, _, _, ι, v', o, n, G, pl, hcI, hvI, hVT, hSh, hGP, hGR, hBT, hpr⟩` from `_root_.GlobalTheory.MiTop.placedPrim_iff_placedP.2 hP`. Establish `h0 : 0 + 2 * D.R.rS + 2 = D.R.m` using `by show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m`. Take `⟨k, hk⟩` from `D.R.m_even`. Use `D.R.two_le_m` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨i, rfl⟩` from `(hSh.pre.tP v).1 ((hVT.tP v).2 hTv)`. Establish `hU` using `(hSh.pre.char i).2`. Establish `hψ : IsStdChar D W.Q.Rl.ψ (-1)` using `hcI.std`. Establish `hm` using `GlobalTheory.StMoves.moves_inv (hVT.moves 0 (by omega) (· = (o.p i).v) fun p hp hg => by`.

Take `⟨PP, h1, h2⟩` from `(hVT.gP p).1 hg`. Conclude with `hv PP h1 (h2.symm.trans hp))`. Use `(hm _ fun r => Ideal.mul_mem_right _ _ hc).symm.trans ?_` and prove the remaining obligations. Take `⟨μ, lam, hml, hz, hτ⟩` from `hBT.norm`. Establish `hξ : D.host.xi0 ≠ 0` using `GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D`.

Establish `hμ : μ ≠ 0` using `left_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))`. Establish `hj : 2 * D.R.rS + 2 * 0 + 2 = D.R.m` using `by omega`. Take `⟨lam', hl', hval⟩` from `hSh.pre.lam _ hj`. Establish `hll : lam = lam'` using `smul_left_injective _ (ne_zero_of_line (f.c.bes _ 0 hj).line) ((hτ _ hj).symm.trans hl')`. Substitute `hll` using the available equality.

Establish `uμ : UnitScal (o.p i).v μ` using `UnitScal.cancel (hml ▸ ((unitAt_of hξ hU.1).pow _).neg) (unitAt_val _ (hval i).1 (hval i).2)`. Establish `hcop : Nat.Coprime (D.mem u).A.T W.S.X.B.g`. Take `⟨M, h1, h2⟩` from `GlobalTheory.TorusCong.one_sub_T_zmod D W.S.X u`. Conclude with `GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub _ _ _ M (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)) h1 h2`. Establish `ug : UnitScal (o.p i).v (W.S.X.B.g : D.host.E)` using `unitAt_nat fun hg => by`.

Take `⟨a, b, hab⟩` from `(Nat.Coprime.cast (R := 𝓞 D.host.F) hcop)`. Conclude with `(o.p i).v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hTv) (Ideal.mul_mem_left _ _ hg)))`. Take `⟨l, hl, he⟩` from `first_scale W.S.X W.Q.instEq u _ (W.S.tr u) hW.bot.idE hψ (psiE_ne hψ _ hU o.q) hr B hμ hz`. Establish `ul : UnitScal (o.p i).v l`. Apply the tactic sequence `rcases hl with e | e <;> rw [e]`.

Use `exacts [ug, ug.neg]`. Establish `hl0 : l ≠ 0`. Establish `hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)`. Apply the tactic sequence `rcases hl with e | e <;> rw [e]`. Use `exacts [hg, neg_ne_zero.2 hg]`.

Establish `ht0 : μ * l ^ D.R.rS ≠ 0` using `mul_ne_zero hμ (pow_ne_zero _ hl0)`. Establish `ut` using `uμ.mul (ul.pow D.R.rS)`. Establish `hQ : ∀ Bl : BesLev D D.R.rS, Bl = f.c.B 0 D.R.rS h0 → ∀ LV : GlobalTheory.FinPl.Lat Bl.V, HEq LV (v'.N 0) → ∀ j, ∀ a ∈ idAt D (· = (o.p i).v), colMul Bl.d.jX j a ∈ latV Bl.V LV (· = (o.p i).v) ↔ a ∈ intAt D (· = (o.p i).v)`. Introduce and unpack `_ rfl LV hLV`. Take `rfl` from `eq_of_heq hLV`.

Introduce `j a ha`. Establish `hlam : lam ≠ 0` using `right_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))`. Take `⟨α, hα⟩` from `GlobalTheory.IdeleAA.exists_idele_AA D f.c.ψ hcI.std`. Establish `u1` using `isU_alpha hU hSh.pre.line (hα _).1`. Establish `u2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D)` using `(isU_xi hU).mul u1.conj`.

Establish `u3 : IsU (o.p i).v ((α * (xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D)` using `u1.mul (u2.inv (Units.mul_inv _))`. Establish `u4 : IsU (o.p i).v ((xiU D * α * cU α : (AE D)ˣ) : AE D)` using `((isU_xi hU).mul u1).mul u1.conj`. Establish `u5 : IsU (o.p i).v (((xiU D * α * cU α) ^ (D.R.rS - j.1) * ((α * (xiU D * cU α)⁻¹) ^ (D.R.rS + 1) * inU lam hlam) : (AE D)ˣ) : AE D)`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]`. Conclude with `(u4.pow _).mul ((u3.pow _).mul (isU_of_val _ (hval i).1 (hval i).2))`.

Use `(iso_line_all hcI hSh hpr (_root_.GlobalTheory.MiTop.rank_X_succ_pos f) hlam hτ (hα _).1 (fun s hs => ?_) _ 0 h0 j a ha).trans (u5.inv (Units.mul_inv _) a ha).symm` and prove the remaining obligations. Rewrite using `[(hα _).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]`. Generalize the expression as in `μ * l ^ D.R.rS = t at he ht0 ut`. Establish `hc' : incA D t⁻¹ * c ∈ idAt D (· = (o.p i).v)` using `Ideal.mul_mem_left _ _ hc`. Establish `e1 : incA D t * (incA D t⁻¹ * c) = c`.

Rewrite using `[← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ ht0, RingHom.map_one, one_mul]`. Establish `h1` using `(hQ B.lev (hBT.lev h0) (v'.N 0) HEq.rfl ⟨0, hr⟩ _ hc').trans (ut _ hc').symm`. Rewrite `h1` using `[e1]`. Use `Iff.trans (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v'.N 0) (· = (o.p i).v)) (funext fun r => ?_))) h1` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (incA D t⁻¹ * c * ·) (he r)).symm` and prove the remaining obligations.

Conclude with `(congrArg (· * _) e1.symm).trans (by rw [mul_comm (incA D t), mul_assoc])`.
-/
theorem GlobalTheory.MiTop.line_ideal_at_own_prime_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP v hv hTv c hc
  obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, hcI, hvI, hVT, hSh, hGP, hGR, hBT, hpr⟩ := _root_.GlobalTheory.MiTop.placedPrim_iff_placedP.2 hP
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  obtain ⟨i, rfl⟩ := (hSh.pre.tP v).1 ((hVT.tP v).2 hTv)
  have hU := (hSh.pre.char i).2
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hcI.std
  have hm := GlobalTheory.StMoves.moves_inv (hVT.moves 0 (by omega) (· = (o.p i).v) fun p hp hg => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP p).1 hg
    exact hv PP h1 (h2.symm.trans hp))
  refine (hm _ fun r => Ideal.mul_mem_right _ _ hc).symm.trans ?_
  obtain ⟨μ, lam, hml, hz, hτ⟩ := hBT.norm
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
  have hj : 2 * D.R.rS + 2 * 0 + 2 = D.R.m := by omega
  obtain ⟨lam', hl', hval⟩ := hSh.pre.lam _ hj
  have hll : lam = lam' := smul_left_injective _ (ne_zero_of_line (f.c.bes _ 0 hj).line) ((hτ _ hj).symm.trans hl')
  subst hll
  have uμ : UnitScal (o.p i).v μ := UnitScal.cancel (hml ▸ ((unitAt_of hξ hU.1).pow _).neg) (unitAt_val _ (hval i).1 (hval i).2)
  have hcop : Nat.Coprime (D.mem u).A.T W.S.X.B.g := by
    obtain ⟨M, h1, h2⟩ := GlobalTheory.TorusCong.one_sub_T_zmod D W.S.X u
    exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub _ _ _ M (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)) h1 h2
  have ug : UnitScal (o.p i).v (W.S.X.B.g : D.host.E) := unitAt_nat fun hg => by
    obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.F) hcop)
    exact (o.p i).v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hTv) (Ideal.mul_mem_left _ _ hg)))
  obtain ⟨l, hl, he⟩ := first_scale W.S.X W.Q.instEq u _ (W.S.tr u) hW.bot.idE hψ (psiE_ne hψ _ hU o.q) hr B hμ hz
  have ul : UnitScal (o.p i).v l := by
    rcases hl with e | e <;> rw [e]
    exacts [ug, ug.neg]
  have hl0 : l ≠ 0 := by
    have hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)
    rcases hl with e | e <;> rw [e]
    exacts [hg, neg_ne_zero.2 hg]
  have ht0 : μ * l ^ D.R.rS ≠ 0 := mul_ne_zero hμ (pow_ne_zero _ hl0)
  have ut := uμ.mul (ul.pow D.R.rS)
  have hQ : ∀ Bl : BesLev D D.R.rS, Bl = f.c.B 0 D.R.rS h0 → ∀ LV : GlobalTheory.FinPl.Lat Bl.V, HEq LV (v'.N 0) → ∀ j,
      ∀ a ∈ idAt D (· = (o.p i).v), colMul Bl.d.jX j a ∈ latV Bl.V LV (· = (o.p i).v) ↔ a ∈ intAt D (· = (o.p i).v) := by
    rintro _ rfl LV hLV
    obtain rfl := eq_of_heq hLV
    intro j a ha
    have hlam : lam ≠ 0 := right_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
    obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D f.c.ψ hcI.std
    have u1 := isU_alpha hU hSh.pre.line (hα _).1
    have u2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D) := (isU_xi hU).mul u1.conj
    have u3 : IsU (o.p i).v ((α * (xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := u1.mul (u2.inv (Units.mul_inv _))
    have u4 : IsU (o.p i).v ((xiU D * α * cU α : (AE D)ˣ) : AE D) := ((isU_xi hU).mul u1).mul u1.conj
    have u5 : IsU (o.p i).v (((xiU D * α * cU α) ^ (D.R.rS - j.1) *
        ((α * (xiU D * cU α)⁻¹) ^ (D.R.rS + 1) * inU lam hlam) : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact (u4.pow _).mul ((u3.pow _).mul (isU_of_val _ (hval i).1 (hval i).2))
    refine (iso_line_all hcI hSh hpr (_root_.GlobalTheory.MiTop.rank_X_succ_pos f) hlam hτ (hα _).1 (fun s hs => ?_) _ 0 h0 j a ha).trans
      (u5.inv (Units.mul_inv _) a ha).symm
    rw [(hα _).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  generalize μ * l ^ D.R.rS = t at he ht0 ut
  have hc' : incA D t⁻¹ * c ∈ idAt D (· = (o.p i).v) := Ideal.mul_mem_left _ _ hc
  have e1 : incA D t * (incA D t⁻¹ * c) = c := by
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ ht0, RingHom.map_one, one_mul]
  have h1 := (hQ B.lev (hBT.lev h0) (v'.N 0) HEq.rfl ⟨0, hr⟩ _ hc').trans (ut _ hc').symm
  rw [e1] at h1
  refine Iff.trans (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v'.N 0) (· = (o.p i).v)) (funext fun r => ?_))) h1
  refine Eq.trans ?_ (congrArg (incA D t⁻¹ * c * ·) (he r)).symm
  exact (congrArg (· * _) e1.symm).trans (by rw [mul_comm (incA D t), mul_assoc])
end
end
