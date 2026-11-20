import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BasePairChar

variable {D : D7}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Substitute `hw` using the available equality. Establish `key : ∀ y, Formalism.L2.Host.IsUnitAt w y → finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ) ∈ intAE D` using `fun y hy => (GlobalTheory.LFun.mem_int_iff _).2 fun P => by`. Rewrite using `[show GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ)) = Neutral.B1.finiteSingle _ w y from GlobalTheory.LFun.finTens_locIdele w y]`. Distinguish the cases in `e : P = w`. Substitute `e` using the available equality.

Rewrite using `[GlobalTheory.LFun.finSingle_self]`. Conclude with `hy.le`. Rewrite using `[GlobalTheory.LFun.finSingle_ne e, map_one]`. Take `⟨α, rfl, h1, -⟩` from `hε`. Introduce `y hy`.

Establish `hs : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * ((GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1) = (GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1`. Use `GlobalTheory.LFun.tens_ext ?_ ?_` and prove the remaining obligations. Simplify using `only [map_mul, map_sub, map_one, GlobalTheory.LFun.infTens_locIdele, sub_self, mul_zero]`. Apply `(GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective` to reduce the goal to its premises. Establish `e2` using `GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y`.

Use `FiniteAdeleRing.ext _ fun P => ?_` and prove the remaining obligations. Simplify using `only [map_mul, map_sub, map_one, e2]`. Establish `hA : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.LFun.finTens D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E))` using `rfl`. Rewrite using `[hA]`. Express the relevant statement in the definitionally equal form `GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) P * (Neutral.B1.finiteSingle D.host.E w y P - 1) = Neutral.B1.finiteSingle D.host.E w y P - 1`.

Rewrite using `[GlobalTheory.LFun.finAdEquiv_tmul, map_one, mul_one]`. Distinguish the cases in `hP : P = w`. Substitute `hP` using the available equality. Rewrite using `[GlobalTheory.LFun.finSingle_self]`. Establish `: α (P.under (𝓞 D.host.F)) = 1` using `h1`.

Rewrite using `[this, map_one, one_mul]`. Rewrite using `[GlobalTheory.LFun.finSingle_ne hP, sub_self, mul_zero]`. Establish `h` using `hc _ hs (key y hy) (by`. Rewrite using `[← map_inv]`. Use `key _ ?_` and prove the remaining obligations.

Unfold `Formalism.L2.Host.IsUnitAt at hy ⊢`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])`. Conclude with `(congrArg Circle.toUnits h).trans (map_one _)`.
-/
theorem unrAt_of_unramAt {c : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hc : GlobalTheory.WeilParts.UnramAt ε c) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.LFun.UnrAt c w := by
  subst hw
  have key : ∀ y, Formalism.L2.Host.IsUnitAt w y → finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ) ∈ intAE D := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).2 fun P => by
      rw [show GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ)) =
        Neutral.B1.finiteSingle _ w y from GlobalTheory.LFun.finTens_locIdele w y]
      by_cases e : P = w
      · subst e; rw [GlobalTheory.LFun.finSingle_self]; exact hy.le
      · rw [GlobalTheory.LFun.finSingle_ne e, map_one]
  obtain ⟨α, rfl, h1, -⟩ := hε
  intro y hy
  have hs : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * ((GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1) =
      (GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1 := by
    refine GlobalTheory.LFun.tens_ext ?_ ?_
    · simp only [map_mul, map_sub, map_one, GlobalTheory.LFun.infTens_locIdele, sub_self, mul_zero]
    · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      have e2 := GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y
      refine FiniteAdeleRing.ext _ fun P => ?_
      simp only [map_mul, map_sub, map_one, e2]
      have hA : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.LFun.finTens D.host.F D.host.E
          (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) =
          GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) := rfl
      rw [hA]
      change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) P *
          (Neutral.B1.finiteSingle D.host.E w y P - 1) = Neutral.B1.finiteSingle D.host.E w y P - 1
      rw [GlobalTheory.LFun.finAdEquiv_tmul, map_one, mul_one]
      by_cases hP : P = w
      · subst hP
        rw [GlobalTheory.LFun.finSingle_self]
        have : α (P.under (𝓞 D.host.F)) = 1 := h1
        rw [this, map_one, one_mul]
      · rw [GlobalTheory.LFun.finSingle_ne hP, sub_self, mul_zero]
  have h := hc _ hs (key y hy) (by
    rw [← map_inv]
    refine key _ ?_
    unfold Formalism.L2.Host.IsUnitAt at hy ⊢
    rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  exact (congrArg Circle.toUnits h).trans (map_one _)

open Formalism.L2.JoinChr in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D V W B hB χ hc bad hbad`. Use `⟨fun Q hQ => ?_, fun Q hQ k => ?_⟩` and prove the remaining obligations. Establish `hPg : GlobalTheory.ExportSeries.SplitSet B.G.Pg`. Take `⟨P, h1, -, h3⟩` from `hB.places.split`. Conclude with `h3.mono h1`.

Establish `hu : GlobalTheory.StepLaw.UnrOff (B.mu * B.eta⁻¹) (B.G.Pg ∪ B.de.Q)` using `(GlobalTheory.StepLaw.UnrOff.mul (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hB.unram hPg Finset.subset_union_left) (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hB.de.unram hB.de.split Finset.subset_union_right)).mul (GlobalTheory.ExportSeries.TupleChars.unrOff …`. Take `⟨ε, hε⟩` from `GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))`. Use `(GlobalTheory.LFun.unrAt_iff_of_chrEq hc Q).1 (unrAt_of_unramAt hε (hu _ ε hε fun PP hPP he => ?_) rfl)` and prove the remaining obligations. Establish `hm : (bad : 𝓞 D.host.E) ∈ PP.asIdeal` using `hbad PP (Finset.mem_union.1 hPP)`. Break down `GlobalTheory.IdemSupport.eq_or_eq_cP he with h | h` into its components or cases.

Conclude with `hQ (h ▸ hm)`. Rewrite `hm` using `[h, GlobalTheory.IdemSupport.mem_cP, map_natCast]`. Conclude with `hQ hm`. Take `⟨e, he⟩` from `GlobalTheory.StdFrames.exists_isIdemAt hQ`. Establish `he' : Formalism.L2.NTheta.IsIdemAt (cA D e) (GlobalTheory.IdemSupport.cP Q)` using `GlobalTheory.MovedIdem.isIdemAt_conj he fun x => GlobalTheory.IdemSupport.mem_cP Q x`.

Establish `p1` using `GlobalTheory.HeckeDetChar.isPlIdem he`. Establish `p2` using `GlobalTheory.HeckeDetChar.isPlIdem he'`. Establish `hs : star ((Formalism.L2.Host.upF D.host.F k : D.host.Eˣ) : D.host.E) = (Formalism.L2.Host.upF D.host.F k : D.host.Eˣ)` using `(D.sp.cm.fixed _).2 ⟨k, rfl⟩`. Set `y : (AE D)ˣ` to `locU p1.1 (Formalism.L2.Host.upF D.host.F k)`. Establish `h1` using `hc.2 Q e p1 _ y (locU_val p1.1 _)`.

Establish `h2` using `hc.2 _ (cA D e) p2 (Formalism.L2.Host.upF D.host.F k) (Units.map (cA D).toMonoidHom y) (by`. Express the relevant statement in the definitionally equal form `cA D (y : AE D) = _`. Rewrite using `[locU_val, locE, locE, map_add, map_one, map_mul, map_sub, map_one, GlobalTheory.IdemSupport.cA_incA, hs])`. Establish `r2 : ResEta D B.eta 1` using `hB.eta.2.2.1`. Establish `r0 : ResEta D B.mu0 0` using `GlobalTheory.SplitChange.resEta_zero_of_triv r2 hB.real`.

Establish `r1 : ResEta D B.de.chi 0` using `GlobalTheory.SplitChange.resEta_zero_of_triv r2 hB.de.real`. Establish `hconj : (B.mu * B.eta⁻¹) (Units.map (cA D).toMonoidHom y) = ((B.mu * B.eta⁻¹) y)⁻¹`. Simplify using `only [GlobalTheory.ExportSeries.Base.mu, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ConjAdjWeil.chi_conj r0, GlobalTheory.ConjAdjWeil.chi_conj r1, GlobalTheory.ConjAdjWeil.chi_conj r2, mul_inv, inv_inv]`. Rewrite using `[Formalism.L2.Host.HChar.resFin_apply, GlobalTheory.ClassScalarValue.above_eq, Finset.prod_pair hQ.symm]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, Units.val_one, ← h1, ← h2, hconj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]`.
-/
theorem base_pair_char : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq (B.mu * B.eta⁻¹) χ → ∀ bad : ℕ, (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q → (bad : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1 := by
  intro D V W B hB χ hc bad hbad
  classical
  refine ⟨fun Q hQ => ?_, fun Q hQ k => ?_⟩
  · have hPg : GlobalTheory.ExportSeries.SplitSet B.G.Pg := by
      obtain ⟨P, h1, -, h3⟩ := hB.places.split
      exact h3.mono h1
    have hu : GlobalTheory.StepLaw.UnrOff (B.mu * B.eta⁻¹) (B.G.Pg ∪ B.de.Q) :=
      (GlobalTheory.StepLaw.UnrOff.mul
        (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hB.unram hPg Finset.subset_union_left)
        (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hB.de.unram hB.de.split Finset.subset_union_right)).mul
        (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unramEverywhere hB.eta.2.1 _).inv
    obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq hc Q).1 (unrAt_of_unramAt hε (hu _ ε hε fun PP hPP he => ?_) rfl)
    have hm : (bad : 𝓞 D.host.E) ∈ PP.asIdeal := hbad PP (Finset.mem_union.1 hPP)
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP he with h | h
    · exact hQ (h ▸ hm)
    · rw [h, GlobalTheory.IdemSupport.mem_cP, map_natCast] at hm
      exact hQ hm
  · obtain ⟨e, he⟩ := GlobalTheory.StdFrames.exists_isIdemAt hQ
    have he' : Formalism.L2.NTheta.IsIdemAt (cA D e) (GlobalTheory.IdemSupport.cP Q) :=
      GlobalTheory.MovedIdem.isIdemAt_conj he fun x => GlobalTheory.IdemSupport.mem_cP Q x
    have p1 := GlobalTheory.HeckeDetChar.isPlIdem he
    have p2 := GlobalTheory.HeckeDetChar.isPlIdem he'
    have hs : star ((Formalism.L2.Host.upF D.host.F k : D.host.Eˣ) : D.host.E) = (Formalism.L2.Host.upF D.host.F k : D.host.Eˣ) :=
      (D.sp.cm.fixed _).2 ⟨k, rfl⟩
    let y : (AE D)ˣ := locU p1.1 (Formalism.L2.Host.upF D.host.F k)
    have h1 := hc.2 Q e p1 _ y (locU_val p1.1 _)
    have h2 := hc.2 _ (cA D e) p2 (Formalism.L2.Host.upF D.host.F k) (Units.map (cA D).toMonoidHom y) (by
      change cA D (y : AE D) = _
      rw [locU_val, locE, locE, map_add, map_one, map_mul, map_sub, map_one, GlobalTheory.IdemSupport.cA_incA, hs])
    have r2 : ResEta D B.eta 1 := hB.eta.2.2.1
    have r0 : ResEta D B.mu0 0 := GlobalTheory.SplitChange.resEta_zero_of_triv r2 hB.real
    have r1 : ResEta D B.de.chi 0 := GlobalTheory.SplitChange.resEta_zero_of_triv r2 hB.de.real
    have hconj : (B.mu * B.eta⁻¹) (Units.map (cA D).toMonoidHom y) = ((B.mu * B.eta⁻¹) y)⁻¹ := by
      simp only [GlobalTheory.ExportSeries.Base.mu, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ConjAdjWeil.chi_conj r0,
        GlobalTheory.ConjAdjWeil.chi_conj r1, GlobalTheory.ConjAdjWeil.chi_conj r2, mul_inv, inv_inv]
    rw [Formalism.L2.Host.HChar.resFin_apply, GlobalTheory.ClassScalarValue.above_eq, Finset.prod_pair hQ.symm]
    apply Units.ext
    rw [Units.val_mul, Units.val_one, ← h1, ← h2, hconj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]

end GlobalTheory.BasePairChar
