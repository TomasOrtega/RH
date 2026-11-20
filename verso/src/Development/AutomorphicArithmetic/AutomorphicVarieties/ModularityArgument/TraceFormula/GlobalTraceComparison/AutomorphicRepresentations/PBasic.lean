import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IntegrableShift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `h` using `congrArg (fun g : GA E n => logAbs g.val.det) (Dcy.splitCentre_mul_tor (E := E) (n := n) τ (fun _ => 0))`. Simplify using `only [Dcy.logAbs_det_mul', Dcy.logAbs_det_tor] at h`. Simplify using `using h`.
-/
private theorem logAbs_det_centre (τ : ℝ) :
    logAbs (splitCentre E n τ).val.det = Module.finrank ℚ E * (n * τ) := by
  have h := congrArg (fun g : GA E n => logAbs g.val.det) (Dcy.splitCentre_mul_tor (E := E) (n := n) τ (fun _ => 0))
  simp only [Dcy.logAbs_det_mul', Dcy.logAbs_det_tor] at h
  simpa using h

/- English proof (translation)
Establish `hd : (Module.finrank ℚ E : ℝ) ≠ 0` using `by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'`. Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast (by omega : n ≠ 0)`. Express the relevant statement in the definitionally equal form `logAbs (splitCentre E n (t / (n * Module.finrank ℚ E))).val.det = t`. Rewrite using `[logAbs_det_centre]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem ldet_ac (hn : 1 ≤ n) (t : ℝ) : ldet (ac E n t) = t := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  change logAbs (splitCentre E n (t / (n * Module.finrank ℚ E))).val.det = t
  rw [logAbs_det_centre]
  field_simp

/- English proof (translation)
Establish `h` using `Dcy.logAbs_det_mul' g g⁻¹`. Establish `h1` using `Dcy.logAbs_ratGL' (E := E) (n := n) 1`. Rewrite `h1` using `[map_one]`. Rewrite `h` using `[mul_inv_cancel, h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem logAbs_det_inv (g : GA E n) : logAbs (g⁻¹ : GA E n).val.det = -logAbs g.val.det := by
  have h := Dcy.logAbs_det_mul' g g⁻¹
  have h1 := Dcy.logAbs_ratGL' (E := E) (n := n) 1
  rw [map_one] at h1
  rw [mul_inv_cancel, h1] at h
  linarith

/- English proof (translation)
Establish `h : (thetaA E n g).val.det = conjAd E (g⁻¹ : GA E n).val.det`. Express the relevant statement in the definitionally equal form `(((g⁻¹ : GA E n).val.map (conjAd E))ᵀ).det = _`. Rewrite using `[Matrix.det_transpose]`. Conclude with `(RingHom.map_det (conjAd E) _).symm`. Rewrite using `[h, GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj D1.conjPlaces, logAbs_det_inv]`.
-/
private theorem logAbs_det_theta (g : GA E n) : logAbs (thetaA E n g).val.det = -logAbs g.val.det := by
  have h : (thetaA E n g).val.det = conjAd E (g⁻¹ : GA E n).val.det := by
    change (((g⁻¹ : GA E n).val.map (conjAd E))ᵀ).det = _
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (conjAd E) _).symm
  rw [h, GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj D1.conjPlaces, logAbs_det_inv]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ n hn`. Use `⟨ldet_ac hn, fun x y => Dcy.logAbs_det_mul' x.1 y.1, fun t x => ?_, fun s t => ?_, ?_, ?_, fun x => ?_, fun x => ?_, fun x y => ?_, ?_, continuous_ldet, ?_⟩` and prove the remaining obligations. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `CuspidalL2GL.splitCentre_comm _ _`. Express the relevant statement in the definitionally equal form `1 * x.2 = x.2 * 1`.

Rewrite using `[one_mul, mul_one]`. Use `Prod.ext ?_ (mul_one _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `splitCentre E n ((s + t) / _) = splitCentre E n (s / _) * splitCentre E n (t / _)`. Rewrite using `[add_div, CuspidalL2GL.splitCentre_add]`. Use `Prod.ext ?_ rfl` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `splitCentre E n (0 / _) = 1`. Rewrite using `[zero_div, CuspidalL2GL.splitCentre_zero]`. Conclude with `(GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const`. Conclude with `logAbs_det_theta x.1`. Conclude with `Prod.ext ((thetaBasic_holds E n).2.1 x.1) ((thetaBasic_holds E 0).2.1 x.2)`.

Conclude with `Prod.ext (map_mul (thetaA E n) x.1 y.1) (map_mul (thetaA E 0) x.2 y.2)`. Introduce and unpack `⟨_, γ, rfl⟩`. Use `⟨Dcy.logAbs_ratGL' γ.1, ⟨(thetaE E n γ.1, thetaE E 0 γ.2), ?_⟩⟩` and prove the remaining obligations. Conclude with `Prod.ext ((thetaBasic_holds E n).2.2 γ.1).symm ((thetaBasic_holds E 0).2.2 γ.2).symm`. Conclude with `(((thetaBasic_holds E n).1.comp continuous_fst).prodMk ((thetaBasic_holds E 0).1.comp continuous_snd))`.
-/
theorem basic_pf : Basic := by
  intro E _ _ _ n hn
  refine ⟨ldet_ac hn, fun x y => Dcy.logAbs_det_mul' x.1 y.1, fun t x => ?_, fun s t => ?_, ?_, ?_, fun x => ?_, fun x => ?_,
    fun x y => ?_, ?_, continuous_ldet, ?_⟩
  · refine Prod.ext ?_ ?_
    · exact CuspidalL2GL.splitCentre_comm _ _
    · change 1 * x.2 = x.2 * 1
      rw [one_mul, mul_one]
  · refine Prod.ext ?_ (mul_one _).symm
    change splitCentre E n ((s + t) / _) = splitCentre E n (s / _) * splitCentre E n (t / _)
    rw [add_div, CuspidalL2GL.splitCentre_add]
  · refine Prod.ext ?_ rfl
    change splitCentre E n (0 / _) = 1
    rw [zero_div, CuspidalL2GL.splitCentre_zero]
  · exact (GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const
  · exact logAbs_det_theta x.1
  · exact Prod.ext ((thetaBasic_holds E n).2.1 x.1) ((thetaBasic_holds E 0).2.1 x.2)
  · exact Prod.ext (map_mul (thetaA E n) x.1 y.1) (map_mul (thetaA E 0) x.2 y.2)
  · rintro ⟨_, γ, rfl⟩
    refine ⟨Dcy.logAbs_ratGL' γ.1, ⟨(thetaE E n γ.1, thetaE E 0 γ.2), ?_⟩⟩
    exact Prod.ext ((thetaBasic_holds E n).2.2 γ.1).symm ((thetaBasic_holds E 0).2.2 γ.2).symm
  · exact (((thetaBasic_holds E n).1.comp continuous_fst).prodMk ((thetaBasic_holds E 0).1.comp continuous_snd))

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
