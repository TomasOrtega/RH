import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk
open GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
open GlobalTheory.CuspRep (Af)

/- English proof (translation)
Introduce `F _ _ _ s`. Use `⟨absChar F s, fun v => ?_⟩` and prove the remaining obligations. Use `TR.expo_eq_of_exp _ v s fun t => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _`. Establish `h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1` using `Units.ext (by`.

Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Use the proof step `simp)`. Establish `h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u)` using `fun u => by`. Establish `e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val`. Express the relevant statement in the definitionally equal form `1 - TR.infEq F 1 + TR.infEq F _ = _`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `(((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans (Real.norm_of_nonneg (Real.exp_pos _).le)`. Rewrite using `[logNorm, h1, logFin_one, logInf]`. Simplify using `[h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]`.
-/
theorem UpperTheory.V.Af.Gk.expoChar :
    UpperTheory.V.Af.Gk.ExpoChar := by
  intro F _ _ _ s
  refine ⟨absChar F s, fun v => ?_⟩
  classical
  refine TR.expo_eq_of_exp _ v s fun t => ?_
  change Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _
  have h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1 := Units.ext (by
    change (1 : Af F) - 0 + 0 = 1
    simp)
  have h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u) := fun u => by
    have e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val := by
      change 1 - TR.infEq F 1 + TR.infEq F _ = _
      simp
    rw [e]
    exact (((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  rw [logNorm, h1, logFin_one, logInf]
  simp [h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]
