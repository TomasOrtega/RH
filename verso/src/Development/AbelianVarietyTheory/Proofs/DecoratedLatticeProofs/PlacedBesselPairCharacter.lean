import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterMtEqSmulOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntLocIffValBar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZero
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTv`. Establish `hm : 0 < D.R.m` using `by have := D.R.rS_two; omega`. Take `⟨hsd, hfr⟩` from `GlobalTheory.Fam.sdY_frames W hW 0 hm`. Establish `hFG : ((pk W).ΛY 0).FG` using `hsd.1.fg`. Establish `hkSt : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((pk W).βY 0)` using `Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)`.

Establish `hkM : Moves (D.sp.Y 0) k ((pk W).ΛY 0) ((pk W).ΛY 0) (· = v)` using `(GlobalTheory.StMoves.moves_iff_stabLoc _ _ hFG v k).2 ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ _ hfr k).1 hkSt v)`. Take `⟨c, hc⟩` from `GlobalTheory.CenterScalar.center_mt_eq_smul_one D (D.sp.Y 0) z⁻¹ (Subgroup.inv_mem _ hzc)`. Establish `hmul : ∀ g h : GA D (D.sp.Y 0), Formalism.L2.Theta.mt _ (g * h) = Formalism.L2.Theta.mt _ g * Formalism.L2.Theta.mt _ h` using `fun g h => by simp [Formalism.L2.Theta.mt, map_mul]`. Establish `hone : Formalism.L2.Theta.mt (D.sp.Y 0) 1 = 1` using `by simp [Formalism.L2.Theta.mt, map_one]`. Establish `h3` using `GlobalTheory.T.placed_bessel_translate_vector W hW hr u f B hP a₀ a hA`.

Establish `h3'` using `GlobalTheory.T.placed_bessel_translate_vector W hW hr u' f' B' hP' a₀' a' hA'`. Establish `h4` using `GlobalTheory.T.placed_bessel_pair_vector W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' v hv hTv`. Establish `h5` using `GlobalTheory.coord_first_isotropic_ne_zero W.S.X W.Q.instEq hr`. Generalize the expression as in `tOf f B a₀ a = t at he h3`. Generalize the expression as in `tOf f' B' a₀' a' = t' at he h3'`.

Establish `hunit : IsUnit (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹)` using `⟨⟨Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹, Formalism.L2.Theta.mt (D.sp.Y 0) t', by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩, rfl⟩`. Establish `hkey : t'⁻¹ * z⁻¹ = k * t⁻¹` using `by rw [he]; group`. Establish `hMinv : Moves (D.sp.Y 0) z⁻¹ ((pk W).ΛY 0) ((pk W).ΛY 0) (· = v)`. Introduce `y hy`. Rewrite using `[hc, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Use `GlobalTheory.LineUnit.smul_mem_latV_iff D (D.sp.Y 0) _ hsd.1 v _ h5 c _ hunit ?_ y hy` and prove the remaining obligations. Introduce `b hb`. Establish `h3b` using `h3 b`. Establish `h3b'` using `h3' b`. Establish `h4b` using `h4 b hb`.

Generalize the expression as in `hw : (fun i => b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = w at h3b h3b' h4b`. Establish `hsupp : ∀ i, w i ∈ GlobalTheory.FinPl.idAt D (· = v)` using `fun i => by`. Rewrite using `[← hw]`. Conclude with `Ideal.mul_mem_right _ _ hb`. Establish `e1 : (fun i => c * (b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w`.

Rewrite using `[← hw, hc, Matrix.smul_mulVec, Matrix.one_mulVec]`. Both sides reduce to the same expression. Establish `s1 : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) k) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t⁻¹) w)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul, hkey]`. Establish `s2` using `hkM _ (GlobalTheory.FinPl.KOpen.supp_mulVec _ _ t⁻¹ hsupp)`.

Rewrite using `[e1, s1, ← s2, h3b, h3b']`. Conclude with `h4b`. Establish `hM` using `GlobalTheory.StMoves.moves_inv hMinv`. Rewrite `hM` using `[inv_inv]`. Conclude with `(GlobalTheory.StMoves.moves_iff_stabLoc (D.sp.Y 0) _ hFG v z).1 hM`.
-/
theorem centralRatio_stab_atT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTv
  have hm : 0 < D.R.m := by have := D.R.rS_two; omega
  obtain ⟨hsd, hfr⟩ := GlobalTheory.Fam.sdY_frames W hW 0 hm
  have hFG : ((pk W).ΛY 0).FG := hsd.1.fg
  have hkSt : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((pk W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkM : Moves (D.sp.Y 0) k ((pk W).ΛY 0) ((pk W).ΛY 0) (· = v) :=
    (GlobalTheory.StMoves.moves_iff_stabLoc _ _ hFG v k).2
      ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ _ hfr k).1 hkSt v)
  obtain ⟨c, hc⟩ := GlobalTheory.CenterScalar.center_mt_eq_smul_one D (D.sp.Y 0) z⁻¹ (Subgroup.inv_mem _ hzc)
  have hmul : ∀ g h : GA D (D.sp.Y 0), Formalism.L2.Theta.mt _ (g * h) = Formalism.L2.Theta.mt _ g * Formalism.L2.Theta.mt _ h :=
    fun g h => by simp [Formalism.L2.Theta.mt, map_mul]
  have hone : Formalism.L2.Theta.mt (D.sp.Y 0) 1 = 1 := by simp [Formalism.L2.Theta.mt, map_one]
  have h3 := GlobalTheory.T.placed_bessel_translate_vector W hW hr u f B hP a₀ a hA
  have h3' := GlobalTheory.T.placed_bessel_translate_vector W hW hr u' f' B' hP' a₀' a' hA'
  have h4 := GlobalTheory.T.placed_bessel_pair_vector W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' v hv hTv
  have h5 := GlobalTheory.coord_first_isotropic_ne_zero W.S.X W.Q.instEq hr
  generalize tOf f B a₀ a = t at he h3
  generalize tOf f' B' a₀' a' = t' at he h3'
  have hunit : IsUnit (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) :=
    ⟨⟨Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹, Formalism.L2.Theta.mt (D.sp.Y 0) t', by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩, rfl⟩
  have hkey : t'⁻¹ * z⁻¹ = k * t⁻¹ := by rw [he]; group
  have hMinv : Moves (D.sp.Y 0) z⁻¹ ((pk W).ΛY 0) ((pk W).ΛY 0) (· = v) := by
    intro y hy
    rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    refine GlobalTheory.LineUnit.smul_mem_latV_iff D (D.sp.Y 0) _ hsd.1 v _ h5 c _ hunit ?_ y hy
    intro b hb
    have h3b := h3 b
    have h3b' := h3' b
    have h4b := h4 b hb
    generalize hw : (fun i => b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = w at h3b h3b' h4b
    have hsupp : ∀ i, w i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => by
      rw [← hw]; exact Ideal.mul_mem_right _ _ hb
    have e1 : (fun i => c * (b * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w := by
      rw [← hw, hc, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl
    have s1 : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t'⁻¹) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) z⁻¹) w) =
        Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) k) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) t⁻¹) w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul, hkey]
    have s2 := hkM _ (GlobalTheory.FinPl.KOpen.supp_mulVec _ _ t⁻¹ hsupp)
    rw [e1, s1, ← s2, h3b, h3b']
    exact h4b
  have hM := GlobalTheory.StMoves.moves_inv hMinv
  rw [inv_inv] at hM
  exact (GlobalTheory.StMoves.moves_iff_stabLoc (D.sp.Y 0) _ hFG v z).1 hM

end GlobalTheory.MiTop
