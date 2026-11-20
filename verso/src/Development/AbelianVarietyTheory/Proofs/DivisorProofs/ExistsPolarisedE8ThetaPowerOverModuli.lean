import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegEighth

/- English proof (translation)
Establish `hS : (W + W.transpose).transpose = W + W.transpose`. Rewrite using `[Matrix.transpose_add, Matrix.transpose_transpose, add_comm]`. Establish `h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1` using `by rw [Matrix.mul_adjugate, hW.2, one_smul]`. Establish `h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1` using `by rw [Matrix.adjugate_mul, hW.2, one_smul]`. Set `e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))` to `{ twistSnd (W + W.transpose).adjugate with invFun := twistSnd (W + W.transpose) left_inv := twistSnd_twistSnd _ _ h1 right_inv := twistSnd_twistSnd _ _ h2 }`.

Use `⟨(sharpReindex h).trans e, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← sum_omegaStd_single h i j]`. Conclude with `sum_omegaStd_twistSnd _ _ hS h1 _ _`.
-/
theorem exists_isSharpBasis (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  have hS : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by rw [Matrix.mul_adjugate, hW.2, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by rw [Matrix.adjugate_mul, hW.2, one_smul]
  let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    { twistSnd (W + W.transpose).adjugate with
      invFun := twistSnd (W + W.transpose)
      left_inv := twistSnd_twistSnd _ _ h1
      right_inv := twistSnd_twistSnd _ _ h2 }
  refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd _ _ hS h1 _ _

/- English proof (translation)
Introduce `g n _ hn hno F W hW`. Establish `hn0 : n ≠ 0` using `by omega`. Set `b` to `cycBase hn0`. Set `c : SiegPre g n (b.ζ : cycAway n) (𝟙 F.X ≫ F.s)` to `GlobalTheory.LowChart.siegPull F.univ (𝟙 F.X) (𝟙 F.X ≫ F.s) rfl`. Establish `hc : c.Principal` using `GlobalTheory.LowChart.principal_siegPull F.univ _ _ rfl F.princ`.

Establish `hd : SmoothOfRelativeDimension g c.A.hom` using `SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit`. Establish `hpow : b.ζ ^ n = 1` using `Units.ext ((Units.val_pow_eq_pow_val _ _).trans (Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one))`. Take `⟨L₁, L₂⟩` from `abelianSchemeLaws_all`. Use `haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _`. Use `haveI : IsLocallyNoetherian (Sp (cycAway n)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))`.

Use `haveI := F.smooth`. Use `haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s`. Use `haveI : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s`. Take `⟨bas, hb⟩` from `exists_isSharpBasis g W hW`. Take `⟨a, w, w', hw, hw', hs⟩` from `EighthPowerFactor.exists_matrices hW.2`.

Take `⟨t, ⟨pr, hpr, hu, hL, -, -⟩, hp⟩` from `GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W _ a w w' bas hW hb hw hw' hs n (cycAway n) b F.X (𝟙 F.X ≫ F.s) c hpow hno hc hd`. Take `⟨r, hr⟩` from `t.rigid`. Conclude with `⟨t.pol, r, rfl, ⟨c, GlobalTheory.LowChart.siegPB_siegPull F.univ _ _ rfl, pr, hpr, hu, hL⟩, hr, t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩`.
-/
theorem exists_polAV_sharpOver : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  intro g n _ hn hno F W hW
  have hn0 : n ≠ 0 := by omega
  let b := cycBase hn0
  let c : SiegPre g n (b.ζ : cycAway n) (𝟙 F.X ≫ F.s) := GlobalTheory.LowChart.siegPull F.univ (𝟙 F.X) (𝟙 F.X ≫ F.s) rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ _ _ rfl F.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  have hpow : b.ζ ^ n = 1 :=
    Units.ext ((Units.val_pow_eq_pow_val _ _).trans (Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one))
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway n)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  obtain ⟨bas, hb⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨t, ⟨pr, hpr, hu, hL, -, -⟩, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W _ a w w'
    bas hW hb hw hw' hs n (cycAway n) b F.X (𝟙 F.X ≫ F.s) c hpow hno hc hd
  obtain ⟨r, hr⟩ := t.rigid
  exact ⟨t.pol, r, rfl, ⟨c, GlobalTheory.LowChart.siegPB_siegPull F.univ _ _ rfl, pr, hpr, hu, hL⟩, hr,
    t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩

end GlobalTheory.SiegEighth
