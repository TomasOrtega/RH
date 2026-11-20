import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section casts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def castBS {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : B.RealPlaceData k b Wp Wq := e ▸ Bs

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem castBS_z_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z = D.castV e Bs.z := by
  subst e
  rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem castBS_z'_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z' = D.castV e Bs.z' := by
  subst e
  rfl

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `h`.
-/
theorem cptCoef_castF {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) (G : B.Mat k b → (Wq →L[ℂ] Wp))
    (h : KB.CptCoef (castBS e Bs) G) : KB.CptCoef Bs (D.castF e G) := by
  subst e
  exact h

end casts

/- English proof (translation)
Substitute `hρ` using the available equality. Conclude with `Formalism.FourierDecayAlt.P.JCx2.sq_glev0 g`.
-/
theorem glev_last_iff {k ρ : ℕ} (hρ : ρ = 0) (g : B.Mat k ρ) :
    g ∈ Q.Glev k ρ (Fin.last ρ) ↔ g ∈ B.GV k ρ := by
  subst hρ
  exact Formalism.FourierDecayAlt.P.JCx2.sq_glev0 g

/- English proof (translation)
Substitute `hρ` using the available equality. Establish `h0 : Dmin k 0 z z' g ⟨0, by omega⟩ = 1`. Unfold `Dmin`. Conclude with `Matrix.det_isEmpty`. Establish `h1 : Dmin k 0 z z' g (Fin.last 1) = Zhat k 0 z z' g (Fin.last 0) (Fin.last 0)`.

Unfold `Dmin`. Conclude with `Matrix.det_fin_one _`. Unfold `Gf Q.GGl`. Rewrite using `[Formalism.FourierDecayAlt.P.PBI.zetaL_eq_zhat, h0, h1]`. Simplify using the standard rewrite rules.
-/
theorem gf_eq_ggl {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  have h0 : Dmin k 0 z z' g ⟨0, by omega⟩ = 1 := by
    unfold Dmin
    exact Matrix.det_isEmpty
  have h1 : Dmin k 0 z z' g (Fin.last 1) = Zhat k 0 z z' g (Fin.last 0) (Fin.last 0) := by
    unfold Dmin
    exact Matrix.det_fin_one _
  unfold Gf Q.GGl
  rw [Formalism.FourierDecayAlt.P.PBI.zetaL_eq_zhat, h0, h1]
  simp

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Establish `hzl` using `(T.z_lev r le_rfl).symm`. Express the relevant statement in the definitionally equal form `T.base.z = _ at hzl`. Rewrite using `[hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _`.
-/
theorem lowV_top {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z) = (T.bs r).z := by
  have hzl := (T.z_lev r le_rfl).symm
  change T.base.z = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

/- English proof (translation)
Establish `hzl` using `(T.z'_lev r le_rfl).symm`. Express the relevant statement in the definitionally equal form `T.base.z' = _ at hzl`. Rewrite using `[hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _`.
-/
theorem lowV_top' {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z') = (T.bs r).z' := by
  have hzl := (T.z'_lev r le_rfl).symm
  change T.base.z' = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

end top

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p b b' hb hbc hb' hb'c Φ hΦ K hK hKU hsupp`. Establish `hρ : P.r - P.r = 0` using `Nat.sub_self _`. Establish `e : P.r = P.r + (P.r - P.r)` using `by omega`. Establish `hz : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z = (p.T.bs P.r).z`. Rewrite using `[castBS_z_eq_castV]`.

Conclude with `lowV_top p.T e`. Establish `hz' : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z' = (p.T.bs P.r).z'`. Rewrite using `[castBS_z'_eq_castV]`. Conclude with `lowV_top' p.T e`. Establish `hUTo : IsOpen (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')`.

Establish `c1 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det)` using `Continuous.matrix_det continuous_fst`. Establish `c2 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of q.2))` using `(Formalism.FourierDecayAlt.P.Qx5.GGl_continuous _ _ _ _).comp continuous_snd`. Conclude with `(isOpen_ne_fun c1 continuous_const).inter (isOpen_lt continuous_const c2)`. Establish `hCpt : KB.CptCoef (castBS e p.T.base) (PBI.chartCoefficient b b' Φ)`. Use `PBI.chartCoefficient_hasCompactSupport (castBS e p.T.base) b b' hb hbc hb' hb'c Φ (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') hUTo ?_ K hK hKU ?_ ?_` and prove the remaining obligations.

Introduce `q₀ hq₀ hG`. Take `⟨U', F, hU', hq, hF, hEq⟩` from `hΦ q₀ hq₀ ((glev_last_iff hρ _).2 hG)`. Conclude with `⟨U', F, hU', hq, hF, fun q hqU hqG => hEq q hqU ((glev_last_iff hρ _).2 hqG)⟩`. Introduce `q hq`. Take `⟨h1, h2⟩` from `hKU hq`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hz', gf_eq_ggl hρ]`. Conclude with `h2`. Introduce `q hG hq`. Conclude with `hsupp q ((glev_last_iff hρ _).2 hG) hq`.

Use `⟨cptCoef_castF e p.T.base _ hCpt, (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) '' K, hK.image (Continuous.matrix_det continuous_fst), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨q, hq, h0⟩`. Conclude with `(hKU hq).1 h0`. Introduce `g hg hne`. Establish `hg' : D.castM e g ∈ B.GV P.k (P.r + (P.r - P.r))` using `Formalism.FourierDecayAlt.P.PBE.castM_GV e hg`.

Establish `hne' : PBI.chartCoefficient b b' Φ (D.castM e g) ≠ 0` using `hne`. Establish `hD : U.DjU P.k P.r (P.r - P.r) (D.castM e g) ≠ 0`. Introduce `h0`. Apply `hne'` to reduce the goal to its premises. Unfold `PBI.chartCoefficient`.

Rewrite using `[if_neg (not_not.2 h0)]`. Take `⟨-, hμ, heq⟩` from `PBI.chart_spec (D.castM e g) hg' hD`. Establish `hmk` using `hne'`. Unfold `PBI.chartCoefficient at hmk`. Rewrite `hmk` using `[if_pos hD]`.

Take `⟨-, hΦne⟩` from `smul_ne_zero_iff.1 hmk`. Establish `hμ' : Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.2 ∈ B.GV P.k (P.r - P.r)`. Simplify `hμ` using `[PBI.chart]`. Establish `hK' : (PBI.chart (Matrix.of.symm (D.castM e g))).2 ∈ K`. Assume the negation of the conclusion as `hn`.

Conclude with `hΦne (hsupp _ ((glev_last_iff hρ _).2 hμ') hn)`. Use `⟨_, hK', ?_⟩` and prove the remaining obligations. Establish `hpsi : PBI.psiC (PBI.chart (Matrix.of.symm (D.castM e g))) = D.castM e g`. Unfold `PBI.psiC PBI.chart`. Simplify using `only [Equiv.apply_symm_apply]`.

Conclude with `heq.symm`. Establish `e1` using `PBI.djU_psiC (PBI.chart (Matrix.of.symm (D.castM e g)))`. Rewrite `e1` using `[hpsi]`. Use `show (Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.1).det = _`. Rewrite using `[← e1, ← Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r) (D.castV e p.T.base.z) (D.castV e p.T.base.z'), Formalism.FourierDecayAlt.P.PBG.Dmin_castM e _ _ g P.r, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Fo …`.
-/
theorem mkCpt : MkCpt := by
  intro Wp Wq _ _ _ _ _ _ P p b b' hb hbc hb' hb'c Φ hΦ K hK hKU hsupp
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  have e : P.r = P.r + (P.r - P.r) := by omega
  have hz : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z = (p.T.bs P.r).z := by
    rw [castBS_z_eq_castV]; exact lowV_top p.T e
  have hz' : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z' = (p.T.bs P.r).z' := by
    rw [castBS_z'_eq_castV]; exact lowV_top' p.T e
  have hUTo : IsOpen (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') := by
    have c1 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) :=
      Continuous.matrix_det continuous_fst
    have c2 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) =>
        Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of q.2)) :=
      (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous _ _ _ _).comp continuous_snd
    exact (isOpen_ne_fun c1 continuous_const).inter (isOpen_lt continuous_const c2)
  have hCpt : KB.CptCoef (castBS e p.T.base) (PBI.chartCoefficient b b' Φ) := by
    refine PBI.chartCoefficient_hasCompactSupport (castBS e p.T.base) b b' hb hbc hb' hb'c Φ (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      hUTo ?_ K hK hKU ?_ ?_
    · intro q₀ hq₀ hG
      obtain ⟨U', F, hU', hq, hF, hEq⟩ := hΦ q₀ hq₀ ((glev_last_iff hρ _).2 hG)
      exact ⟨U', F, hU', hq, hF, fun q hqU hqG => hEq q hqU ((glev_last_iff hρ _).2 hqG)⟩
    · intro q hq
      obtain ⟨h1, h2⟩ := hKU hq
      refine ⟨h1, ?_⟩
      rw [hz, hz', gf_eq_ggl hρ]
      exact h2
    · intro q hG hq
      exact hsupp q ((glev_last_iff hρ _).2 hG) hq
  refine ⟨cptCoef_castF e p.T.base _ hCpt,
    (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) '' K,
    hK.image (Continuous.matrix_det continuous_fst), ?_, ?_⟩
  · rintro ⟨q, hq, h0⟩
    exact (hKU hq).1 h0
  · intro g hg hne
    have hg' : D.castM e g ∈ B.GV P.k (P.r + (P.r - P.r)) := Formalism.FourierDecayAlt.P.PBE.castM_GV e hg
    have hne' : PBI.chartCoefficient b b' Φ (D.castM e g) ≠ 0 := hne
    have hD : U.DjU P.k P.r (P.r - P.r) (D.castM e g) ≠ 0 := by
      intro h0; apply hne'; unfold PBI.chartCoefficient; rw [if_neg (not_not.2 h0)]
    obtain ⟨-, hμ, heq⟩ := PBI.chart_spec (D.castM e g) hg' hD
    have hmk := hne'
    unfold PBI.chartCoefficient at hmk
    rw [if_pos hD] at hmk
    obtain ⟨-, hΦne⟩ := smul_ne_zero_iff.1 hmk
    have hμ' : Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.2 ∈ B.GV P.k (P.r - P.r) := by
      simpa [PBI.chart] using hμ
    have hK' : (PBI.chart (Matrix.of.symm (D.castM e g))).2 ∈ K := by
      by_contra hn
      exact hΦne (hsupp _ ((glev_last_iff hρ _).2 hμ') hn)
    refine ⟨_, hK', ?_⟩
    have hpsi : PBI.psiC (PBI.chart (Matrix.of.symm (D.castM e g))) = D.castM e g := by
      unfold PBI.psiC PBI.chart
      simp only [Equiv.apply_symm_apply]
      exact heq.symm
    have e1 := PBI.djU_psiC (PBI.chart (Matrix.of.symm (D.castM e g)))
    rw [hpsi] at e1
    show (Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.1).det = _
    rw [← e1, ← Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r) (D.castV e p.T.base.z) (D.castV e p.T.base.z'),
      Formalism.FourierDecayAlt.P.PBG.Dmin_castM e _ _ g P.r, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV,
      Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `CutEX.MkCptPf.mkCpt`.
-/
theorem compact_truncation_construction : CutEX.MkCpt := CutEX.MkCptPf.mkCpt

end Formalism.FourierDecayAlt.P
