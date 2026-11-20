import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section
variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

/- English proof (translation)
Unfold `xInvM xA`. Rewrite using `[← map_mul]`. Establish `: ((fun π => (M.xC P π y)⁻¹) * fun π => M.xC P π y) = (1 : M.Ty P → ℂ)`. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.mul_apply, Pi.one_apply]`.

Conclude with `inv_mul_cancel₀ (hy π)`. Rewrite using `[this, map_one]`.
-/
theorem inverse_mul_regular_element {y : ℂ} (hy : RegY P y) : xInvM P y * xA P (DQ P) y = 1 := by
  unfold xInvM xA
  rw [← map_mul]
  have : ((fun π => (M.xC P π y)⁻¹) * fun π => M.xC P π y) = (1 : M.Ty P → ℂ) := by
    funext π; simp only [Pi.mul_apply, Pi.one_apply]; exact inv_mul_cancel₀ (hy π)
  rw [this, map_one]

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.MAx3.H.kap_comm_DG P g hz`.
-/
theorem jdr_kap_DG (g : M.Ty P → ℂ) {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P) :
    kap P (DQ P) g * z = z * kap P (DQ P) g := Formalism.FourierDecayAlt.P.MAx3.H.kap_comm_DG P g hz

/- English proof (translation)
Take `⟨w, rfl⟩` from `hz`. Conclude with `Formalism.FourierDecayAlt.P.MAx3.H.sc_memDG P w`.
-/
theorem jdr_SC_DG {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P) : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P := by
  obtain ⟨w, rfl⟩ := hz
  exact Formalism.FourierDecayAlt.P.MAx3.H.sc_memDG P w

end

/- English proof (translation)
Introduce `P L hL y hy`. Take `⟨hDr, hDrb, hDri, -⟩` from `Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL`. Establish `hGG : L.GG = ggA P (DQ P)` using `hL.2.2.2.2.2.2.2.2.2.2.1`. Establish `hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P` using `(Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1`. Establish `hl0 : L.l0 y = l0A P (DQ P) y`.

Take `⟨-, -, -, -, -, -, -, -, hzb, -, -, hgi, hn, -, -⟩` from `hL`. Simplify using `only [LevelData.l0, l0A, hn, hzb, hgi]`. Use `set X := xInvM P y with hXdef`. Use `set x := xA P (DQ P) y with hxdef`. Establish `hXx : X * x = 1` using `inverse_mul_regular_element hy`.

Establish `cD : X * L.Drb = L.Drb * X` using `jdr_kap_DG _ (jdr_SC_DG hDrb)`. Establish `cG : X * L.GG = L.GG * X` using `jdr_kap_DG _ (jdr_SC_DG hGGsc)`. Establish `hDriDr : L.Dri * L.Dr = 1`. Rewrite using `[Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDri L) (Formalism.FourierDecayAlt.P.MAx3.H.memDr L)]`. Conclude with `Formalism.FourierDecayAlt.P.MAx3.H.Dr_Dri' L`.

Establish `hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1), X * SSn P L l * kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y = X * L.Drb * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y`. Introduce `l _`. Establish `c1 : SS P (DQ P) l * L.Dr = L.Dr * SS P (DQ P) l` using `Formalism.FourierDecayAlt.P.MAx3.H.SS_comm_SC P l hDr`. Establish `c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y)` using `jdr_kap_DG _ (jdr_SC_DG hDr)`. Unfold `SSn LevelData.Ahat`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = X * L.Drb * (L.Dri * L.Dr) * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by`. Rewrite using `[c2, ← mul_assoc (SS P (DQ P) l), c1]`. Simplify using `only [mul_assoc]`.

Use `_ = _ := by rw [hDriDr, mul_one]`. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]`. Establish `hS21 : (∑ l ∈ Finset.Icc 1 (P.k - 1), SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) = weightedSumBis P (DQ P) y` using `rfl`. Rewrite using `[hS21]`. Establish `hR : X * RhM P L y = L.R0 y + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y`.

Unfold `RhM LevelData.R0 t21 t22`. Rewrite using `[hl0, hGG]`. Establish `e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P)`. Rewrite using `[← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]`. Establish `e2 : X * (ggA P (DQ P) * x * l0A P (DQ P) y) = ggA P (DQ P) * l0A P (DQ P) y`.

Rewrite using `[← mul_assoc X, e1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, cD, mul_assoc]`. Simplify using `only [mul_add, add_mul, mul_assoc]`. Use `_ = L.Drb * ggA P (DQ P) * (l0A P (DQ P) y * L.Ar y + L.Br y) + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by`.

Rewrite using `[e1, e2, cD]`. Simplify using `only [mul_add, add_mul, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[hR]`. Normalize the expressions using the abelian group laws.
-/
theorem residue_splitting_holds : ResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, hDri, -⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hl0 : L.l0 y = l0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hgi, hn, -, -⟩ := hL
    simp only [LevelData.l0, l0A, hn, hzb, hgi]
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Drb = L.Drb * X := jdr_kap_DG _ (jdr_SC_DG hDrb)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDriDr : L.Dri * L.Dr = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDri L) (Formalism.FourierDecayAlt.P.MAx3.H.memDr L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Dr_Dri' L

  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * SSn P L l * kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y =
        X * L.Drb * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
    intro l _
    have c1 : SS P (DQ P) l * L.Dr = L.Dr * SS P (DQ P) l := Formalism.FourierDecayAlt.P.MAx3.H.SS_comm_SC P l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    unfold SSn LevelData.Ahat
    calc X * (L.Drb * L.Dri * SS P (DQ P) l) * kap P (DQ P) (fun π => M.xEx P {l} π y) * (L.Dr * L.Ar y)
        = X * L.Drb * L.Dri * (SS P (DQ P) l * (kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr)) * L.Ar y := by
          simp only [mul_assoc]
      _ = X * L.Drb * (L.Dri * L.Dr) * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
          rw [c2, ← mul_assoc (SS P (DQ P) l), c1]; simp only [mul_assoc]
      _ = _ := by rw [hDriDr, mul_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS21 : (∑ l ∈ Finset.Icc 1 (P.k - 1), SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) =
      weightedSumBis P (DQ P) y := rfl
  rw [hS21]

  have hR : X * RhM P L y = L.R0 y + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
    unfold RhM LevelData.R0 t21 t22
    rw [hl0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * l0A P (DQ P) y) = ggA P (DQ P) * l0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Drb * ((ggA P (DQ P) * x * l0A P (DQ P) y + weightedSumBis P (DQ P) y) * L.Ar y + ggA P (DQ P) * x * L.Br y))
        = L.Drb * ((X * (ggA P (DQ P) * x * l0A P (DQ P) y) + X * weightedSumBis P (DQ P) y) * L.Ar y +
            X * (ggA P (DQ P) * x) * L.Br y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Drb * ggA P (DQ P) * (l0A P (DQ P) y * L.Ar y + L.Br y) + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

/- English proof (translation)
Introduce `P L hL y hy`. Take `⟨hDr, hDrb, -, hDrbi⟩` from `Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL`. Establish `hGG : L.GG = ggA P (DQ P)` using `hL.2.2.2.2.2.2.2.2.2.2.1`. Establish `hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P` using `(Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1`. Establish `hm0 : L.m0 y = m0A P (DQ P) y`.

Take `⟨-, -, -, -, -, -, hz, -, -, -, -, hgi, -, hns, -⟩` from `hL`. Simplify using `only [LevelData.m0, m0A, hns, hz, hgi]`. Establish `sDrb : star L.Drb = L.Dr`. Unfold `LevelData.Drb LevelData.Dr`. Rewrite using `[Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]`.

Establish `: (star ∘ L.cb) = L.c` using `funext fun l => by`. Take `⟨-, -, hc, -, hcb, -⟩` from `hL`. Use `show star (L.cb l) = L.c l`. Rewrite using `[hcb, hc]`. Simplify using `only [cbA, cA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`.

Both sides reduce to the same expression. Rewrite using `[this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]`. Introduce `x hx`. Take `⟨l, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_c L l)`.

Establish `sDri : star L.Dri = L.Drbi`. Unfold `LevelData.Dri LevelData.Drbi`. Rewrite using `[Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]`. Establish `: (star ∘ L.ci) = L.cbi` using `funext fun l => by`. Take `⟨-, -, -, hci, -, hcbi, -⟩` from `hL`.

Use `show star (L.ci l) = L.cbi l`. Rewrite using `[hci, hcbi]`. Simplify using `only [ciA, cbiA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Both sides reduce to the same expression. Rewrite using `[this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]`.

Introduce `x hx`. Take `⟨l, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_cbi L l)`. Use `set X := xInvM P y with hXdef`. Use `set x := xA P (DQ P) y with hxdef`.

Establish `hXx : X * x = 1` using `inverse_mul_regular_element hy`. Establish `cD : X * L.Dr = L.Dr * X` using `jdr_kap_DG _ (jdr_SC_DG hDr)`. Establish `cG : X * L.GG = L.GG * X` using `jdr_kap_DG _ (jdr_SC_DG hGGsc)`. Establish `hDrbiDrb : L.Drbi * L.Drb = 1`. Rewrite using `[Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDrbi L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)]`.

Conclude with `Formalism.FourierDecayAlt.P.MAx3.H.Drb_Drbi' L`. Establish `cDD : L.Dr * L.Drb = L.Drb * L.Dr` using `Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDr L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)`. Establish `hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1), X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y = X * L.Dr * (kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) * L.Avr y`. Introduce `l _`. Establish `c1 : star (SS P (DQ P) l) * L.Dr = L.Dr * star (SS P (DQ P) l)` using `Formalism.FourierDecayAlt.P.MAx3.H.SSs_comm_SC l hDr`.

Establish `c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y)` using `jdr_kap_DG _ (jdr_SC_DG hDr)`. Establish `hs : star (SSn P L l) = star (SS P (DQ P) l) * L.Drbi * L.Dr`. Unfold `SSn`. Rewrite using `[star_mul, star_mul, sDri, sDrb, mul_assoc]`. Rewrite using `[hs]`.

Unfold `LevelData.Ahatv`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cDD, ← mul_assoc L.Drbi, hDrbiDrb, one_mul]`. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [c1, ← mul_assoc (kap P (DQ P) _), c2]; simp only [mul_assoc]`.

Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]`. Establish `hS12 : (∑ l ∈ Finset.Icc 1 (P.k - 1), kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) = S12 P (DQ P) y` using `rfl`. Rewrite using `[hS12]`. Establish `hR : X * RhvM P L y = L.R0v y + X * L.Dr * S12 P (DQ P) y * L.Avr y`. Unfold `RhvM LevelData.R0v t12 t22`.

Rewrite using `[hm0, hGG]`. Establish `e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P)`. Rewrite using `[← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]`. Establish `e2 : X * (ggA P (DQ P) * x * m0A P (DQ P) y) = ggA P (DQ P) * m0A P (DQ P) y`. Rewrite using `[← mul_assoc X, e1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, cD, mul_assoc]`. Simplify using `only [mul_add, add_mul, mul_assoc]`. Use `_ = L.Dr * ggA P (DQ P) * (m0A P (DQ P) y * L.Avr y + L.Bvr y) + X * L.Dr * S12 P (DQ P) y * L.Avr y := by`. Rewrite using `[e1, e2, cD]`.

Simplify using `only [mul_add, add_mul, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[hR]`. Normalize the expressions using the abelian group laws.
-/
theorem mirror_residue_splitting_holds : MirrorResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, -, hDrbi⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hm0 : L.m0 y = m0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hgi, -, hns, -⟩ := hL
    simp only [LevelData.m0, m0A, hns, hz, hgi]
  have sDrb : star L.Drb = L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.cb) = L.c := funext fun l => by
      obtain ⟨-, -, hc, -, hcb, -⟩ := hL
      show star (L.cb l) = L.c l
      rw [hcb, hc]
      simp only [cbA, cA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_c L l)
  have sDri : star L.Dri = L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.ci) = L.cbi := funext fun l => by
      obtain ⟨-, -, -, hci, -, hcbi, -⟩ := hL
      show star (L.ci l) = L.cbi l
      rw [hci, hcbi]
      simp only [ciA, cbiA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_cbi L l)
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Dr = L.Dr * X := jdr_kap_DG _ (jdr_SC_DG hDr)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDrbiDrb : L.Drbi * L.Drb = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDrbi L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Drb_Drbi' L
  have cDD : L.Dr * L.Drb = L.Drb * L.Dr :=
    Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDr L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)
  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y =
        X * L.Dr * (kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) * L.Avr y := by
    intro l _
    have c1 : star (SS P (DQ P) l) * L.Dr = L.Dr * star (SS P (DQ P) l) := Formalism.FourierDecayAlt.P.MAx3.H.SSs_comm_SC l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    have hs : star (SSn P L l) = star (SS P (DQ P) l) * L.Drbi * L.Dr := by
      unfold SSn; rw [star_mul, star_mul, sDri, sDrb, mul_assoc]
    rw [hs]
    unfold LevelData.Ahatv
    calc X * kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Drbi * L.Dr) * (L.Drb * L.Avr y)
        = X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l) * (L.Drbi * (L.Dr * L.Drb)) *
            L.Avr y := by simp only [mul_assoc]
      _ = X * (kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Dr)) * L.Avr y := by
          rw [cDD, ← mul_assoc L.Drbi, hDrbiDrb, one_mul]; simp only [mul_assoc]
      _ = _ := by rw [c1, ← mul_assoc (kap P (DQ P) _), c2]; simp only [mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS12 : (∑ l ∈ Finset.Icc 1 (P.k - 1), kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) =
      S12 P (DQ P) y := rfl
  rw [hS12]
  have hR : X * RhvM P L y = L.R0v y + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
    unfold RhvM LevelData.R0v t12 t22
    rw [hm0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * m0A P (DQ P) y) = ggA P (DQ P) * m0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Dr * ((ggA P (DQ P) * x * m0A P (DQ P) y + S12 P (DQ P) y) * L.Avr y + ggA P (DQ P) * x * L.Bvr y))
        = L.Dr * ((X * (ggA P (DQ P) * x * m0A P (DQ P) y) + X * S12 P (DQ P) y) * L.Avr y +
            X * (ggA P (DQ P) * x) * L.Bvr y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Dr * ggA P (DQ P) * (m0A P (DQ P) y * L.Avr y + L.Bvr y) + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

end

end Formalism.FourierDecayAlt.P.CutMP
