import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLQOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDGqRes

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D X Y hX hY hxy g hg`. Take `⟨p, hp, hq, hge⟩` from `Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg`. Use `set q := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' g with hqdef`. Establish `hgq` using `Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq`. Take `⟨x, hxD, w, hw, hres⟩` from `radial_group_residue k r Wp Wq D q hq`.

Establish `hxe : X (B.gq D q) = Y (B.gq D q)`. Establish `e` using `rdsp_resG_congr X Y x (hxy x hxD)`. Rewrite `e` using `[hres X hX, hres Y hY]`. Conclude with `smul_right_injective _ hw e`. Establish `hD : ∀ y ∈ JF.Om k r D.z D.z', y ∈ Q.Glev k r 0 ∩ JF.Om k r D.z D.z'` using `fun y hy => ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, hy⟩`.

Establish `hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0` using `fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩`. Rewrite using `[hge]`. Conclude with `Formalism.FourierDecayAlt.P.CutMP.JA.LT.agree_sgs D X Y (fun y hy n hn => hX.2.1 y (hD y hy) n (hNl n hn)) (fun y hy n hn => hX.2.2.1 y (hD y hy) n (hNl n hn)) (fun y hy h hh h' hh' => hX.2.2.2 y (hD y hy) h hh h' hh') (fun y hy n hn => hY.2.1 y (hD y hy) n (hNl n hn)) (fun y hy …`.
-/
theorem spectral_pairing_zero_right : RDSPZeroR := by
  intro k r Wp Wq _ _ _ _ _ _ D X Y hX hY hxy g hg
  obtain ⟨p, hp, hq, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
  set q := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' g with hqdef
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨x, hxD, w, hw, hres⟩ := radial_group_residue k r Wp Wq D q hq
  have hxe : X (B.gq D q) = Y (B.gq D q) := by
    have e := rdsp_resG_congr X Y x (hxy x hxD)
    rw [hres X hX, hres Y hY] at e
    exact smul_right_injective _ hw e
  have hD : ∀ y ∈ JF.Om k r D.z D.z', y ∈ Q.Glev k r 0 ∩ JF.Om k r D.z D.z' := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  rw [hge]
  exact Formalism.FourierDecayAlt.P.CutMP.JA.LT.agree_sgs D X Y
    (fun y hy n hn => hX.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hX.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hX.2.2.2 y (hD y hy) h hh h' hh')
    (fun y hy n hn => hY.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hY.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hY.2.2.2 y (hD y hy) h hh h' hh')
    hp hgq hxe

end Formalism.FourierDecayAlt.P.CutSE
