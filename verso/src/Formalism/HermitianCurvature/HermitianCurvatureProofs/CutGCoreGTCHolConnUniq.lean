import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X d hyp e he A B A' B' hAB hAB' hC hC' ρ ζ hζ`. Take `⟨Φ, hΦ, -⟩` from `SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))`. Establish `h1` using `(hC Φ ρ).1`. Establish `h2` using `(hC' Φ ρ).1`. Rewrite `h1`, `h2` using `[hΦ]`.

Simplify using `only [mul_one] at h1 h2`. Establish `h3 : fnZ P (A ρ) = fnZ P (A' ρ)`. Use `h1.symm.trans h2` as an intermediate fact. Conclude with `add_left_cancel this`. Rewrite `h3` using `[fnZ_eq_mk P (hAB ρ).1, fnZ_eq_mk P (hAB' ρ).1]`.

Establish `hq : ((fun _ => (1 : ℂ), ζ) : (Fin P.r → ℂ) × ℂ) ∈ MA.Qset P.r P.TT` using `⟨fun _ => one_ne_zero, hζ⟩`. Use `congrFun (congrArg Subtype.val h3) ⟨_, hq⟩` as an intermediate fact. Conclude with `this`.
-/
theorem connection_uniqueness_holds : GTCConnUniq := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he A B A' B' hAB hAB' hC hC' ρ ζ hζ
  obtain ⟨Φ, hΦ, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have h1 := (hC Φ ρ).1
  have h2 := (hC' Φ ρ).1
  rw [hΦ] at h1 h2
  simp only [mul_one] at h1 h2
  have h3 : fnZ P (A ρ) = fnZ P (A' ρ) := by
    have := h1.symm.trans h2
    exact add_left_cancel this
  rw [fnZ_eq_mk P (hAB ρ).1, fnZ_eq_mk P (hAB' ρ).1] at h3
  have hq : ((fun _ => (1 : ℂ), ζ) : (Fin P.r → ℂ) × ℂ) ∈ MA.Qset P.r P.TT :=
    ⟨fun _ => one_ne_zero, hζ⟩
  have := congrFun (congrArg Subtype.val h3) ⟨_, hq⟩
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
