import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Decay

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `: IsModuleTopology (Ainf F) (Ainf F ⊗[F] E)` using `⟨rfl⟩`. Unfold `sizeInf`. Use `continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_` and prove the remaining obligations. Establish `hk : Continuous fun y : Ainf F ⊗[F] E => (Algebra.TensorProduct.basis (Ainf F) b).coord k y` using `IsModuleTopology.continuous_of_linearMap _`. Simplify using `only [← Module.Basis.coord_apply]`.

Conclude with `continuous_norm.comp ((continuous_apply v).comp hk)`.
-/
theorem continuous_sizeInf {d : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

/- English proof (translation)
Unfold `sizeTup`. Use `continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(continuous_sizeInf b).comp ((continuous_apply i).comp (continuous_apply a))`.
-/
theorem continuous_sizeTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup (M := M) (n := n) b) := by
  unfold sizeTup
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
  exact (continuous_sizeInf b).comp ((continuous_apply i).comp (continuous_apply a))

/- English proof (translation)
Introduce `N`. Establish `hcont : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N` using `(continuous_norm.comp hc).mul ((continuous_const.add (continuous_sizeTup b)).pow N)`. Establish `hsupp : HasCompactSupport fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N` using `hs.norm.mul_right`. Take `⟨C, hC⟩` from `hcont.bounded_above_of_compact_support hsupp`. Conclude with `⟨C, fun X => le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC X)⟩`.
-/
theorem rapidDecay_of_compact {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    RapidDecay b Φ := by
  intro N
  have hcont : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    (continuous_norm.comp hc).mul ((continuous_const.add (continuous_sizeTup b)).pow N)
  have hsupp : HasCompactSupport fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hs.norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨C, fun X => le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC X)⟩

end Decay

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν Φ hΦ`. Take `⟨d, b, Φinf, Φf, Φv, hci, hsi, hpf, hpr, hsm⟩` from `hΦ`. Establish `hS` using `hc a ha2 (gramE σ J X0) hT hdet d b Φ Φinf Φf Φv hci (rapidDecay_of_compact b Φinf hci hsi) hsm hpf hpr`. Take `⟨_, hν2⟩` from `hν`. Take `⟨μinf, hμinf⟩` from `hν2.1`.

Establish `hν3` using `hν2.2 μinf hμinf`. Take `⟨νinf, hνinf⟩` from `hν3.1`. Establish `hν4` using `hν3.2 νinf hνinf`. Take `⟨μv, hμv⟩` from `hν4.1`. Establish `hν5` using `hν4.2 μv hμv`.

Take `⟨νv, hνv⟩` from `hν5.1`. Establish `hν6` using `hν5.2 νv hνv`. Take `⟨fibInf, hfibInf⟩` from `hν6.1`. Establish `hν7` using `hν6.2 fibInf hfibInf`. Take `⟨fibV, hfibV⟩` from `hν7.1`.

Establish `hν8` using `hν7.2 fibV hfibV d b Φ Φinf Φf Φv hci hsi hpf hpr`. Take `⟨ginf, gv, hdi, hdv, _, hmean⟩` from `(((((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv)`. Establish `hmean' : meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = gramE σ J X0}) = ginf (hermOf (Ainf F) σ (gramE σ J X0) hT) * ∏' v, gv v (hermOf (Fv F v) σ (gramE σ J X0) hT)` using `hmean`. Rewrite using `[hmean', hν8.2.2, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfibInf Φinf ginf hci hsi hdi]`. Use `congr 1`.

Conclude with `tprod_congr fun v => h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hpf.1 v) (hdv v)`.
-/
theorem sWeqOm_of (h1 : DensFibInf) (h2 : DensFibV) : SWeqOm := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν Φ hΦ
  obtain ⟨d, b, Φinf, Φf, Φv, hci, hsi, hpf, hpr, hsm⟩ := hΦ
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b Φ Φinf Φf Φv hci
    (rapidDecay_of_compact b Φinf hci hsi) hsm hpf hpr
  obtain ⟨_, hν2⟩ := hν
  obtain ⟨μinf, hμinf⟩ := hν2.1
  have hν3 := hν2.2 μinf hμinf
  obtain ⟨νinf, hνinf⟩ := hν3.1
  have hν4 := hν3.2 νinf hνinf
  obtain ⟨μv, hμv⟩ := hν4.1
  have hν5 := hν4.2 μv hμv
  obtain ⟨νv, hνv⟩ := hν5.1
  have hν6 := hν5.2 νv hνv
  obtain ⟨fibInf, hfibInf⟩ := hν6.1
  have hν7 := hν6.2 fibInf hfibInf
  obtain ⟨fibV, hfibV⟩ := hν7.1
  have hν8 := hν7.2 fibV hfibV d b Φ Φinf Φf Φv hci hsi hpf hpr
  obtain ⟨ginf, gv, hdi, hdv, _, hmean⟩ :=
    (((((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv)
  have hmean' : meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = gramE σ J X0}) =
      ginf (hermOf (Ainf F) σ (gramE σ J X0) hT) *
        ∏' v, gv v (hermOf (Fv F v) σ (gramE σ J X0) hT) := hmean
  rw [hmean', hν8.2.2, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
    fibInf hfibInf Φinf ginf hci hsi hdi]
  congr 1
  exact tprod_congr fun v => h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hpf.1 v) (hdv v)

end PI.VolStabS
