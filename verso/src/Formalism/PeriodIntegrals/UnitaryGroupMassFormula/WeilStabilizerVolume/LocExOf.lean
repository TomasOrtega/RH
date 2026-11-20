import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.SWeqOm

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μv hμv νv hνv fibV hfibV d b Φf Φv hp`. Establish `hS` using `hc a ha2 (gramE σ J X0) hT hdet d b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) Φf Φv continuous_const (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)`. Take `⟨μ, hμ⟩` from `hS.1`. Take `⟨𝓕, h𝓕⟩` from `(hS.2 μ hμ).1`. Establish `h3` using `((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ`.

Take `⟨μinf, hμinf⟩` from `h3.1`. Take `⟨νinf, hνinf⟩` from `(h3.2 μinf hμinf).1`. Take `⟨ginf, gv, _, hdv, hm, _⟩` from `(((h3.2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv`. Use `hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`.

Conclude with `(h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hp.1 v) (hdv v)).symm`.
-/
theorem multFib_of (h2 : DensFibV) : MultFib := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μv hμv νv hνv fibV hfibV d b Φf Φv hp
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) Φf Φv
    continuous_const (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp
    (fun X => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
  obtain ⟨μinf, hμinf⟩ := h3.1
  obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
  obtain ⟨ginf, gv, _, hdv, hm, _⟩ := (((h3.2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv
  convert hm using 1
  funext v
  exact (h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)
    (fibV v) (hfibV v) (Φv v) (gv v) (hp.1 v) (hdv v)).symm

def LatSB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (d M n : ℕ)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)),
    IsSB ((latV (M := M) (n := n) b v).indicator (1 : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)`. Set `b` to `Module.finBasis F E`. Set `Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ` to `fun v => (latV b v).indicator 1`. Use `⟨fun μinf hμinf νinf hνinf fib1 fib2 hf1 hf2 Φinf hci hsi => ?_, ?_⟩` and prove the remaining obligations.

Establish `hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv` using `⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩`. Establish `hS` using `hc a ha2 (gramE σ J X0) hT hdet _ b (fun X => Φinf (projInf X) * (fun X => ∏ᶠ v, Lv v (projV v X)) (projFin X)) Φinf _ Lv hci (rapidDecay_of_compact b Φinf hci hsi) hp (fun X => rfl)`. Take `⟨μ, hμ⟩` from `hS.1`. Take `⟨𝓕, h𝓕⟩` from `(hS.2 μ hμ).1`. Establish `h3` using `(((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf)`.

Take `⟨μv, hμv⟩` from `h3.1`. Take `⟨νv, hνv⟩` from `(h3.2 μv hμv).1`. Take `⟨ginf, gv, hdi, _, _, _⟩` from `(h3.2 μv hμv).2 νv hνv`. Rewrite using `[← h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fib1 hf1 Φinf ginf hci hsi hdi, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fib2 hf2 Φinf ginf hci hsi hdi]`. Introduce `v0 μ0 hμ0 ν0 hν0 fib1 fib2 hf1 hf2 Φ0 hΦ0`.

Set `Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ` to `Function.update Lv v0 Φ0`. Establish `hp : IsPureFin b (fun X => ∏ᶠ v, Φv v (projV v X)) Φv`. Use `⟨fun v => ?_, ?_, fun X => rfl⟩` and prove the remaining obligations. Distinguish the cases in `hv : v = v0`. Substitute `hv` using the available equality.

Simplify using `only [Φv, Function.update_self]`. Conclude with `hΦ0`. Simplify using `only [Φv, Function.update_of_ne hv]`. Conclude with `hL F E _ M a b v`. Use `filter_upwards [(Set.finite_singleton v0).compl_mem_cofinite] with v hv`.

Simplify using `only [Φv, Function.update_of_ne (show v ≠ v0 from hv)]`. Both sides reduce to the same expression. Establish `hS` using `hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) (fun X => ∏ᶠ v, Φv v (projV v X)) Φv continuous_const (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)`. Take `⟨μ, hμ⟩` from `hS.1`. Take `⟨𝓕, h𝓕⟩` from `(hS.2 μ hμ).1`.

Establish `h3` using `((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ`. Take `⟨μinf, hμinf⟩` from `h3.1`. Take `⟨νinf, hνinf⟩` from `(h3.2 μinf hμinf).1`. Establish `h4` using `((h3.2 μinf hμinf).2 νinf hνinf)`. Take `⟨μv', hμv'⟩` from `h4.1`.

Set `μv` to `Function.update μv' v0 μ0`. Establish `hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)`. Introduce `v`. Distinguish the cases in `hv : v = v0`. Substitute `hv` using the available equality.

Simplify using `only [μv, Function.update_self]`. Conclude with `hμ0`. Simplify using `only [μv, Function.update_of_ne hv]`. Conclude with `hμv' v`. Take `⟨νv', hνv'⟩` from `(h4.2 μv hμv).1`.

Set `νv` to `Function.update νv' v0 ν0`. Establish `hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)`. Introduce `v`. Distinguish the cases in `hv : v = v0`. Substitute `hv` using the available equality.

Simplify using `only [νv, Function.update_self]`. Conclude with `hν0`. Simplify using `only [νv, Function.update_of_ne hv]`. Conclude with `hνv' v`. Take `⟨ginf, gv, _, hdv, _, _⟩` from `(h4.2 μv hμv).2 νv hνv`.

Establish `hd0` using `hdv v0`. Simplify using `only [μv, νv, Φv, Function.update_self] at hd0`. Rewrite using `[← h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib1 hf1 Φ0 (gv v0) hΦ0 hd0, h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib2 hf2 Φ0 (gv v0) hΦ0 hd0]`.
-/
theorem fibPin_of (h1 : DensFibInf) (h2 : DensFibV) (hL : LatSB) : FibPin := by
  classical
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  let Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (latV b v).indicator 1
  refine ⟨fun μinf hμinf νinf hνinf fib1 fib2 hf1 hf2 Φinf hci hsi => ?_, ?_⟩
  · have hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv :=
      ⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩
    have hS := hc a ha2 (gramE σ J X0) hT hdet _ b
      (fun X => Φinf (projInf X) * (fun X => ∏ᶠ v, Lv v (projV v X)) (projFin X)) Φinf _ Lv
      hci (rapidDecay_of_compact b Φinf hci hsi) hp (fun X => rfl)
    obtain ⟨μ, hμ⟩ := hS.1
    obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
    have h3 := (((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf)
    obtain ⟨μv, hμv⟩ := h3.1
    obtain ⟨νv, hνv⟩ := (h3.2 μv hμv).1
    obtain ⟨ginf, gv, hdi, _, _, _⟩ := (h3.2 μv hμv).2 νv hνv
    rw [← h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fib1 hf1
      Φinf ginf hci hsi hdi, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf
      hνinf fib2 hf2 Φinf ginf hci hsi hdi]
  · intro v0 μ0 hμ0 ν0 hν0 fib1 fib2 hf1 hf2 Φ0 hΦ0
    let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
      Function.update Lv v0 Φ0
    have hp : IsPureFin b (fun X => ∏ᶠ v, Φv v (projV v X)) Φv := by
      refine ⟨fun v => ?_, ?_, fun X => rfl⟩
      · by_cases hv : v = v0
        · subst hv; simp only [Φv, Function.update_self]; exact hΦ0
        · simp only [Φv, Function.update_of_ne hv]; exact hL F E _ M a b v
      · filter_upwards [(Set.finite_singleton v0).compl_mem_cofinite] with v hv
        simp only [Φv, Function.update_of_ne (show v ≠ v0 from hv)]
        rfl
    have hS := hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))
      (fun X => ∏ᶠ v, Φv v (projV v X)) Φv continuous_const
      (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)
    obtain ⟨μ, hμ⟩ := hS.1
    obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
    have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
    obtain ⟨μinf, hμinf⟩ := h3.1
    obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
    have h4 := ((h3.2 μinf hμinf).2 νinf hνinf)
    obtain ⟨μv', hμv'⟩ := h4.1
    let μv := Function.update μv' v0 μ0
    have hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v) := by
      intro v
      by_cases hv : v = v0
      · subst hv; simp only [μv, Function.update_self]; exact hμ0
      · simp only [μv, Function.update_of_ne hv]; exact hμv' v
    obtain ⟨νv', hνv'⟩ := (h4.2 μv hμv).1
    let νv := Function.update νv' v0 ν0
    have hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v) := by
      intro v
      by_cases hv : v = v0
      · subst hv; simp only [νv, Function.update_self]; exact hν0
      · simp only [νv, Function.update_of_ne hv]; exact hνv' v
    obtain ⟨ginf, gv, _, hdv, _, _⟩ := (h4.2 μv hμv).2 νv hνv
    have hd0 := hdv v0
    simp only [μv, νv, Φv, Function.update_self] at hd0
    rw [← h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib1 hf1 Φ0 (gv v0)
      hΦ0 hd0, h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib2 hf2 Φ0
      (gv v0) hΦ0 hd0]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)`. Set `b` to `Module.finBasis F E`. Set `Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ` to `fun v => (latV b v).indicator 1`. Establish `hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv` using `⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩`.

Establish `hS` using `hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) (fun X => ∏ᶠ v, Lv v (projV v X)) Lv continuous_const (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)`. Take `⟨μ, hμ⟩` from `hS.1`. Take `⟨𝓕, h𝓕⟩` from `(hS.2 μ hμ).1`. Establish `h3` using `((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ`. Take `⟨μinf, hμinf⟩` from `h3.1`.

Take `⟨νinf, hνinf⟩` from `(h3.2 μinf hμinf).1`. Establish `h4` using `((h3.2 μinf hμinf).2 νinf hνinf)`. Take `⟨μv, hμv⟩` from `h4.1`. Take `⟨νv, hνv⟩` from `(h4.2 μv hμv).1`. Take `⟨fibInf, hfi⟩` from `hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf`.

Use `choose fibV hfv using fun v => hV F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)`. Conclude with `⟨μinf, νinf, μv, νv, fibInf, fibV, hμinf, hνinf, hμv, hνv, hfi, hfv⟩`.
-/
theorem locEx_of (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) : LocEx := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  let Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (latV b v).indicator 1
  have hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv :=
    ⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩
  have hS := hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))
    (fun X => ∏ᶠ v, Lv v (projV v X)) Lv continuous_const
    (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
  obtain ⟨μinf, hμinf⟩ := h3.1
  obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
  have h4 := ((h3.2 μinf hμinf).2 νinf hνinf)
  obtain ⟨μv, hμv⟩ := h4.1
  obtain ⟨νv, hνv⟩ := (h4.2 μv hμv).1
  obtain ⟨fibInf, hfi⟩ := hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
  choose fibV hfv using fun v =>
    hV F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)
  exact ⟨μinf, νinf, μv, νv, fibInf, fibV, hμinf, hνinf, hμv, hνv, hfi, hfv⟩

/- English proof (translation)
The claim follows from `exOmT_of (locEx_of hI hV hL) hU (fibPin_of hDI hDV hL) (multFib_of hDV) hR`.
-/
theorem exOmT_of_steps (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) (hU : SdUniq)
    (hDI : DensFibInf) (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of (locEx_of hI hV hL) hU (fibPin_of hDI hDV hL) (multFib_of hDV) hR

end PI.VolStabW
