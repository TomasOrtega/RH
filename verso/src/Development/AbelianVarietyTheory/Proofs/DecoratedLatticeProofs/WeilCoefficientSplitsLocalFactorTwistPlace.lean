import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeightStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceTwistSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistCoef

/- English proof (translation)
Establish `hu : (u : ℂ) ≠ 0` using `u.ne_zero`. Rewrite using `[Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, h]`. Simplify using the standard rewrite rules.
-/
theorem conj_unit {u : ℂˣ} (h : ‖(u : ℂ)‖ = 1) : conj (u : ℂ) = ((u⁻¹ : ℂˣ) : ℂ) := by
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

/- English proof (translation)
Unfold `datum`. Use `split_ifs with h`. Establish `h1 : ‖(((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ)‖ = 1`. Simplify using `[Units.val_inv_eq_inv_val, norm_inv, hμ]`. Rewrite using `[conj_unit h1]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    datum μ⁻¹ z = conj (datum μ z) := by
  unfold datum
  split_ifs with h
  · have h1 : ‖(((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      simp [Units.val_inv_eq_inv_val, norm_inv, hμ]
    rw [conj_unit h1]
    simp
  · simp

/- English proof (translation)
Unfold `GlobalTheory.SplitWeil.om`. Rewrite using `[datum_inv_conj μ hμ]`. Simplify using `only [map_mul, Complex.conj_ofReal, conj_unit (hμ _), MonoidHom.inv_apply]`. Simplify using the standard rewrite rules.
-/
theorem om_datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (y : GL (A ⊕ D') k)
    (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    GlobalTheory.SplitWeil.om μ⁻¹ y (1 : GL (A ⊕ D) k) (datum μ⁻¹) z =
      conj (GlobalTheory.SplitWeil.om μ y (1 : GL (A ⊕ D) k) (datum μ) z) := by
  unfold GlobalTheory.SplitWeil.om
  rw [datum_inv_conj μ hμ]
  simp only [map_mul, Complex.conj_ofReal, conj_unit (hμ _), MonoidHom.inv_apply]
  simp

end Local

end GlobalTheory.TwistCoef

namespace GlobalTheory.TwistCoef

section IP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] {m n : Type} [Fintype m] [Fintype n]

/- English proof (translation)
Unfold `GlobalTheory.SplitWeil.ip`. Rewrite using `[← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using `[map_mul]`.
-/
theorem ip_conj (ν : Measure k) (F G : Matrix m n k → ℂ) :
    GlobalTheory.SplitWeil.ip ν (fun z => conj (F z)) (fun z => conj (G z)) = conj (GlobalTheory.SplitWeil.ip ν F G) := by
  unfold GlobalTheory.SplitWeil.ip
  rw [← integral_conj]
  congr 1
  funext z
  simp [map_mul]

end IP

/- English proof (translation)
Introduce `D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP v φ hφ ι hι μT hμT _ _ ν hν cf hcf P x hx`. Take `⟨-, hch'⟩` from `GlobalTheory.TwistChart.charts_at_twist D c w hw (k + 1) hk s' hs' PP hPP`. Take `⟨⟨e, he⟩, -, ⟨ι', hι'⟩, hμ⟩` from `hch' v φ hφ`. Take `⟨μS, -, hμS⟩` from `hμ (c.chS (k + 1))`. Take `⟨U, hU1, -⟩` from `GlobalTheory.TwistChart.unit_section φ he`.

Establish `hunit : ∀ d, ‖(μT d : ℂ)‖ = 1` using `fun d => by`. Rewrite using `[hμT (U d) d ⟨e, he, (hU1 d).1, (hU1 d).2⟩]`. Conclude with `Circle.norm_coe _`. Establish `hlift : LiftsChar φ PP μT (w.ξ PP)` using `(GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v φ hφ).2.2.2.1 k hk μT (Or.inr hμT)`. Take `⟨hW, hΦ, T, hT0, -, hTω, hC⟩` from `GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hgap c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT μT hμS hμT hlift P m X hX`.

Take `⟨C, hC⟩` from `hC ν hν x hx`. Establish `key : ∀ y, coefW p.ω m X (p.pt P) (x * ι y) = C * conj (cf y)`. Introduce `y`. Establish `h1 : p.ω (x * ι y, 1) = p.ω (x, 1) * p.ω (ι y, ι' 1)`. Rewrite using `[map_one, ← map_mul]`.

Simplify using the standard rewrite rules. Unfold `coefW`. Rewrite using `[h1, ← hT0]`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[hTω, hC, hcf, ← ip_conj]`.

Use `congr 2`. Use function extensionality and compare the values at `z`. Simplify using `[GlobalTheory.ParHecke.omTwo, om_datum_inv_conj _ hunit]`. Use function extensionality and compare the values at `z`. Conclude with `datum_inv_conj _ hunit z`.

Introduce `y`. Establish `h0` using `key 1`. Rewrite `h0` using `[map_one, mul_one]`. Rewrite using `[key y, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_split : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s k φ ι → ∀ μT : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ, (∀ g, cf g = GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fv D.host.F v)) (datum μT)) (datum μT)) → ∀ P (x : GA D s.V), gAt s.V (.inl v) x = 1 → ∀ y, coefW p.ω m X (p.pt P) (x * ι y) * conj (cf 1) = coefW p.ω m X (p.pt P) x * conj (cf y) := by
  intro D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP v φ hφ ι hι μT hμT _ _ ν hν cf hcf P x hx
  obtain ⟨-, hch'⟩ := GlobalTheory.TwistChart.charts_at_twist D c w hw (k + 1) hk s' hs' PP hPP
  obtain ⟨⟨e, he⟩, -, ⟨ι', hι'⟩, hμ⟩ := hch' v φ hφ
  obtain ⟨μS, -, hμS⟩ := hμ (c.chS (k + 1))
  obtain ⟨U, hU1, -⟩ := GlobalTheory.TwistChart.unit_section φ he
  have hunit : ∀ d, ‖(μT d : ℂ)‖ = 1 := fun d => by
    rw [hμT (U d) d ⟨e, he, (hU1 d).1, (hU1 d).2⟩]
    exact Circle.norm_coe _
  have hlift : LiftsChar φ PP μT (w.ξ PP) :=
    (GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v φ hφ).2.2.2.1 k hk μT (Or.inr hμT)
  obtain ⟨hW, hΦ, T, hT0, -, hTω, hC⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hgap c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT μT hμS hμT hlift P m X hX
  obtain ⟨C, hC⟩ := hC ν hν x hx
  have key : ∀ y, coefW p.ω m X (p.pt P) (x * ι y) = C * conj (cf y) := by
    intro y
    have h1 : p.ω (x * ι y, 1) = p.ω (x, 1) * p.ω (ι y, ι' 1) := by
      rw [map_one, ← map_mul]
      simp
    unfold coefW
    rw [h1, ← hT0]
    simp only [Module.End.mul_apply]
    rw [hTω, hC, hcf, ← ip_conj]
    congr 2
    · funext z
      simp [GlobalTheory.ParHecke.omTwo, om_datum_inv_conj _ hunit]
    · funext z
      exact datum_inv_conj _ hunit z
  intro y
  have h0 := key 1
  rw [map_one, mul_one] at h0
  rw [key y, h0]
  ring

end GlobalTheory.TwistCoef
