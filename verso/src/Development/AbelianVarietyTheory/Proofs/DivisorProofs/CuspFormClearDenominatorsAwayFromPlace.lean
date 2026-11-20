import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScal
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.Clear

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c`. Use `letI := H.starRing`. Introduce `r U G f m hm hmv la k hk`. Use `set ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := Function.update m la (k : ℝ) with hρ`. Establish `hsupp : (Function.support ρ).Finite`.

Use `(hm.insert la).subset ?_` and prove the remaining obligations. Introduce `w hw`. Distinguish the cases in `h : w = la`. Conclude with `Or.inl h`. Use `right`.

Simplify `hw` using `[hρ, Function.mem_support, Function.update_of_ne h]`. Take `⟨a, ha0, hala, hapos⟩` from `GlobalTheory.RefSum.ScalApprox.exists_scal c.F ρ hsupp la`. Establish `hρla : ρ la = (k : ℝ)` using `by simp [hρ]`. Establish `hvla : vAdd la a = -k`. Rewrite `hala` using `[hρla, Int.floor_intCast]`.

Conclude with `hala` after adjusting the coercions. Establish `hle : ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((ρ w : ℝ) : EReal) ≤ v (f : Rul Xo c)`. Introduce `w v hv`. Distinguish the cases in `h : w = la`. Substitute `h` using the available equality.

Rewrite using `[hρla]`. Conclude with `hk v hv`. Rewrite using `[show ρ w = m w by simp [hρ, Function.update_of_ne h]]; exact hmv w v hv`. Use `⟨a, ha0, hvla, ⟨a • f, (cuspW Xo c U G).smul_mem a f.2⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show _ ∈ GlobalTheory.AllWt.supLat _`.

Rewrite using `[GlobalTheory.AllWt.mem_supLat]`. Introduce `w v hv`. Use `show 0 ≤ v (a • (f : Rul Xo c))`. Rewrite using `[(isVal_valSet w v hv).smul a _ ha0]`. Establish `h1 : (0 : EReal) ≤ (((vAdd w a : ℤ) : ℝ) : EReal) + ((ρ w : ℝ) : EReal)`.

Rewrite using `[← EReal.coe_add]`. Conclude with `hapos w` after adjusting the coercions. Conclude with `h1.trans (add_le_add le_rfl (hle w v hv))`.
-/
theorem clear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ E) (f : cuspW Xo c U G) (m : HeightOneSpectrum (𝓞 c.F) → ℝ), (Function.support m).Finite → (∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℤ), (∀ v ∈ valSet Xo c (algCls Xo c) la, ((k : ℝ) : EReal) ≤ v f) → ∃ s : c.F, s ≠ 0 ∧ vLa la s = -k ∧ ∃ g ∈ latW U G, (g : Rul Xo c) = s • (f : Rul Xo c) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro r U G f m hm hmv la k hk
  classical
  set ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := Function.update m la (k : ℝ) with hρ
  have hsupp : (Function.support ρ).Finite := by
    refine (hm.insert la).subset ?_
    intro w hw
    by_cases h : w = la
    · exact Or.inl h
    · right
      simpa [hρ, Function.mem_support, Function.update_of_ne h] using hw
  obtain ⟨a, ha0, hala, hapos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F ρ hsupp la
  have hρla : ρ la = (k : ℝ) := by simp [hρ]
  have hvla : vAdd la a = -k := by
    rw [hρla, Int.floor_intCast] at hala
    exact_mod_cast hala
  have hle : ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((ρ w : ℝ) : EReal) ≤ v (f : Rul Xo c) := by
    intro w v hv
    by_cases h : w = la
    · subst h; rw [hρla]; exact hk v hv
    · rw [show ρ w = m w by simp [hρ, Function.update_of_ne h]]; exact hmv w v hv
  refine ⟨a, ha0, hvla, ⟨a • f, (cuspW Xo c U G).smul_mem a f.2⟩, ?_, rfl⟩
  show _ ∈ GlobalTheory.AllWt.supLat _
  rw [GlobalTheory.AllWt.mem_supLat]
  intro w v hv
  show 0 ≤ v (a • (f : Rul Xo c))
  rw [(isVal_valSet w v hv).smul a _ ha0]
  have h1 : (0 : EReal) ≤ (((vAdd w a : ℤ) : ℝ) : EReal) + ((ρ w : ℝ) : EReal) := by
    rw [← EReal.coe_add]; exact_mod_cast hapos w
  exact h1.trans (add_le_add le_rfl (hle w v hv))

end GlobalTheory.RefSum.Clear
